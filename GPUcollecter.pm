package PVE::API2::GPUMonitor;

use strict;
use warnings;
use JSON;
use POSIX qw(WNOHANG);
use Fcntl qw(:flock);
use Time::HiRes qw(time);
use Fcntl qw(:flock O_CREAT O_EXCL O_WRONLY);
use File::Path qw(remove_tree);

# debug configuration - set to 0 to disable all _debug output
my $debug_ENABLED = 1;
my $VERSION = '1.0.0';

# debug function showing line number and call chain
# Usage: _debug(__LINE__, "message")
sub _debug {
    return unless $debug_ENABLED;
    
    my ($line, $message) = @_;
    
    # Get function call chain
    my @caller1 = caller(1);  # who called _debug()
    my @caller2 = caller(2);  # parent of caller
    
    my $sub1 = $caller1[3] || 'main';
    my $sub2 = $caller2[3];
    
    $sub1 =~ s/.*:://;  # Remove package prefix
    
    if (defined $sub2) {
        $sub2 =~ s/.*:://;
        warn "[$sub2 -> $sub1:$line] $message\n";
    } else {
        # No parent caller (called from top level)
        warn "[$sub1:$line] $message\n";
    }
}

my $pve_mod_working_dir = '/run/pveproxy/pve-mod';
my $stats_dir = $pve_mod_working_dir;
my $state_file = "$pve_mod_working_dir/stats.json";
my $lock_file = "$pve_mod_working_dir/pve-mod-worker.lock";
my $pve_mod_worker_lock = "$pve_mod_working_dir/pve-mod-pve_mod_worker.lock";
my $startup_lock = $lock_file . ".startup";
my $last_snapshot = {};
my $last_mtime = 0;
my $is_collector_parent = 0;  # Flag to track if this process started collectors
my $last_get_graphic_stats_time = 0;  # Track when get_graphic_stats was last called
my $COLLECTOR_TIMEOUT = 10;   # Stop collectors x seconds after last get_graphic_stats call

my $intel_gpu_enabled = 1; # Set to 0 to disable Intel GPU support
my $amd_gpu_enabled   = 0; # Set to 1 to enable AMD GPU support (not yet implemented)
my $nvidia_gpu_enabled = 1; # Set to 1 to enable NVIDIA GPU support (not yet implemented)
my $pve_mod_worker_pid;
my $pve_mod_worker_running = 0;

# ============================================================================
# Intel GPU Support
# ============================================================================

# Parse Intel GPU line output format
sub _parse_intel_gpu_line {
    my ($line) = @_;
    
    # Expected format (with aligned columns):
    # Freq MHz      IRQ RC6     Power W             RCS             BCS             VCS            VECS
    # req  act       /s   %   gpu   pkg       %  se  wa       %  se  wa       %  se  wa       %  se  wa
    #   0    0        0   0  0.00  7.47    0.00   0   0    0.00   0   0    0.00   0   0    0.00   0   0
    
    # Remove leading/trailing whitespace
    $line =~ s/^\s+|\s+$//g;
    
    # Split by whitespace and filter empty values
    my @values = grep { $_ ne '' } split(/\s+/, $line);
    
    # Expected: req(0) act(1) irq(2) rc6(3) gpu(4) pkg(5) rcs%(6) rcs_se(7) rcs_wa(8) 
    #           bcs%(9) bcs_se(10) bcs_wa(11) vcs%(12) vcs_se(13) vcs_wa(14) vecs%(15) vecs_se(16) vecs_wa(17)
    
    return unless @values >= 18;
    
    my $stats = {
        frequency => {
            requested => $values[0] + 0.0,
            actual => $values[1] + 0.0,
            unit => "MHz"
        },
        interrupts => {
            count => $values[2] + 0.0,
            unit => "irq/s"
        },
        rc6 => {
            value => $values[3] + 0.0,
            unit => "%"
        },
        power => {
            GPU => $values[4] + 0.0,
            Package => $values[5] + 0.0,
            unit => "W"
        },
        engines => {
            "Render/3D" => {
                busy => $values[6] + 0.0,
                sema => $values[7] + 0.0,
                wait => $values[8] + 0.0,
                unit => "%"
            },
            Blitter => {
                busy => $values[9] + 0.0,
                sema => $values[10] + 0.0,
                wait => $values[11] + 0.0,
                unit => "%"
            },
            Video => {
                busy => $values[12] + 0.0,
                sema => $values[13] + 0.0,
                wait => $values[14] + 0.0,
                unit => "%"
            },
            VideoEnhance => {
                busy => $values[15] + 0.0,
                sema => $values[16] + 0.0,
                wait => $values[17] + 0.0,
                unit => "%"
            }
        },
        clients => {}
    };
    
    return $stats;
}

# Get list of Intel GPU devices
sub _get_intel_gpu_devices {
    my @devices = ();
    
    return @devices unless -x '/usr/bin/intel_gpu_top';
    
    _debug(__LINE__, "Getting Intel GPU devices");
    if (open my $fh, '-|', 'intel_gpu_top -L') {
        while (<$fh>) {
            chomp;
            # Parse: "card0  Intel Alderlake_n (Gen12)  pci:vendor=8086,device=46D0,card=0"
            # or: "card0  Intel Alderlake_n (Gen12)  pci:0000:00:02.0"
            if (/^(card\d+)\s+(.+?)\s+(pci:[^\s]+)/) {
                my $card = $1;
                my $name = $2;
                my $path = $3;
                push @devices, {
                    card => $card,
                    name => $name,
                    path => $path,
                    drm_path => "/dev/dri/$card"
                };
                _debug(__LINE__, "Found Intel device: $card -> $name ($path)");
            }
        }
        close $fh;
    } else {
        _debug(__LINE__, "Failed to run intel_gpu_top -L: $!");
    }
    
    return @devices;
}

sub _collector_for_intel_device {
    my ($device) = @_;
    $0 = "pve-mod-gpu-intel-collector: $device->{card}";

    my $drm_dev = "drm:/dev/dri/$device->{card}";
    my $intel_gpu_top_pid = undef;
    
    # Each device writes to its own file
    my $device_state_file = "$pve_mod_working_dir/stats-$device->{card}.json";
    
    _debug(__LINE__, "Collector started for device: $drm_dev, writing to $device_state_file");
    
    # Set up signal handlers for graceful shutdown
    my $shutdown = 0;
    $SIG{TERM} = sub {
        _debug(__LINE__, "Collector for $device->{card} received SIGTERM");
        $shutdown = 1;
        kill 'TERM', $intel_gpu_top_pid if defined $intel_gpu_top_pid && $intel_gpu_top_pid > 0;
    };
    $SIG{INT} = sub {
        _debug(__LINE__, "Collector for $device->{card} received SIGINT");
        $shutdown = 1;
        kill 'TERM', $intel_gpu_top_pid if defined $intel_gpu_top_pid && $intel_gpu_top_pid > 0;
    };
    
    # Run intel_gpu_top once and keep reading from it
    _debug(__LINE__, "About to open pipe to intel_gpu_top");
    $intel_gpu_top_pid = open(my $fh, '-|', "intel_gpu_top -d $drm_dev -s 1000 -l 2>&1");
    
    unless (defined $intel_gpu_top_pid && $intel_gpu_top_pid > 0) {
        _debug(__LINE__, "Failed to run intel_gpu_top for $drm_dev: $!");
        exit 1;
    }
    
    _debug(__LINE__, "Pipe opened successfully, PID=$intel_gpu_top_pid");
    
    my $line_count = 0;
    my $node_name = "node0";  # You may want to generate this based on device index
    
    while (my $line = <$fh>) {
        last if $shutdown;
        
        $line_count++;
        chomp $line;
        
        # Skip header lines
        next if $line =~ /MHz|IRQ|RC6|Power|RCS|BCS|VCS|VECS|req\s+act|^\s*$/;
        
        # Check if this is a data line
        if ($line =~ /^\s*[\d\s\.]+$/) {
            my $stats = _parse_intel_gpu_line($line);
            
            if ($stats) {
                # Build device-specific structure (just the node, not the full Graphics/Intel hierarchy)
                my $device_data = {
                    $node_name => {
                        name => $device->{name},
                        device_path => $device->{path},
                        drm_path => $device->{drm_path},
                        stats => $stats
                    }
                };
                
                # Write to device-specific file
                eval {
                    open my $ofh, '>', $device_state_file or die "Failed to open $device_state_file: $!";
                    print $ofh JSON->new->pretty->encode($device_data);
                    close $ofh;
                    _debug(__LINE__, "Wrote stats to $device_state_file (line #$line_count)");
                };
                if ($@) {
                    _debug(__LINE__, "Error writing stats: $@");
                }
            }
        }
    }
    
    close $fh;
    _debug(__LINE__, "Collector for $device->{card} shutting down");
    exit 0;
}

# ============================================================================
# AMD GPU Support (Placeholder)
# ============================================================================

sub _get_amd_gpu_devices {
    # TODO: Implement AMD GPU detection
    # Use rocminfo or similar tools to detect AMD GPUs
    _debug(__LINE__, "AMD GPU support not yet implemented");
    return ();
}

sub _parse_amd_gpu_line {
    my ($line) = @_;
    # TODO: Implement AMD GPU line parsing
    # Parse rocm-smi or similar output
    _debug(__LINE__, "AMD GPU line parsing not yet implemented");
    return undef;
}

sub _collector_for_amd_device {
    my ($device) = @_;
    # TODO: Implement AMD GPU collector
    _debug(__LINE__, "AMD GPU collector not yet implemented");
    exit 0;
}

# ============================================================================
# NVIDIA GPU Support (Placeholder)
# ============================================================================

sub get_nvidia_gpu_devices {
    my @devices = ();
    
    # Expected format (CSV with header):
    # index, name
    # 0, NVIDIA GeForce RTX 3080
    # 1, NVIDIA RTX A4000

    # add debug mode where Expected format is loaded from a file instead or calling nvidia-smi
    my $debug_file = '/tmp/nvidia-smi-debug.csv';
    my $use_debug_file = 1;  # Set to 1 to enable debug mode
    
    # todo - delete this block later
    if ($use_debug_file && -f $debug_file) {
        _debug(__LINE__, "Debug mode: reading NVIDIA GPU data from $debug_file");
        if (open my $fh, '<', $debug_file) {
            while (<$fh>) {
                chomp;
                # Skip empty lines
                next if /^\s*$/;
                
                # Parse CSV: "0, NVIDIA GeForce RTX 3080"
                if (/^\s*(\d+)\s*,\s*(.+?)\s*$/) {
                    my $index = $1;
                    my $name = $2;
                    push @devices, {
                        name => $name,
                        index => $index,
                    };
                    _debug(__LINE__, "Found NVIDIA GPU device (debug): $name -> (index: $index)");
                }
            }
            close $fh;
        } else {
            _debug(__LINE__, "Failed to open debug file $debug_file: $!");
        }
    }
    return @devices;


    # if (open my $fh, '-|', 'nvidia-smi --query-gpu=index,name --format=csv') {
    #     while (<$fh>) {
    #         chomp;
    #         # Skip empty lines
    #         next if /^\s*$/;
            
    #         # Parse CSV: "0, NVIDIA GeForce RTX 3080"
    #         if (/^\s*(\d+)\s*,\s*(.+?)\s*$/) {
    #             my $index = $1;
    #             my $name = $2;
    #             push @devices, {
    #                 name => $name,
    #                 index => $index,
    #             };
    #             _debug(__LINE__, "Found NVIDIA GPU device: $name -> (index: $index)");
    #         }
    #     }
    #     close $fh;
    # } else {
    #     _debug(__LINE__, "Failed to run nvidia-smi: $!");
    # }
    
    # return @devices;
}

sub parse_nvidia_gpu_line {
    my ($line) = @_;

    # Expected format (CSV) for multiple GPUs:
    # index, name, temperature.gpu, utilization.gpu, utilization.memory, memory.used, memory.total, power.draw, power.limit, fan.speed
    #0, NVIDIA GeForce RTX 3080, 62, 79, 44, 8260, 10240, 268.12, 320.00, 67

    # Remove leading/trailing whitespace
    $line =~ s/^\s+|\s+$//g;
    
    # Skip empty lines
    return unless $line;
    
    # Split by comma and trim whitespace from each field
    my @values = map { s/^\s+|\s+$//gr } split(/,/, $line);
    
    # Expected: index(0), name(1), temp(2), util_gpu(3), util_mem(4), mem_used(5), mem_total(6), power_draw(7), power_limit(8), fan_speed(9)
    return unless @values >= 10;
    
    my $stats = {
        index => $values[0] + 0,
        name => $values[1],
        temperature => {
            gpu => $values[2] + 0.0,
            unit => "°C"
        },
        utilization => {
            gpu => $values[3] + 0.0,
            memory => $values[4] + 0.0,
            unit => "%"
        },
        memory => {
            used => $values[5] + 0.0,
            total => $values[6] + 0.0,
            unit => "MiB"
        },
        power => {
            draw => $values[7] + 0.0,
            limit => $values[8] + 0.0,
            unit => "W"
        },
        fan => {
            speed => $values[9] + 0.0,
            unit => "%"
        }
    };
    
    return $stats;
}

sub collector_for_nvidia_device {
    my ($device) = @_;
    # nvidia-smi --query-gpu=index,name,temperature.gpu,utilization.gpu,utilization.memory,memory.used,memory.total,power.draw,power.limit,fan.speed --format=csv,nounits,noheader --loop=1
}

# ============================================================================
# Supporting functions
# ============================================================================

# Check if a process is alive
sub _is_process_alive {
    my ($pid) = @_;
    return -d "/proc/$pid";
}

sub _read_lock_pid {
    my ($lock_path) = @_;
    
    return undef unless open(my $fh, '<', $lock_path);
    
    my $pid = <$fh>;
    close($fh);
    chomp $pid if defined $pid;
    
    return $pid;
}

sub _acquire_exclusive_lock {
    my ($lock_path, $purpose) = @_;
    $purpose //= 'lock';
    
    my $fh;

    # Try to create lock file exclusively
    if (sysopen($fh, $lock_path, O_CREAT|O_EXCL|O_WRONLY, 0644)) {
        _debug(__LINE__, "Acquired $purpose on first try");
        return $fh;
    }
    
    # Lock file creation failed - check if it's stale or held by another process
    _debug(__LINE__, ucfirst($purpose) . " exists, checking if stale");
    
    my $lock_pid = _read_lock_pid($lock_path);
    
    if (!defined $lock_pid) {
        _debug(__LINE__, "Could not read $purpose file: $!");
        return undef;
    }
    
    if ($lock_pid eq '' || $lock_pid !~ /^\d+$/) {
        _debug(__LINE__, "Invalid PID in $purpose: '" . ($lock_pid // 'undefined') . "', removing");
        unlink($lock_path);
    } elsif (_is_process_alive($lock_pid)) {
        _debug(__LINE__, ucfirst($purpose) . " holder PID $lock_pid is still alive");
        return undef;
    } else {
        _debug(__LINE__, ucfirst($purpose) . " holder PID $lock_pid is dead, removing stale lock");
        unlink($lock_path);
    }
    
    # Try to acquire lock again after cleanup
    unless (sysopen($fh, $lock_path, O_CREAT|O_EXCL|O_WRONLY, 0644)) {
        _debug(__LINE__, "Failed to acquire $purpose on retry: $!");
        return undef;
    }
    
    _debug(__LINE__, "Acquired $purpose after removing stale lock");
    return $fh;
}

sub _is_lock_stale {
    my ($lock_path) = @_;
    
    return 0 unless open(my $fh, '<', $lock_path);
    
    my $lock_pid = <$fh>;
    chomp $lock_pid if defined $lock_pid;
    close($fh);
    
    # Invalid or missing PID
    return 1 unless defined $lock_pid && $lock_pid =~ /^\d+$/;
    
    # Valid PID but process is dead
    return !_is_process_alive($lock_pid);
}

sub _ensure_pve_mod_directory_exists {
    unless (-d $pve_mod_working_dir) {
        _debug(__LINE__, "Creating directory $pve_mod_working_dir");
        unless (mkdir($pve_mod_working_dir, 0755)) {
            _debug(__LINE__, "Failed to create $pve_mod_working_dir: $!. PVE Mod cannot start.");
            die "Failed to create $pve_mod_working_dir: $!";
        }
        _debug(__LINE__, "Directory $pve_mod_working_dir created");
    } else {
        _debug(__LINE__, "Directory $pve_mod_working_dir already exists");
    }
}

sub _pve_mod_hello {
    _debug(__LINE__, "PVE Mod is being started. Version $VERSION");
}

# ============================================================================
# API calls
# ============================================================================

sub get_graphic_stats {
    #  todo name the process without overruling other processes
    _debug(__LINE__, "get_graphic_stats called");
    _pve_mod_hello();
    
    # Start PVE Mod
    _pve_mod_starter();
    
    # Find all device-specific stat files
    my $dh;
    unless (opendir($dh, $stats_dir)) {
        _debug(__LINE__, "Failed to open stats directory: $stats_dir: $!");
        return $last_snapshot;
    }
    
    my @stat_files = grep { /^stats-card\d+\.json$/ } readdir($dh);
    closedir($dh);
    
    unless (@stat_files) {
        _debug(__LINE__, "No device stat files found in $stats_dir");
        return $last_snapshot;
    }
    
    _debug(__LINE__, "Found " . scalar(@stat_files) . " device stat file(s): " . join(', ', @stat_files));
    
    # Check if any files have been modified
    my $newest_mtime = 0;
    my $files_changed = 0;
    
    foreach my $file (@stat_files) {
        my $filepath = "$stats_dir/$file";
        my @stat = stat($filepath);
        if (@stat && $stat[9] > $newest_mtime) {
            $newest_mtime = $stat[9];
        }
    }
    
    if ($newest_mtime == $last_mtime) {
        _debug(__LINE__, "No device files modified, returning cached snapshot");
        return $last_snapshot;
    }
    
    _debug(__LINE__, "Device files modified ($last_mtime -> $newest_mtime), reading and merging files");
    
    # Merge all device files
    my $merged = {
        Graphics => {
            Intel => {}
        }
    };
    
    foreach my $file (@stat_files) {
        my $filepath = "$stats_dir/$file";
        
        _debug(__LINE__, "Reading device file: $filepath");
        
        eval {
            my $fh;
            unless (open($fh, '<', $filepath)) {
                _debug(__LINE__, "Failed to open $filepath: $!");
                return;
            }
            
            local $/;
            my $json = <$fh>;
            close($fh);
            
            _debug(__LINE__, "Read $file, JSON length: " . length($json) . " bytes");
            
            my $device_data = decode_json($json);
            
            # Merge this device's data into the main structure
            foreach my $node_name (keys %$device_data) {
                $merged->{Graphics}->{Intel}->{$node_name} = $device_data->{$node_name};
                _debug(__LINE__, "Merged node '$node_name' from $file");
            }
        };
        if ($@) {
            _debug(__LINE__, "Failed to read/parse $filepath: $@");
        }
    }
    
    # Update cache
    $last_snapshot = $merged;
    $last_mtime = $newest_mtime;
    $last_get_graphic_stats_time = time();
    
    _debug(__LINE__, "Successfully merged " . scalar(keys %{$merged->{Graphics}->{Intel}}) . " device node(s)");
    
    # Notify pve_mod_worker of activity
    _notify_pve_mod_worker();

    return $last_snapshot;
}

# ============================================================================
# Main Collector
# ============================================================================

sub _start_graphics_collectors {

    if ($intel_gpu_enabled == 0 && $amd_gpu_enabled == 0 && $nvidia_gpu_enabled == 0) {
        _debug(__LINE__, "No GPU types enabled, skipping collector startup");
        return;
    }
    else {
        _debug(__LINE__, "Starting graphics collectors");
    }

    # NOW check if collectors are already running (while holding startup lock)
    my %existing_collectors;
    if (-f $lock_file) {
        _debug(__LINE__, "Lock file exists: $lock_file");
        if (open(my $lock_fh, '<', $lock_file)) {
            _debug(__LINE__, "Opened lock file for reading");
            flock($lock_fh, LOCK_EX) or _debug(__LINE__, "Failed to lock $lock_file: $!");
            while (my $line = <$lock_fh>) {
                chomp $line;
                if ($line =~ /^(\d+)\s+(\S+)/) {
                    $existing_collectors{$2} = $1;
                } elsif ($line =~ /^(\d+)$/) {
                    # Backward compatibility: only PID, no card
                    $existing_collectors{"unknown"} = $1;
                }
            }
            close($lock_fh);
        } else {
            _debug(__LINE__, "Failed to open lock file: $!");
        }
    } else {
        _debug(__LINE__, "Lock file does not exist. Clean start");
    }
    
    # Generalized device collector management for future AMD/NVIDIA support
    my @all_devices;
    my @all_types;
    my @all_collectors;

    # Intel
    if ($intel_gpu_enabled) {
        _debug(__LINE__, "Intel GPU support enabled");
        _debug(__LINE__, "Checking for intel_gpu_top");
        unless (-x '/usr/bin/intel_gpu_top') {
            _debug(__LINE__, "intel_gpu_top not executable");
            return;
        }
        _debug(__LINE__, "intel_gpu_top is executable");
        
        my @intel_devices = _get_intel_gpu_devices();
        unless (@intel_devices) {
            _debug(__LINE__, "No Intel GPU devices found");
            return;
        }
        _debug(__LINE__, "Found " . scalar(@intel_devices) . " Intel GPU device(s)");
        foreach my $device (@intel_devices) {
            push @all_devices, $device;
            push @all_types, 'intel';
        }
    }
    # AMD (future)
    if ($amd_gpu_enabled) {
        my @amd_devices = _get_amd_gpu_devices();
        _debug(__LINE__, "Got " . scalar(@amd_devices) . " AMD devices");
        foreach my $device (@amd_devices) {
            push @all_devices, $device;
            push @all_types, 'amd';
        }
    }
    # NVIDIA (future)
    if ($nvidia_gpu_enabled) {
        _debug(__LINE__, "NVIDIA GPU support enabled");

        # _debug(__LINE__, "Checking for nvidia-smi");
        # unless (-x '/usr/bin/nvidia-smi') {
        #     _debug(__LINE__, "nvidia-smi not executable");
        #     return;
        # }
        _debug(__LINE__, "nvidia-smi is executable");

        my @nvidia_devices = get_nvidia_gpu_devices();
        _debug(__LINE__, "Got " . scalar(@nvidia_devices) . " NVIDIA devices");
        foreach my $device (@nvidia_devices) {
            push @all_devices, $device;
            push @all_types, 'nvidia';
        }
    }

    my @child_pids;
    my @child_devices;
    my @child_types;
    for (my $i = 0; $i < @all_devices; $i++) {
        my $device = $all_devices[$i];
        my $type = $all_types[$i];
        my $card = $device->{card};
        my $existing_pid = $existing_collectors{$card};
        if ($existing_pid && _is_process_alive($existing_pid)) {
            _debug(__LINE__, "Collector for $type $card already running with PID $existing_pid");
            push @child_pids, $existing_pid;
            push @child_devices, $device;
            push @child_types, $type;
            next;
        }
        _debug(__LINE__, "About to fork collector for $type $card");
        my $pid = fork();
        unless (defined $pid) {
            _debug(__LINE__, "fork failed: $!");
            unlink($startup_lock);
            die "fork failed: $!";
        }
        if ($pid == 0) {
            # Child process
            _debug(__LINE__, "In child process for $type $card");
            if ($type eq 'intel') {
                _collector_for_intel_device($device);
            } elsif ($type eq 'amd') {
                _collector_for_amd_device($device);
            } elsif ($type eq 'nvidia') {
                collector_for_nvidia_device($device);
            } else {
                _debug(__LINE__, "Unknown GPU type $type for $card");
                exit(1);
            }
            # Should not reach here
            exit(0);
        } else {
            _debug(__LINE__, "Forked child PID $pid for $type $card");
            push @child_pids, $pid;
            push @child_devices, $device;
            push @child_types, $type;
        }
    }
    _debug(__LINE__, "Active children: " . join(", ", @child_pids));

    # Write child PIDs and device cards/types to lock file
    if (open(my $lock_fh, '>', $lock_file)) {
        _debug(__LINE__, "Opened lock file for writing");
        for (my $i = 0; $i < @child_pids; $i++) {
            my $pid = $child_pids[$i];
            my $device = $child_devices[$i];
            my $type = $child_types[$i];
            my $card = $device->{card} // '';
            print $lock_fh "$pid $card $type\n";
        }
        flock($lock_fh, LOCK_UN);
        close($lock_fh);
        _debug(__LINE__, "Wrote " . scalar(@child_pids) . " collector PID(s) to lock file");
    } else {
        _debug(__LINE__, "Failed to open lock file for writing: $!");
        foreach my $pid (@child_pids) {
            _debug(__LINE__, "Killing child $pid due to lock file write failure");
            kill 'TERM', $pid;
        }
        unlink($startup_lock);
        return;
    }
    
    # Wait briefly to ensure collector is actually running
    sleep 0.1;

    # Verify at least one child is still alive (by PID only)
    my $any_alive = 0;
    for (my $i = 0; $i < @child_pids; $i++) {
        my $pid = $child_pids[$i];
        my $device = $child_devices[$i];
        my $card = $device->{card} // '';
        my $alive = kill(0, $pid);
        if ($alive) {
            $any_alive = 1;
            _debug(__LINE__, "Verified child PID $pid for $card is alive");
        } else {
            _debug(__LINE__, "WARNING - Child PID $pid for $card died immediately!");
        }
    }
    unless ($any_alive) {
        _debug(__LINE__, "ERROR - No children alive after fork!");
    }

    _debug(__LINE__, "Graphics collectors started");
}

# ============================================================================
# PVE Mod Worker
# ============================================================================
sub _pve_mod_starter {
    # Check if pve_mod_worker is already running - if so, entire system is already up
    _debug(__LINE__, "Checking if pve_mod_worker is already running");
    if (_is_pve_mod_worker_running()) {
        _debug(__LINE__, "pve_mod_worker process already running, system is already started");
        return "pve_mod_worker process already running, system is already started";
    }
    _debug(__LINE__, "PVE mod worker is not running. PVE Mod will be started.");

    # Ensure directory exists
    _ensure_pve_mod_directory_exists();

    # Try to acquire startup lock FIRST (prevents race conditions)
    _debug(__LINE__, "Trying to acquire startup lock: $startup_lock");
    my $startup_fh = _acquire_exclusive_lock($startup_lock, 'startup lock');
    return unless $startup_fh;
    print $startup_fh "$$\n";
    close($startup_fh);
    _debug(__LINE__, "Wrote PID, $$, to startup lock");
    
    

    # Start graphics collectors
    _start_graphics_collectors();

    # Start sensor collector
    # TBD

    # Start UPS collector
    # TBD

    _debug(__LINE__, "All collectors started");

    # Start pve mod workers
    _pve_mod_worker();

    # Remove startup lock LAST
    unlink($startup_lock);
    _debug(__LINE__, "Released startup lock");
    
    _debug(__LINE__, "pve_mod_worker started successfully, returning");
}

# ============================================================================
# PVE Mod Worker
# ============================================================================

sub _pve_mod_worker {
    _debug(__LINE__, "_pve_mod_worker called");
    
    # Check if worker is already running
    my $pve_mod_worker_fh = _acquire_exclusive_lock($pve_mod_worker_lock, 'pve_mod_worker lock');
    return unless $pve_mod_worker_fh;
    print $pve_mod_worker_fh "$$\n";
    close($pve_mod_worker_fh);
    
    _debug(__LINE__, "Forking new pve_mod_worker process");
    my $pve_mod_worker_pid = fork();
    
    unless (defined $pve_mod_worker_pid) {
        _debug(__LINE__, "Failed to fork pve_mod_worker process: $!");
        return;
    }
    
    if ($pve_mod_worker_pid == 0) {
        # Child process - run the pve_mod_worker
        _debug(__LINE__, "Child process forked, calling _pve_mod_keep_alive");
        _pve_mod_keep_alive();
        exit(0);  # Should never reach here
    } else {
        # Parent process - write PID to lock file
        _debug(__LINE__, "Forked pve_mod_worker process with PID $pve_mod_worker_pid");
        
        if (open my $fh, '>', $pve_mod_worker_lock) {
            print $fh "$pve_mod_worker_pid\n";
            close $fh;
            _debug(__LINE__, "Wrote pve_mod_worker PID to lock file: $pve_mod_worker_lock");
        } else {
            _debug(__LINE__, "Failed to write pve_mod_worker lock file: $!");
            kill('TERM', $pve_mod_worker_pid);
        }
    }
    _debug(__LINE__, "pve_mod_worker process started successfully");
}

sub _notify_pve_mod_worker {
    _debug(__LINE__, "_notify_pve_mod_worker called");
    unless (-f $pve_mod_worker_lock) {
        _debug(__LINE__, "pve_mod_worker lock file does not exist");
        return;
    }

    _debug(__LINE__, "pve_mod_worker lock file exists, reading PID");
    if (open my $fh, '<', $pve_mod_worker_lock) {
        my $pid = <$fh>;
        close $fh;
        chomp $pid if defined $pid;
        if (defined $pid && $pid =~ /^(\d+)$/) {
            # Untaint by capturing in regex - $1 is now untainted
            my $clean_pid = $1;
            
            if (_is_process_alive($clean_pid)) {
                _debug(__LINE__, "Sending USR1 signal to pve_mod_worker PID $clean_pid");
                my $result = kill('USR1', $clean_pid);
                _debug(__LINE__, "Signal result: $result");
            } else {
                _debug(__LINE__, "pve_mod_worker process $clean_pid is not alive, removing stale lock");
                unlink($pve_mod_worker_lock);
            }
        } else {
            # Stale lock, remove it
            _debug(__LINE__, "pve_mod_worker lock is stale (PID: " . ($pid // 'undefined') . "), removing");
            unlink($pve_mod_worker_lock);
        }
    } else {
        _debug(__LINE__, "Failed to open pve_mod_worker lock file: $!");
    }
}

sub _pve_mod_keep_alive {
    _debug(__LINE__, "pve_mod_worker process started with PID $$");
    
    my $last_activity = time();
    
    # Set up signal handlers
    $SIG{USR1} = sub {
        $last_activity = time();
        _debug(__LINE__, "Activity ping received");
    };
    $SIG{TERM} = sub {
        _debug(__LINE__, "pve_mod_worker received SIGTERM, shutting down");
        unlink($pve_mod_worker_lock) if -f $pve_mod_worker_lock;
        exit(0);
    };
    $SIG{INT} = sub {
        _debug(__LINE__, "pve_mod_worker received SIGINT, shutting down");
        unlink($pve_mod_worker_lock) if -f $pve_mod_worker_lock;
        exit(0);
    };
    
    _debug(__LINE__, "Entering pve_mod_worker loop, timeout=${COLLECTOR_TIMEOUT}s");
    
    while (1) {
        _debug(__LINE__, "pve_mod_worker loop start: checking activity");
        
        my $idle_time = time() - $last_activity;
        
        _debug(__LINE__, "pve_mod_worker loop: idle_time=${idle_time}s, timeout=${COLLECTOR_TIMEOUT}s");
        
        if ($idle_time > $COLLECTOR_TIMEOUT) {
            _debug(__LINE__, "Timeout reached, stopping collectors");
            _stop_collectors();
            _debug(__LINE__, "Collectors stopped, exiting pve_mod_worker");
            unlink($pve_mod_worker_lock) if -f $pve_mod_worker_lock;
            exit(0);
        }
        sleep(1);
    }
    
    # Should never reach here
    _debug(__LINE__, "pve_mod_worker loop exited unexpectedly!");
}

sub _is_pve_mod_worker_running {
    return -f $pve_mod_worker_lock;
}

# ============================================================================
# Other
# ============================================================================

sub _stop_collectors {
    _debug(__LINE__, "Stopping all collectors");
    
    # Read current PIDs from lock file
    my @pids;
    if (open my $lock_fh, '<', $lock_file) {
        while (my $line = <$lock_fh>) {
            chomp $line;
            # Extract PID from "PID card type" format
            if ($line =~ /^(\d+)/) {
                push @pids, $1;
            }
        }
        close($lock_fh);
    }
    _debug(__LINE__, "Cleanup complete_1");

    if (@pids) {
        _debug(__LINE__, "Sending SIGTERM to " . scalar(@pids) . " collector process(es)");
        foreach my $pid (@pids) {
            kill('TERM', $pid) if kill(0, $pid);
        }
        
        _debug(__LINE__, "Cleanup complete_2");

        # Wait up to 5 seconds for graceful shutdown
        my $timeout = 5;
        my $start = time();
        while (time() - $start < $timeout) {
            my $any_alive = 0;
            foreach my $pid (@pids) {
                if (kill(0, $pid)) {
                    $any_alive = 1;
                    last;
                }
            }
            last unless $any_alive;
            select(undef, undef, undef, 0.1);
        }
        _debug(__LINE__, "Cleanup complete_3");
        # Force kill any survivors
        foreach my $pid (@pids) {
            if (kill(0, $pid)) {
                _debug(__LINE__, "Force killing collector process $pid");
                kill('KILL', $pid);
            }
        }
        _debug(__LINE__, "Cleanup complete_4");
    }
    
    if (-f $state_file) {
        unlink $state_file or _debug(__LINE__, "Failed to remove $state_file: $!");
    }
    if (-f $lock_file) {
        unlink $lock_file or _debug(__LINE__, "Failed to remove $lock_file: $!");
    }
    
    # Remove pve mod worker directory and all files if it exists
    if (-d $pve_mod_working_dir) {
        remove_tree($pve_mod_working_dir, { error => \my $err });
        _debug(__LINE__, "Cleanup errors: @$err") if @$err;
    }

    _debug(__LINE__, "Cleanup complete_5");
}

END { _stop_collectors() }

1;
