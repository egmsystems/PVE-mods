package PVE::API2::GPUMonitor;

use strict;
use warnings;
use JSON;
use POSIX qw(WNOHANG);
use Fcntl qw(:flock);
use Time::HiRes qw(time);
use Fcntl qw(:flock O_CREAT O_EXCL O_WRONLY);

# Debug configuration - set to 0 to disable all debug output
my $DEBUG_ENABLED = 1;

# Debug function showing line number and call chain
# Usage: debug(__LINE__, "message")
sub debug {
    return unless $DEBUG_ENABLED;
    
    my ($line, $message) = @_;
    
    # Get function call chain
    my @caller1 = caller(1);  # who called debug()
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

my $stats_dir = '/var/run/pve-gpu';
my $state_file = '/var/run/pve-gpu/stats.json';
my $lock_file = '/var/run/pve-gpu/pve-gpu-collector.lock';
my $startup_lock = $lock_file . ".startup";
my $last_snapshot = {};
my $last_mtime = 0;
my $is_collector_parent = 0;  # Flag to track if this process started collectors
my $last_get_graphic_stats_time = 0;  # Track when get_graphic_stats was last called
my $COLLECTOR_TIMEOUT = 0;   # Stop collectors x seconds after last get_graphic_stats call

my $intel_gpu_enabled = 1; # Set to 0 to disable Intel GPU support
my $amd_gpu_enabled   = 0; # Set to 1 to enable AMD GPU support (not yet implemented)
my $nvidia_gpu_enabled = 0; # Set to 1 to enable NVIDIA GPU support (not yet implemented)
my $monitor_pid;
my $monitor_running = 0;

# ============================================================================
# Intel GPU Support
# ============================================================================

# Parse Intel GPU line output format
sub parse_intel_gpu_line {
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
sub get_intel_gpu_devices {
    my @devices = ();
    
    return @devices unless -x '/usr/bin/intel_gpu_top';
    
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
                debug(__LINE__, "Found GPU device: $card -> $name ($path)");
            }
        }
        close $fh;
    } else {
        debug(__LINE__, "Failed to run intel_gpu_top -L: $!");
    }
    
    return @devices;
}

sub collector_for_intel_device {
    my ($device) = @_;
    $0 = "pve-mod-gpu-intel-collector: $device->{card}";

    my $drm_dev = "drm:/dev/dri/$device->{card}";
    my $intel_gpu_top_pid = undef;
    
    # Each device writes to its own file
    my $device_state_file = "/var/run/pve-gpu/stats-$device->{card}.json";
    
    debug(__LINE__, "Collector started for device: $drm_dev, writing to $device_state_file");
    
    # Set up signal handlers for graceful shutdown
    my $shutdown = 0;
    $SIG{TERM} = sub {
        debug(__LINE__, "Collector for $device->{card} received SIGTERM");
        $shutdown = 1;
        kill 'TERM', $intel_gpu_top_pid if defined $intel_gpu_top_pid && $intel_gpu_top_pid > 0;
    };
    $SIG{INT} = sub {
        debug(__LINE__, "Collector for $device->{card} received SIGINT");
        $shutdown = 1;
        kill 'TERM', $intel_gpu_top_pid if defined $intel_gpu_top_pid && $intel_gpu_top_pid > 0;
    };
    
    # Run intel_gpu_top once and keep reading from it
    debug(__LINE__, "About to open pipe to intel_gpu_top");
    $intel_gpu_top_pid = open(my $fh, '-|', "intel_gpu_top -d $drm_dev -s 1000 -l 2>&1");
    
    unless (defined $intel_gpu_top_pid && $intel_gpu_top_pid > 0) {
        debug(__LINE__, "Failed to run intel_gpu_top for $drm_dev: $!");
        exit 1;
    }
    
    debug(__LINE__, "Pipe opened successfully, PID=$intel_gpu_top_pid");
    
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
            my $stats = parse_intel_gpu_line($line);
            
            if ($stats) {
                # Build device-specific structure (just the node, not the full Graphics/Intel hierarchy)
                my $device_data = {
                    $node_name => {
                        gpu_name => $device->{name},
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
                    debug(__LINE__, "Wrote stats to $device_state_file (line #$line_count)");
                };
                if ($@) {
                    debug(__LINE__, "Error writing stats: $@");
                }
            }
        }
    }
    
    close $fh;
    debug(__LINE__, "Collector for $device->{card} shutting down");
    exit 0;
}

# ============================================================================
# AMD GPU Support (Placeholder)
# ============================================================================

sub get_amd_gpu_devices {
    # TODO: Implement AMD GPU detection
    # Use rocminfo or similar tools to detect AMD GPUs
    debug(__LINE__, "AMD GPU support not yet implemented");
    return ();
}

sub parse_amd_gpu_line {
    my ($line) = @_;
    # TODO: Implement AMD GPU line parsing
    # Parse rocm-smi or similar output
    debug(__LINE__, "AMD GPU line parsing not yet implemented");
    return undef;
}

sub collector_for_amd_device {
    my ($device) = @_;
    # TODO: Implement AMD GPU collector
    debug(__LINE__, "AMD GPU collector not yet implemented");
    exit 0;
}

# ============================================================================
# NVIDIA GPU Support (Placeholder)
# ============================================================================

sub get_nvidia_gpu_devices {
    # TODO: Implement NVIDIA GPU detection
    # Use nvidia-smi to detect NVIDIA GPUs
    debug(__LINE__, "NVIDIA GPU support not yet implemented");
    return ();
}

sub parse_nvidia_gpu_line {
    my ($line) = @_;
    # TODO: Implement NVIDIA GPU line parsing
    # Parse nvidia-smi output
    debug(__LINE__, "NVIDIA GPU line parsing not yet implemented");
    return undef;
}

sub collector_for_nvidia_device {
    my ($device) = @_;
    # TODO: Implement NVIDIA GPU collector
    debug(__LINE__, "NVIDIA GPU collector not yet implemented");
    exit 0;
}

# ============================================================================
# Supporting functions
# ============================================================================

# Check if a process is alive
sub is_process_alive {
    my ($pid) = @_;
    return -d "/proc/$pid";
}

# ============================================================================
# Main Collector
# ============================================================================

sub start_graphics_collectors {

    if ($intel_gpu_enabled == 0 && $amd_gpu_enabled == 0 && $nvidia_gpu_enabled == 0) {
        debug(__LINE__, "No GPU types enabled, skipping collector startup");
        return;
    }

    # NOW check if collectors are already running (while holding startup lock)
    my %existing_collectors;
    if (-f $lock_file) {
        debug(__LINE__, "Lock file exists: $lock_file");
        if (open(my $lock_fh, '<', $lock_file)) {
            debug(__LINE__, "Opened lock file for reading");
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
            debug(__LINE__, "Failed to open lock file: $!");
        }
    } else {
        debug(__LINE__, "Lock file does not exist. Clean start");
    }
    
    # Generalized device collector management for future AMD/NVIDIA support
    my @all_devices;
    my @all_types;
    my @all_collectors;

    # Intel
    if ($intel_gpu_enabled) {
        debug(__LINE__, "Checking for intel_gpu_top");
        unless (-x '/usr/bin/intel_gpu_top') {
            debug(__LINE__, "intel_gpu_top not executable");
            unlink($startup_lock);
            return;
        }
        debug(__LINE__, "intel_gpu_top is executable");
        debug(__LINE__, "Getting Intel GPU devices");
        my @intel_devices = get_intel_gpu_devices();
        unless (@intel_devices) {
            debug(__LINE__, "No Intel GPU devices found");
            unlink($startup_lock);
            return;
        }
        debug(__LINE__, "Found " . scalar(@intel_devices) . " Intel GPU device(s)");
        foreach my $device (@intel_devices) {
            push @all_devices, $device;
            push @all_types, 'intel';
        }
    }
    # AMD (future)
    if ($amd_gpu_enabled) {
        my @amd_devices = get_amd_gpu_devices();
        debug(__LINE__, "Got " . scalar(@amd_devices) . " AMD devices");
        foreach my $device (@amd_devices) {
            push @all_devices, $device;
            push @all_types, 'amd';
        }
    }
    # NVIDIA (future)
    if ($nvidia_gpu_enabled) {
        my @nvidia_devices = get_nvidia_gpu_devices();
        debug(__LINE__, "Got " . scalar(@nvidia_devices) . " NVIDIA devices");
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
        if ($existing_pid && is_process_alive($existing_pid)) {
            debug(__LINE__, "Collector for $type $card already running with PID $existing_pid");
            push @child_pids, $existing_pid;
            push @child_devices, $device;
            push @child_types, $type;
            next;
        }
        debug(__LINE__, "About to fork collector for $type $card");
        my $pid = fork();
        unless (defined $pid) {
            debug(__LINE__, "fork failed: $!");
            unlink($startup_lock);
            die "fork failed: $!";
        }
        if ($pid == 0) {
            # Child process
            debug(__LINE__, "In child process for $type $card");
            if ($type eq 'intel') {
                collector_for_intel_device($device);
            } elsif ($type eq 'amd') {
                collector_for_amd_device($device);
            } elsif ($type eq 'nvidia') {
                collector_for_nvidia_device($device);
            } else {
                debug(__LINE__, "Unknown GPU type $type for $card");
                exit(1);
            }
            # Should not reach here
            exit(0);
        } else {
            debug(__LINE__, "Forked child PID $pid for $type $card");
            push @child_pids, $pid;
            push @child_devices, $device;
            push @child_types, $type;
        }
    }
    debug(__LINE__, "Active children: " . join(", ", @child_pids));

    # Write child PIDs and device cards/types to lock file
    if (open(my $lock_fh, '>', $lock_file)) {
        debug(__LINE__, "Opened lock file for writing");
        for (my $i = 0; $i < @child_pids; $i++) {
            my $pid = $child_pids[$i];
            my $device = $child_devices[$i];
            my $type = $child_types[$i];
            my $card = $device->{card} // '';
            print $lock_fh "$pid $card $type\n";
        }
        close($lock_fh);
        debug(__LINE__, "Wrote " . scalar(@child_pids) . " collector PID(s) to lock file");
    } else {
        debug(__LINE__, "Failed to open lock file for writing: $!");
        foreach my $pid (@child_pids) {
            debug(__LINE__, "Killing child $pid due to lock file write failure");
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
            debug(__LINE__, "Verified child PID $pid for $card is alive");
        } else {
            debug(__LINE__, "WARNING - Child PID $pid for $card died immediately!");
        }
    }
    unless ($any_alive) {
        debug(__LINE__, "ERROR - No children alive after fork!");
    }
}

sub get_graphic_stats {
    debug(__LINE__, "get_graphic_stats called");
    
    # Start PVE Mod worker, if not already running
    pve_mod_worker();
    
    # Find all device-specific stat files
    my $dh;
    unless (opendir($dh, $stats_dir)) {
        debug(__LINE__, "Failed to open stats directory: $stats_dir: $!");
        return $last_snapshot;
    }
    
    my @stat_files = grep { /^stats-card\d+\.json$/ } readdir($dh);
    closedir($dh);
    
    unless (@stat_files) {
        debug(__LINE__, "No device stat files found in $stats_dir");
        return $last_snapshot;
    }
    
    debug(__LINE__, "Found " . scalar(@stat_files) . " device stat file(s): " . join(', ', @stat_files));
    
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
        debug(__LINE__, "No device files modified, returning cached snapshot");
        return $last_snapshot;
    }
    
    debug(__LINE__, "Device files modified ($last_mtime -> $newest_mtime), reading and merging files");
    
    # Merge all device files
    my $merged = {
        Graphics => {
            Intel => {}
        }
    };
    
    foreach my $file (@stat_files) {
        my $filepath = "$stats_dir/$file";
        
        debug(__LINE__, "Reading device file: $filepath");
        
        eval {
            my $fh;
            unless (open($fh, '<', $filepath)) {
                debug(__LINE__, "Failed to open $filepath: $!");
                return;
            }
            
            local $/;
            my $json = <$fh>;
            close($fh);
            
            debug(__LINE__, "Read $file, JSON length: " . length($json) . " bytes");
            
            my $device_data = decode_json($json);
            
            # Merge this device's data into the main structure
            foreach my $node_name (keys %$device_data) {
                $merged->{Graphics}->{Intel}->{$node_name} = $device_data->{$node_name};
                debug(__LINE__, "Merged node '$node_name' from $file");
            }
        };
        if ($@) {
            debug(__LINE__, "Failed to read/parse $filepath: $@");
        }
    }
    
    # Update cache
    $last_snapshot = $merged;
    $last_mtime = $newest_mtime;
    $last_get_graphic_stats_time = time();
    
    debug(__LINE__, "Successfully merged " . scalar(keys %{$merged->{Graphics}->{Intel}}) . " device node(s)");
    
    return $last_snapshot;
}

sub pve_mod_starter {
    # Try to acquire startup lock FIRST (prevents race conditions)
    my $startup_fh;
    
    debug(__LINE__, "Trying to acquire startup lock: $startup_lock");
    
    unless (sysopen($startup_fh, $startup_lock, O_CREAT|O_EXCL|O_WRONLY, 0644)) {
        # Startup lock exists - check if it's stale
        debug(__LINE__, "Startup lock exists, checking if stale");
        
        if (open(my $check_fh, '<', $startup_lock)) {
            my $lock_pid = <$check_fh>;
            chomp $lock_pid if defined $lock_pid;
            close($check_fh);
            
            if (defined $lock_pid && $lock_pid =~ /^\d+$/) {
                debug(__LINE__, "Startup lock held by PID $lock_pid");

                if (is_process_alive($lock_pid)) {
                    debug(__LINE__, "Lock holder PID $lock_pid is still alive, waiting");
                } else {
                    # Lock holder is dead, remove stale lock
                    debug(__LINE__, "Lock holder PID $lock_pid is dead, removing stale startup lock");
                    unlink($startup_lock);
                    
                    # Try to acquire lock again
                    unless (sysopen($startup_fh, $startup_lock, O_CREAT|O_EXCL|O_WRONLY, 0644)) {
                        debug(__LINE__, "Failed to acquire startup lock on retry: $!");
                        return;
                    }
                    debug(__LINE__, "Acquired startup lock after removing stale lock");
                }
            } else {
                # Invalid PID in lock file, remove it
                debug(__LINE__, "Invalid PID in startup lock, removing");
                unlink($startup_lock);
                
                # Try to acquire lock again
                unless (sysopen($startup_fh, $startup_lock, O_CREAT|O_EXCL|O_WRONLY, 0644)) {
                    debug(__LINE__, "Failed to acquire startup lock on retry: $!");
                    return;
                }
                debug(__LINE__, "Acquired startup lock after removing invalid lock");
            }
        } else {
            debug(__LINE__, "Could not read startup lock file: $!");
            return;
        }
    } else {
        debug(__LINE__, "Acquired startup lock on first try");
    }
    
    # We have the startup lock
    print $startup_fh "$$\n";
    close($startup_fh);
    debug(__LINE__, "Wrote PID, $$, to startup lock");
}

sub pve_mod_worker {
    # Give the pid a unique name for easier identification
    $0 = "pve_mod_worker";

    # Ensure directory exists
    my $run_dir = '/var/run/pve-gpu';
    unless (-d $run_dir) {
        debug(__LINE__, "Creating directory $run_dir");
        mkdir($run_dir, 0755) or debug(__LINE__, "Failed to create $run_dir: $!");
    }
    
    # Acquire startup lock and start application
    pve_mod_starter();

    # Start graphics collectors
    start_graphics_collectors();

    # Start sensor collector
    # TBD

    # Start UPS collector
    # TBD

    # Start gui activity monitor process
    pve_mod_keep_alive();

    # Remove startup lock LAST
    unlink($startup_lock);
    debug(__LINE__, "Released startup lock");
    
    debug(__LINE__, "Collectors started successfully, returning");
}

sub pve_mod_keep_alive {
    debug(__LINE__, "Monitor process started with PID $$");
    while (1) {
        if(time() - $last_get_graphic_stats_time > $COLLECTOR_TIMEOUT) {
            debug(__LINE__, "No get_graphic_stats call in the last $COLLECTOR_TIMEOUT seconds, stopping collectors");
            stop_collectors();
            exit(0);
        }
        sleep(1);
        debug(__LINE__, "pve_mod_keep_alive still running");
    }
}

sub cleanup {
    unless ($is_collector_parent) {
        debug(__LINE__, "This process did not start collectors, skipping cleanup");
        return;
    }
    
    debug(__LINE__, "Starting cleanup (this should rarely happen)");
    
    # todo add remove of stat files

    # DON'T cleanup automatically - collectors should keep running
    # across worker process lifecycles
    # Only cleanup if explicitly called
}

# Remove the END block that automatically calls cleanup
# END { cleanup() }

# Instead, add a manual cleanup function that can be called explicitly
sub stop_collectors {
    debug(__LINE__, "Stopping all collectors");
    
    # Read current PIDs from lock file
    my @pids;
    if (open my $lock_fh, '<', $lock_file) {
        while (my $line = <$lock_fh>) {
            chomp $line;
            push @pids, $line if $line =~ /^\d+$/;
        }
        close($lock_fh);
    }
    
    if (@pids) {
        # Send SIGTERM to all collectors
        debug(__LINE__, "Sending SIGTERM to " . scalar(@pids) . " process(es)");
        foreach my $pid (@pids) {
            kill('TERM', $pid) if kill(0, $pid);
        }
        
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
            select(undef, undef, undef, 0.1); # sleep 0.1s
        }
        
        # Force kill any survivors
        foreach my $pid (@pids) {
            if (kill(0, $pid)) {
                debug(__LINE__, "Force killing process $pid");
                kill('KILL', $pid);
            }
        }
    }
    
    unlink $state_file if -f $state_file;
    unlink $lock_file if -f $lock_file;
    debug(__LINE__, "Cleanup complete");
}

END { cleanup() }

1;
