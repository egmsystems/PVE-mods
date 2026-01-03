package PVE::API2::GPUMonitor;

use strict;
use warnings;
use JSON;
use POSIX qw(WNOHANG);
use Fcntl qw(:flock);
use Time::HiRes qw(time);
use Fcntl qw(:flock O_CREAT O_EXCL O_WRONLY);


my $state_file = '/var/run/pve-gpu/stats.json';
my $lock_file = '/var/run/pve-gpu/pve-gpu-collector.lock';
my $last_snapshot = {};
my $last_mtime = 0;
my $is_collector_parent = 0;  # Flag to track if this process started collectors
my $last_get_stats_time = 0;  # Track when get_stats was last called
my $COLLECTOR_TIMEOUT = 0;   # Stop collectors x seconds after last get_stats call

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
                warn "DEBUG get_intel_gpu_devices: Found GPU device: $card -> $name ($path)";
            }
        }
        close $fh;
    } else {
        warn "DEBUG get_intel_gpu_devices: Failed to run intel_gpu_top -L: $!";
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
    
    warn "DEBUG collector_for_intel_device: Collector started for device: $drm_dev, writing to $device_state_file";
    
    # Set up signal handlers for graceful shutdown
    my $shutdown = 0;
    $SIG{TERM} = sub {
        warn "DEBUG collector_for_intel_device: Collector for $device->{card} received SIGTERM";
        $shutdown = 1;
        kill 'TERM', $intel_gpu_top_pid if defined $intel_gpu_top_pid && $intel_gpu_top_pid > 0;
    };
    $SIG{INT} = sub {
        warn "DEBUG collector_for_intel_device: Collector for $device->{card} received SIGINT";
        $shutdown = 1;
        kill 'TERM', $intel_gpu_top_pid if defined $intel_gpu_top_pid && $intel_gpu_top_pid > 0;
    };
    
    # Run intel_gpu_top once and keep reading from it
    warn "DEBUG: About to open pipe to intel_gpu_top";
    $intel_gpu_top_pid = open(my $fh, '-|', "intel_gpu_top -d $drm_dev -s 1000 -l 2>&1");
    
    unless (defined $intel_gpu_top_pid && $intel_gpu_top_pid > 0) {
        warn "DEBUG collector_for_intel_device: Failed to run intel_gpu_top for $drm_dev: $!";
        exit 1;
    }
    
    warn "DEBUG: Pipe opened successfully, PID=$intel_gpu_top_pid";
    
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
                    warn "DEBUG: Wrote stats to $device_state_file (line #$line_count)";
                };
                if ($@) {
                    warn "DEBUG: Error writing stats: $@";
                }
            }
        }
    }
    
    close $fh;
    warn "DEBUG collector_for_intel_device: Collector for $device->{card} shutting down";
    exit 0;
}

# ============================================================================
# AMD GPU Support (Placeholder)
# ============================================================================

sub get_amd_gpu_devices {
    # TODO: Implement AMD GPU detection
    # Use rocminfo or similar tools to detect AMD GPUs
    warn "DEBUG: AMD GPU support not yet implemented";
    return ();
}

sub parse_amd_gpu_line {
    my ($line) = @_;
    # TODO: Implement AMD GPU line parsing
    # Parse rocm-smi or similar output
    warn "DEBUG: AMD GPU line parsing not yet implemented";
    return undef;
}

sub collector_for_amd_device {
    my ($device) = @_;
    # TODO: Implement AMD GPU collector
    warn "DEBUG: AMD GPU collector not yet implemented";
    exit 0;
}

# ============================================================================
# NVIDIA GPU Support (Placeholder)
# ============================================================================

sub get_nvidia_gpu_devices {
    # TODO: Implement NVIDIA GPU detection
    # Use nvidia-smi to detect NVIDIA GPUs
    warn "DEBUG: NVIDIA GPU support not yet implemented";
    return ();
}

sub parse_nvidia_gpu_line {
    my ($line) = @_;
    # TODO: Implement NVIDIA GPU line parsing
    # Parse nvidia-smi output
    warn "DEBUG: NVIDIA GPU line parsing not yet implemented";
    return undef;
}

sub collector_for_nvidia_device {
    my ($device) = @_;
    # TODO: Implement NVIDIA GPU collector
    warn "DEBUG: NVIDIA GPU collector not yet implemented";
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

sub start_collector {
    warn "DEBUG start_collector: Checking if collector is already running";
    
    # Ensure directory exists
    my $run_dir = '/var/run/pve-gpu';
    unless (-d $run_dir) {
        warn "DEBUG start_collector: Creating directory $run_dir";
        mkdir($run_dir, 0755) or warn "DEBUG start_collector: Failed to create $run_dir: $!";
    }
    
    # Try to acquire startup lock FIRST (prevents race conditions)
    my $startup_lock = $lock_file . ".startup";
    my $startup_fh;
    
    warn "DEBUG start_collector: Trying to acquire startup lock: $startup_lock";
    
    unless (sysopen($startup_fh, $startup_lock, O_CREAT|O_EXCL|O_WRONLY, 0644)) {
        # Startup lock exists - check if it's stale
        warn "DEBUG start_collector: Startup lock exists, checking if stale";
        
        if (open(my $check_fh, '<', $startup_lock)) {
            my $lock_pid = <$check_fh>;
            chomp $lock_pid if defined $lock_pid;
            close($check_fh);
            
            if (defined $lock_pid && $lock_pid =~ /^\d+$/) {
                warn "DEBUG start_collector: Startup lock held by PID $lock_pid";

                if (is_process_alive($lock_pid)) {
                    warn "DEBUG start_collector: Lock holder PID $lock_pid is still alive, waiting";
                } else {
                    # Lock holder is dead, remove stale lock
                    warn "DEBUG start_collector: Lock holder PID $lock_pid is dead, removing stale startup lock";
                    unlink($startup_lock);
                    
                    # Try to acquire lock again
                    unless (sysopen($startup_fh, $startup_lock, O_CREAT|O_EXCL|O_WRONLY, 0644)) {
                        warn "DEBUG start_collector: Failed to acquire startup lock on retry: $!";
                        return;
                    }
                    warn "DEBUG start_collector: Acquired startup lock after removing stale lock";
                }
            } else {
                # Invalid PID in lock file, remove it
                warn "DEBUG start_collector: Invalid PID in startup lock, removing";
                unlink($startup_lock);
                
                # Try to acquire lock again
                unless (sysopen($startup_fh, $startup_lock, O_CREAT|O_EXCL|O_WRONLY, 0644)) {
                    warn "DEBUG start_collector: Failed to acquire startup lock on retry: $!";
                    return;
                }
                warn "DEBUG start_collector: Acquired startup lock after removing invalid lock";
            }
        } else {
            warn "DEBUG start_collector: Could not read startup lock file: $!";
            return;
        }
    } else {
        warn "DEBUG start_collector: Acquired startup lock on first try";
    }
    
    # We have the startup lock
    print $startup_fh "$$\n";
    close($startup_fh);
    warn "DEBUG start_collector: Wrote PID to startup lock";
    
    # NOW check if collectors are already running (while holding startup lock)
    if (-f $lock_file) {
        warn "DEBUG start_collector: Lock file exists: $lock_file";
        if (open(my $lock_fh, '<', $lock_file)) {
            warn "DEBUG start_collector: Opened lock file for reading";
            my @pids;
            while (my $line = <$lock_fh>) {
                chomp $line;
                push @pids, $line if $line =~ /^\d+$/;
            }
            close($lock_fh);
            
            warn "DEBUG start_collector: Found " . scalar(@pids) . " PIDs in lock file: " . join(", ", @pids);
            
            # Check if ANY collector is alive
            my $collector_running = 0;
            foreach my $pid (@pids) {
                warn "DEBUG start_collector: Checking PID $pid";
                
                if (is_process_alive($pid)) {
                    warn "DEBUG start_collector: Collector already running with PID $pid";
                    $collector_running = 1;
                    last;
                }
            }
            
            warn "DEBUG start_collector: Finished checking PIDs, collector_running = $collector_running";
            
            if ($collector_running) {
                warn "DEBUG start_collector: Releasing startup lock and returning - collector already running";
                unlink($startup_lock);
                return;
            }
            
            # All PIDs are dead, clean up stale lock
            warn "DEBUG start_collector: All PIDs dead, removing stale lock file";
            unlink($lock_file);
        } else {
            warn "DEBUG start_collector: Failed to open lock file: $!";
        }
    } else {
        warn "DEBUG start_collector: Lock file does not exist";
    }
    
    # If we reach here, no collectors are running - start new ones
    # Fork collector processes
    my @child_pids;

    if ($intel_gpu_enabled) {
        warn "DEBUG start_collector: Checking for intel_gpu_top";
        unless (-x '/usr/bin/intel_gpu_top') {
            warn "DEBUG start_collector: intel_gpu_top not executable";
            unlink($startup_lock);
            return;
        }
        warn "DEBUG start_collector: intel_gpu_top is executable";

        warn "DEBUG start_collector: Getting Intel GPU devices";
        my @intel_devices = get_intel_gpu_devices();
        warn "DEBUG start_collector: Got " . scalar(@intel_devices) . " Intel devices";
        
        unless (@intel_devices) {
            warn "DEBUG start_collector: No Intel GPU devices found";
            unlink($startup_lock);
            return;
        }
        warn "DEBUG start_collector: Found " . scalar(@intel_devices) . " Intel GPU device(s)";


        foreach my $device (@intel_devices) {
            warn "DEBUG start_collector: About to fork collector for Intel $device->{card}";
            my $pid = fork();
            
            unless (defined $pid) {
                warn "DEBUG start_collector: fork failed: $!";
                unlink($startup_lock);
                die "fork failed: $!";
            }
            
            if ($pid == 0) {
                # Child process
                warn "DEBUG start_collector: In child process for $device->{card}";
                collector_for_intel_device($device);
                # collector_for_intel_device calls exit(0)
            } else {
                warn "DEBUG start_collector: Forked child PID $pid for $device->{card}";
                push @child_pids, $pid;
            }
        }

        warn "DEBUG start_collector: Forked " . scalar(@child_pids) . " children: " . join(", ", @child_pids);
    }  
    
    # Write child PIDs to lock file
    if (open(my $lock_fh, '>', $lock_file)) {
        warn "DEBUG start_collector: Opened lock file for writing";
        foreach my $pid (@child_pids) {
            print $lock_fh "$pid\n";
        }
        close($lock_fh);
        warn "DEBUG start_collector: Wrote " . scalar(@child_pids) . " collector PID(s) to lock file";
    } else {
        warn "DEBUG start_collector: Failed to open lock file for writing: $!";
        foreach my $pid (@child_pids) {
            warn "DEBUG start_collector: Killing child $pid due to lock file write failure";
            kill 'TERM', $pid;
        }
        unlink($startup_lock);
        return;
    }
    
    # Wait briefly to ensure collector is actually running
    sleep 0.1;
    
    # Verify at least one child is still alive
    my $any_alive = 0;
    foreach my $pid (@child_pids) {
        if (kill(0, $pid)) {
            $any_alive = 1;
            warn "DEBUG start_collector: Verified child PID $pid is alive";
        } else {
            warn "DEBUG start_collector: WARNING - Child PID $pid died immediately!";
        }
    }
    
    unless ($any_alive) {
        warn "DEBUG start_collector: ERROR - No children alive after fork!";
    }
    
    # Start pve_mod_monitor process
    pve_mod_monitor();


    # Remove startup lock LAST
    unlink($startup_lock);
    warn "DEBUG start_collector: Released startup lock";
    
    warn "DEBUG start_collector: Collectors started successfully, returning";
}

sub get_stats {
    warn "DEBUG: get_stats() called";
    
    start_collector();

    my $stats_dir = '/var/run/pve-gpu';
    
    # Find all device-specific stat files
    my $dh;
    unless (opendir($dh, $stats_dir)) {
        warn "DEBUG: Failed to open stats directory: $stats_dir: $!";
        return $last_snapshot;
    }
    
    my @stat_files = grep { /^stats-card\d+\.json$/ } readdir($dh);
    closedir($dh);
    
    unless (@stat_files) {
        warn "DEBUG: No device stat files found in $stats_dir";
        return $last_snapshot;
    }
    
    warn "DEBUG: Found " . scalar(@stat_files) . " device stat file(s): " . join(', ', @stat_files);
    
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
        warn "DEBUG: No device files modified, returning cached snapshot";
        return $last_snapshot;
    }
    
    warn "DEBUG: Device files modified ($last_mtime -> $newest_mtime), reading and merging files";
    
    # Merge all device files
    my $merged = {
        Graphics => {
            Intel => {}
        }
    };
    
    foreach my $file (@stat_files) {
        my $filepath = "$stats_dir/$file";
        
        warn "DEBUG: Reading device file: $filepath";
        
        eval {
            my $fh;
            unless (open($fh, '<', $filepath)) {
                warn "DEBUG: Failed to open $filepath: $!";
                return;
            }
            
            local $/;
            my $json = <$fh>;
            close($fh);
            
            warn "DEBUG: Read $file, JSON length: " . length($json) . " bytes";
            
            my $device_data = decode_json($json);
            
            # Merge this device's data into the main structure
            foreach my $node_name (keys %$device_data) {
                $merged->{Graphics}->{Intel}->{$node_name} = $device_data->{$node_name};
                warn "DEBUG: Merged node '$node_name' from $file";
            }
        };
        if ($@) {
            warn "DEBUG: Failed to read/parse $filepath: $@";
        }
    }
    
    # Update cache
    $last_snapshot = $merged;
    $last_mtime = $newest_mtime;
    $last_get_stats_time = time();
    
    warn "DEBUG: Successfully merged " . scalar(keys %{$merged->{Graphics}->{Intel}}) . " device node(s)";
    
    return $last_snapshot;
}

sub pve_mod_monitor {
    return if $monitor_running;
    
    $monitor_pid = fork();

    if (!defined $monitor_pid) {
        warn "ERROR: Failed to fork monitor process: $!";
        return;
    }
    
    if ($monitor_pid == 0) {
        # Child process
        $0 = "pve_mod_monitor"; # Set process name for easier identification
        
        while (1) {
            if(time() - $last_get_stats_time > $COLLECTOR_TIMEOUT) {
                warn "DEBUG pve_mod_monitor: No get_stats call in the last $COLLECTOR_TIMEOUT seconds, stopping collectors";
                stop_collectors();
                exit(0);
            }
            sleep(1);
            warn "DEBUG pve_mod_monitor: pve_mod_monitor still running";
        }
        
        exit(0); # This shouldn't be reached, but just in case
    }
    
    # Parent process
    $monitor_running = 1;
    warn "DEBUG start_monitor: Monitor process started with PID $monitor_pid";
}

sub cleanup {
    unless ($is_collector_parent) {
        warn "DEBUG cleanup: This process did not start collectors, skipping cleanup";
        return;
    }
    
    warn "DEBUG cleanup: Starting cleanup (this should rarely happen)";
    
    # DON'T cleanup automatically - collectors should keep running
    # across worker process lifecycles
    # Only cleanup if explicitly called
}

# Remove the END block that automatically calls cleanup
# END { cleanup() }

# Instead, add a manual cleanup function that can be called explicitly
sub stop_collectors {
    warn "DEBUG stop_collectors: Stopping all collectors";
    
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
        warn "DEBUG stop_collectors: Sending SIGTERM to " . scalar(@pids) . " process(es)";
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
                warn "DEBUG stop_collectors: Force killing process $pid";
                kill('KILL', $pid);
            }
        }
    }
    
    unlink $state_file if -f $state_file;
    unlink $lock_file if -f $lock_file;
    warn "DEBUG stop_collectors: Cleanup complete";
}

END { cleanup() }

1;
