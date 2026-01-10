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
my $sensors_state_file = "$pve_mod_working_dir/sensors.json";
my $ups_state_file = "$pve_mod_working_dir/ups.json";

my $collectors_pid_file = "$pve_mod_working_dir/collectors.pids"; # List of collector PIDs
my $pve_mod_worker_lock = "$pve_mod_working_dir/pve_mod_worker.lock"; # PVE Mod worker lock 
my $startup_lock = "$pve_mod_working_dir/startup.lock";  # Exclusive startup lock
my $last_snapshot = {};
my $last_mtime = 0;
my $is_collector_parent = 0;  # Flag to track if this process started collectors
my $last_get_graphic_stats_time = 0;  # Track when get_graphic_stats was last called
my $COLLECTOR_TIMEOUT = 10;   # Stop collectors x seconds after last get_graphic_stats call
my $data_pull_interval = 1; # Interval in seconds between data pulls

my $intel_gpu_enabled = 1; # Set to 0 to disable Intel GPU support
my $amd_gpu_enabled   = 0; # Set to 1 to enable AMD GPU support (not yet implemented)
my $nvidia_gpu_enabled = 1; # Set to 1 to enable NVIDIA GPU support (not yet implemented)
my $ups_enabled = 1; # Set to 1 to enable UPS support
my $pve_mod_worker_pid;
my $pve_mod_worker_running = 0;

# UPS Configuration
my $ups_device = {
    ups_name => 'ups@192.168.3.2',  # Format: upsname[@hostname[:port]]
};

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
    my $intel_pull_interval = $data_pull_interval * 1000; # in milliseconds
    $intel_gpu_top_pid = open(my $fh, '-|', "intel_gpu_top -d $drm_dev -s $intel_pull_interval -l 2>&1");
    
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

# Parse information for graphical presentation. 
sub _parse_graphic_info {
    my ($line) = @_;

    # Create an intel file with 
    # Timestamp Device index, name, Render/3D, Blitter, Video, VideoEnhance, power consumption

    return undef;
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
    
    $0 = "pve-mod-gpu-nvidia-collector: $device->{index}";
    _debug(__LINE__, "NVIDIA collector started (stub implementation)");
    
    # Set up signal handlers for graceful shutdown
    my $shutdown = 0;
    $SIG{TERM} = sub {
        _debug(__LINE__, "NVIDIA collector received SIGTERM");
        $shutdown = 1;
    };
    $SIG{INT} = sub {
        _debug(__LINE__, "NVIDIA collector received SIGINT");
        $shutdown = 1;
    };
    
    # TODO: Implement actual NVIDIA monitoring
    while (!$shutdown) {
        _debug(__LINE__, "NVIDIA collector running (stub)");
        sleep $data_pull_interval;
    }
    
    _debug(__LINE__, "NVIDIA collector shutting down");
    exit 0;
}

# ============================================================================
# Unified Child Process Management
# ============================================================================

sub _start_child_collector {
    my ($collector_name, $collector_sub, $device) = @_;
    
    _debug(__LINE__, "Starting child collector: $collector_name");
    
    my $pid = fork();
    unless (defined $pid) {
        _debug(__LINE__, "fork failed for $collector_name: $!");
        return undef;
    }
    
    if ($pid == 0) {
        # Child process
        _debug(__LINE__, "In child process for $collector_name");
        $0 = "pve-mod-$collector_name";
        $collector_sub->($device);
        exit(0);
    }
    
    # Parent process
    _debug(__LINE__, "Forked child PID $pid for $collector_name");
    return $pid;
}

sub _write_collector_lock {
    my ($lock_path, @collector_entries) = @_;
    
    my $lock_fh;
    unless (open $lock_fh, '>', $lock_path) {
        _debug(__LINE__, "Failed to open lock file for writing: $!");
        return 0;
    }
    
    foreach my $entry (@collector_entries) {
        my ($pid, $name, $type) = @$entry;
        # Quote the name to preserve spaces
        print $lock_fh "$pid \"$name\" $type\n";
    }
    
    close($lock_fh);
    _debug(__LINE__, "Wrote " . scalar(@collector_entries) . " collector entries to lock file");
    return 1;
}

sub _read_collector_lock {
    my ($lock_path) = @_;
    
    my %collectors;
    return %collectors unless -f $lock_path;
    
    if (open my $lock_fh, '<', $lock_path) {
        while (my $line = <$lock_fh>) {
            chomp $line;
            # Match: PID "name with spaces" type
            if ($line =~ /^(\d+)\s+"([^"]+)"\s+(\S+)/) {
                $collectors{$2} = { pid => $1, type => $3 };
            }
        }
        close($lock_fh);
    }
    
    return %collectors;
}

sub _is_collector_running {
    my ($collector_name, $lock_path) = @_;
    
    my %collectors = _read_collector_lock($lock_path);
    
    if (exists $collectors{$collector_name}) {
        my $pid = $collectors{$collector_name}->{pid};
        if (_is_process_alive($pid)) {
            _debug(__LINE__, "Collector '$collector_name' already running with PID $pid");
            return $pid;
        } else {
            _debug(__LINE__, "Collector '$collector_name' PID $pid is stale");
        }
    }
    
    return undef;
}

# ============================================================================
# Temperature Sensors
# ============================================================================

sub _collector_for_temperature_sensors {
    my ($device) = @_;
    
    $0 = "pve-mod-sensors-collector";
    _debug(__LINE__, "Temperature sensor collector started");

    # return if lm-sensors is not installed
    unless (-x '/usr/bin/sensors') {
        _debug(__LINE__, "sensors not available, exiting");
        exit(1);
    }

    # Cache for drive and CPU names
    my %cache_ref;

    # Set up signal handlers for graceful shutdown
    my $shutdown = 0;
    $SIG{TERM} = sub {
        _debug(__LINE__, "Temperature sensor collector received SIGTERM");
        $shutdown = 1;
    };
    $SIG{INT} = sub {
        _debug(__LINE__, "Temperature sensor collector received SIGINT");
        $shutdown = 1;
    };

    while (!$shutdown) {
        my $sensorsData = _get_temperature_sensors(\%cache_ref);

        # Write to sensors state file
        eval {
            open my $ofh, '>', $sensors_state_file or die "Failed to open $sensors_state_file: $!";
            print $ofh $sensorsData;
            close $ofh;
            _debug(__LINE__, "Wrote temperature sensor data to $sensors_state_file");
        };
        if ($@) {
            _debug(__LINE__, "Error writing temperature sensor data: $@");
        }

        sleep $data_pull_interval unless $shutdown;
    }

    _debug(__LINE__, "Temperature sensor collector shutting down");
    exit 0;
}

sub _get_temperature_sensors {
    my ($cache_ref) = @_;
    
    my $sensorsOutput;

    # Collect sensor data from lm-sensors
    $sensorsOutput = `sensors -j 2>/dev/null | python3 -m json.tool`;
    
    _debug(__LINE__, "Raw sensors output collected");

    # sanitize output
    my $sensorsData = _sanitize_sensors($sensorsOutput);

    _debug(__LINE__, "Sanitized sensors output");

    # translate drive names (pass cache reference)
    $sensorsData = _get_drive_names($sensorsData, $cache_ref);

    _debug(__LINE__, "Translated drive names in sensors output");

    # translate CPU names (pass cache reference)
    $sensorsData = _get_cpu_name($sensorsData, $cache_ref);  

    _debug(__LINE__, "Translated CPU names in sensors output");  

    # Good, now add a master node called lm sensors exhanced by PVE MOD
    my $sensors_json;
    eval {
        $sensors_json = decode_json($sensorsData);
    };
    if ($@) {
        _debug(__LINE__, "Failed to parse final sensors JSON: $@");
        return $sensorsData;  # Return original output on parse error
    }
    my $enhanced_data = {
        "PVE MOD lm-sensors Enhanced" => $sensors_json
    };
    $sensorsData = JSON->new->pretty->encode($enhanced_data);



    return $sensorsData;
}

sub _sanitize_sensors {
    my ($sensorsOutput) = @_;

    # Sanitize JSON output to handle common lm-sensors parsing issues
    # Replace ERROR lines with placeholder values
    $sensorsOutput =~ s/ERROR:.+\s(\w+):\s(.+)/\"$1\": 0.000,/g;
    $sensorsOutput =~ s/ERROR:.+\s(\w+)!/\"$1\": 0.000,/g;
    
    # Remove trailing commas before closing braces
    $sensorsOutput =~ s/,\s*(})/$1/g;
    
    # Replace NaN values with null for valid JSON
    $sensorsOutput =~ s/\bNaN\b/null/g;
    
    # Fix duplicate SODIMM keys by appending temperature sensor number
    # This prevents JSON key overwrites when multiple SODIMM sensors exist
    # Example: "SODIMM":{"temp3_input":34.0} becomes "SODIMM3":{"temp3_input":34.0}
    $sensorsOutput =~ s/\"SODIMM\":\{\"temp(\d+)_input\"/\"SODIMM$1\":\{\"temp$1_input\"/g;

    return $sensorsOutput;
}

sub _get_drive_names {
    my ($sensorsOutput, $cache_ref) = @_;
    
    # Use empty hash if no cache reference provided (shouldn't happen)
    $cache_ref //= {};
    
    my @drive_names;
    
    # Parse sensors output to extract drive entries
    my $sensors_data;
    eval {
        $sensors_data = decode_json($sensorsOutput);
    };
    if ($@) {
        _debug(__LINE__, "Failed to parse sensors JSON: $@");
        return $sensorsOutput;  # Return original output on parse error
    }
    
    # Extract drive entries from sensors data
    my @entries = grep { 
        /^drivetemp-scsi-/ || /^drivetemp-nvme-/ || /^nvme-pci-/ 
    } keys %{$sensors_data};
    
    _debug(__LINE__, "Found " . scalar(@entries) . " drive entries in sensors output");

    foreach my $entry (@entries) {
        my ($dev_path, $model, $serial) = ("unknown", "unknown", "unknown");
        
        # Check cache first
        if (exists $cache_ref->{$entry}) {
            my $cached = $cache_ref->{$entry};
            $dev_path = $cached->{device_path};
            $model = $cached->{model};
            $serial = $cached->{serial};
            _debug(__LINE__, "Using cached drive info for $entry");
        } else {
            # Lookup drive information
            
            # ----- SCSI/SATA -----
            if ($entry =~ /^drivetemp-scsi-(\d+)-(\d+)/) {
                my ($host, $id) = ($1, $2);
                my $scsi_path = "/sys/class/scsi_disk/$host:$id:0:0/device/block";

                if (opendir(my $sdh, $scsi_path)) {
                    my @devs = grep { /^sd/ } readdir($sdh);
                    closedir($sdh);
                    if (@devs) {
                        $dev_path = "/dev/$devs[0]";
                        $model  = read_sysfs("/sys/class/block/$devs[0]/device/model");
                        $serial = read_sysfs("/sys/class/block/$devs[0]/device/serial");
                    }
                }

            # ----- Numeric NVMe -----
            } elsif ($entry =~ /^drivetemp-nvme-(\d+)/) {
                my $nvme_index = $1;
                $dev_path = "/dev/nvme${nvme_index}n1";
                if (-e $dev_path) {
                    $model  = read_sysfs("/sys/class/block/nvme${nvme_index}n1/device/model");
                    $serial = read_sysfs("/sys/class/block/nvme${nvme_index}n1/device/serial");
                }

            # ----- PCI-style NVMe -----
            } elsif ($entry =~ /^nvme-pci-(\w+)/) {
                my $pci_addr = $1;
                
                # Convert short PCI address to pattern
                # nvme-pci-0600 -> 0000:06:00
                # Format: domain:bus:device (function is usually .0)
                my $pci_pattern;
                if ($pci_addr =~ /^([0-9a-f]{2})([0-9a-f]{2})$/i) {
                    # Short format like "0600" -> "06:00"
                    my ($bus, $dev) = ($1, $2);
                    $pci_pattern = sprintf("%04x:%02x:%02x", 0, hex($bus), hex($dev));
                    _debug(__LINE__, "Converted PCI address $pci_addr to pattern $pci_pattern");
                } else {
                    # Already in some other format, use as-is
                    $pci_pattern = $pci_addr;
                }
                
                # Try multiple approaches to find the NVMe device
                my $found = 0;
                
                # Approach 1: Check /sys/class/nvme/
                my $nvme_dir = "/sys/class/nvme";
                _debug(__LINE__, "Searching for NVMe devices in $nvme_dir matching PCI pattern $pci_pattern");
                if (opendir(my $ndh, $nvme_dir)) {
                    my @nvme_devs = grep { /^nvme\d+$/ && -d "$nvme_dir/$_" } readdir($ndh);
                    closedir($ndh);
                    
                    _debug(__LINE__, "Found NVMe devices: " . join(", ", @nvme_devs));

                    foreach my $nvme_dev (@nvme_devs) {
                        # Check if this nvme device matches our PCI address
                        my $device_link = readlink("$nvme_dir/$nvme_dev/device");
                        if ($device_link && $device_link =~ /$pci_pattern/) {
                            _debug(__LINE__, "NVMe device $nvme_dev matches PCI pattern $pci_pattern");
                            # Found matching device
                            $dev_path = "/dev/$nvme_dev" . "n1";
                            $model  = read_sysfs("$nvme_dir/$nvme_dev/model");
                            $serial = read_sysfs("$nvme_dir/$nvme_dev/serial");
                            $found = 1;
                            _debug(__LINE__, "Found NVMe device via /sys/class/nvme: $dev_path (matched $pci_pattern)");
                            last;
                        }
                        _debug(__LINE__, "NVMe device $nvme_dev did not match PCI pattern $pci_pattern");
                    }
                }
                
                # Approach 2: Try direct block device lookup if not found
                if (!$found && opendir(my $bdh, "/sys/class/block")) {
                    my @block_devs = grep { /^nvme\d+n\d+$/ } readdir($bdh);
                    closedir($bdh);
                    
                    foreach my $block_dev (@block_devs) {
                        my $device_link = readlink("/sys/class/block/$block_dev/device");
                        if ($device_link && $device_link =~ /$pci_pattern/) {
                            $dev_path = "/dev/$block_dev";
                            # For block devices, go up to the nvme controller for model/serial
                            my $nvme_ctrl = $block_dev;
                            $nvme_ctrl =~ s/n\d+$//;  # nvme0n1 -> nvme0
                            $model  = read_sysfs("/sys/class/nvme/$nvme_ctrl/model");
                            $serial = read_sysfs("/sys/class/nvme/$nvme_ctrl/serial");
                            $found = 1;
                            _debug(__LINE__, "Found NVMe device via /sys/class/block: $dev_path (matched $pci_pattern)");
                            last;
                        }
                    }
                }
                
                unless ($found) {
                    _debug(__LINE__, "Could not find device for nvme-pci-$pci_addr (pattern: $pci_pattern)");
                }
            } else {
                next; # unknown device type
            }
            
            # Cache the lookup result
            $cache_ref->{$entry} = {
                device_path => $dev_path,
                model => $model,
                serial => $serial
            };
            
            _debug(__LINE__, "Drive: $entry -> $dev_path (Model: $model, Serial: $serial)");
        }

        # Add to result array
        push @drive_names, [$entry, $dev_path, $model, $serial];
    }

    # Now enhance the sensors_data structure directly (not as string manipulation)
    foreach my $drive_entry (@drive_names) {
        my ($original_name, $dev_path, $model, $serial) = @$drive_entry;
        
        # Add metadata directly to the data structure
        if (exists $sensors_data->{$original_name}) {
            $sensors_data->{$original_name}->{device_path} = $dev_path;
            $sensors_data->{$original_name}->{model} = $model;
            $sensors_data->{$original_name}->{serial} = $serial;
            _debug(__LINE__, "Enhanced $original_name with drive info");
        }
    }

    # Re-encode as pretty JSON
    my $enhanced_json = JSON->new->pretty->canonical->encode($sensors_data);
    
    return $enhanced_json;
}

sub _get_cpu_name {
    my ($sensorsOutput, $cache_ref) = @_;
    
    # Use empty hash if no cache reference provided
    $cache_ref //= {};
    
    # Parse sensors output to extract CPU entries
    my $sensors_data;
    eval {
        $sensors_data = decode_json($sensorsOutput);
    };
    if ($@) {
        _debug(__LINE__, "Failed to parse sensors JSON: $@");
        return $sensorsOutput;  # Return original output on parse error
    }
    
    # Extract CPU entries from sensors data
    my @entries = grep { /^coretemp-isa-/ || /^k10temp-pci-/ } keys %{$sensors_data};
    
    _debug(__LINE__, "Found " . scalar(@entries) . " CPU entries in sensors output");
    
    foreach my $entry (@entries) {
        my ($cpu_model, $pkg) = ("unknown", "unknown");
        
        # Check cache first
        if (exists $cache_ref->{$entry}) {
            my $cached = $cache_ref->{$entry};
            $cpu_model = $cached->{model};
            $pkg = $cached->{package};
            _debug(__LINE__, "Using cached CPU info for $entry");
        } else {
            # Lookup CPU information
            
            # ----- Intel coretemp -----
            if ($entry =~ /^coretemp-isa-(\d+)/) {
                my $isa_id = $1;
                
                # Find matching hwmon device
                for my $hwmon (glob "/sys/class/hwmon/hwmon*") {
                    my $name = read_sysfs("$hwmon/name");
                    next unless $name eq 'coretemp';
                    
                    my $dev = readlink("$hwmon/device");
                    next unless $dev;
                    
                    # coretemp.0 → package 0
                    if ($dev =~ /\.([0-9]+)$/) {
                        $pkg = $1;
                        $cpu_model = _cpu_model_by_package($pkg);
                        _debug(__LINE__, "Found Intel CPU: $entry -> Package $pkg, Model: $cpu_model");
                        last;
                    }
                }
            }
            
            # ----- AMD k10temp -----
            elsif ($entry =~ /^k10temp-pci-(\w+)/) {
                my $pci_addr = $1;
                
                # Convert short PCI address to pattern
                # k10temp-pci-00c3 -> 0000:00:18.3
                my $pci_pattern;
                if ($pci_addr =~ /^([0-9a-f]{2})([0-9a-f]{2})$/i) {
                    # Short format like "00c3" -> "00:18" (bus:device)
                    my ($bus, $dev_func) = ($1, $2);
                    $pci_pattern = sprintf("%04x:%02x:%02x", 0, hex($bus), hex($dev_func));
                    _debug(__LINE__, "Converted PCI address $pci_addr to pattern $pci_pattern");
                }
                
                # Find matching hwmon device
                for my $hwmon (glob "/sys/class/hwmon/hwmon*") {
                    my $name = read_sysfs("$hwmon/name");
                    next unless $name eq 'k10temp';
                    
                    my $dev = readlink("$hwmon/device");
                    next unless $dev;
                    
                    if ($dev =~ /$pci_pattern/ || $dev =~ /$pci_addr/) {
                        # For AMD, package/node info might be in different location
                        # Try to determine from PCI device or use 0 as default
                        $pkg = 0;
                        
                        # Attempt to find package from CPU topology
                        if (opendir(my $dh, "/sys/devices/system/cpu")) {
                            my @cpus = grep { /^cpu\d+$/ } readdir($dh);
                            closedir($dh);
                            
                            foreach my $cpu (@cpus) {
                                my $cpu_pkg = read_sysfs("/sys/devices/system/cpu/$cpu/topology/physical_package_id");
                                if ($cpu_pkg ne "unknown" && $cpu_pkg =~ /^\d+$/) {
                                    $pkg = $cpu_pkg;
                                    last;
                                }
                            }
                        }
                        
                        $cpu_model = _cpu_model_by_package($pkg);
                        _debug(__LINE__, "Found AMD CPU: $entry -> Package $pkg, Model: $cpu_model");
                        last;
                    }
                }
            }
            
            # Cache the lookup result
            $cache_ref->{$entry} = {
                model => $cpu_model,
                package => $pkg
            };
            
            _debug(__LINE__, "CPU: $entry -> Package $pkg (Model: $cpu_model)");
        }
        
        # Add metadata directly to the data structure
        if (exists $sensors_data->{$entry}) {
            $sensors_data->{$entry}->{cpu_model} = $cpu_model;
            $sensors_data->{$entry}->{cpu_package} = $pkg;
            _debug(__LINE__, "Enhanced $entry with CPU info");
        }
    }
    
    # Re-encode as pretty JSON
    my $enhanced_json = JSON->new->pretty->canonical->encode($sensors_data);
    
    return $enhanced_json;
}

sub read_sysfs {
    my ($path) = @_;
    
    return "unknown" unless defined $path && -f $path;
    
    if (open my $fh, '<', $path) {
        my $value = <$fh>;
        close $fh;
        
        if (defined $value) {
            chomp $value;
            # Remove leading/trailing whitespace
            $value =~ s/^\s+|\s+$//g;
            return $value ne '' ? $value : "unknown";
        }
    }
    
    return "unknown";
}

# Helper function to get CPU model by package ID
sub _cpu_model_by_package {
    my ($pkg) = @_;
    
    # Try to read from /proc/cpuinfo
    if (open my $fh, '<', '/proc/cpuinfo') {
        my $current_pkg = -1;
        my $model_name = "unknown";
        
        while (my $line = <$fh>) {
            chomp $line;
            
            # Extract physical id
            if ($line =~ /^physical id\s+:\s+(\d+)/) {
                $current_pkg = $1;
            }
            
            # Extract model name
            if ($line =~ /^model name\s+:\s+(.+)$/) {
                $model_name = $1;
                $model_name =~ s/^\s+|\s+$//g;  # Trim whitespace
                
                # If this is the package we're looking for, return it
                if ($current_pkg == $pkg) {
                    close($fh);
                    return $model_name;
                }
            }
        }
        close($fh);
        
        # If we didn't find the specific package, return the last model found
        # (single socket systems won't have physical id)
        return $model_name if $model_name ne "unknown";
    }
    
    return "unknown";
}

# ============================================================================
# UPS Support
# ============================================================================

sub _collector_for_ups {
    my ($device) = @_;
    
    $0 = "pve-mod-ups-collector";
    _debug(__LINE__, "UPS collector started");
    
    # Set up signal handlers for graceful shutdown
    my $shutdown = 0;
    $SIG{TERM} = sub {
        _debug(__LINE__, "UPS collector received SIGTERM");
        $shutdown = 1;
    };
    $SIG{INT} = sub {
        _debug(__LINE__, "UPS collector received SIGINT");
        $shutdown = 1;
    };
    while (!$shutdown) {
        my $upsData = _get_ups_status($device->{ups_name});

        # Write to ups state file
        eval {
            open my $ofh, '>', $ups_state_file or die "Failed to open $ups_state_file: $!";
            print $ofh $upsData;
            close $ofh;
            _debug(__LINE__, "Wrote ups data to $ups_state_file");
        };
        if ($@) {
            _debug(__LINE__, "Error writing ups data: $@");
        }

        sleep $data_pull_interval unless $shutdown;
    }
    _debug(__LINE__, "UPS collector shutting down");
    exit 0;
}

sub _get_ups_status {
    my ($ups_name) = @_;

    # upsc upsname[@hostname[:port]]
    my $cmd = "upsc $ups_name 2>/dev/null";
    
    _debug(__LINE__, "Running command: $cmd");
    
    # Execute command and capture output
    my $output = `$cmd`;

    _debug(__LINE__, "upsc command output collected");

    my $exit_code = $? >> 8;
    
    _debug(__LINE__, "upsc command exited with code $exit_code");

    if ($exit_code != 0) {
        _debug(__LINE__, "upsc command failed with exit code $exit_code");
        return encode_json({ error => "Failed to execute upsc for $ups_name" });
    }
    
    _debug(__LINE__, "upsc command executed successfully");

    # Convert upsc output to nested hash structure
    my $ups_data = _parse_upsc_output($output);

    _debug(__LINE__, "Parsed upsc output for $ups_name");
    
    # Check if we got any data
    unless (keys %$ups_data) {
        _debug(__LINE__, "No data received from upsc for $ups_name");
        return encode_json({ error => "No data from UPS $ups_name" });
    }
    
    # Wrap in UPS name structure
    my $result = {
        $ups_name => $ups_data
    };
    
    _debug(__LINE__, "Successfully parsed UPS data for $ups_name");
    
    # Return as pretty JSON
    return JSON->new->pretty->canonical->encode($result);
}

sub _parse_upsc_output {
    my ($output) = @_;
    
    my $ups_data = {};
    
    _debug(__LINE__, "Parsing upsc output");

    eval {
        foreach my $line (split /\n/, $output) {
            # Skip empty lines and SSL init message
            next if $line =~ /^\s*$/;
            next if $line =~ /^Init SSL/;
            
            # Parse key-value pairs (format: "key: value")
            if ($line =~ /^([^:]+):\s*(.*)$/) {
                my ($key, $value) = ($1, $2);

                # Trim whitespace
                $key =~ s/^\s+|\s+$//g;
                $value =~ s/^\s+|\s+$//g;
                
                # Store as flat key-value pairs (no nesting)
                # Convert numeric values to numbers, keep strings as strings
                if ($value =~ /^-?\d+\.?\d*$/) {
                    $ups_data->{$key} = $value + 0;
                } else {
                    $ups_data->{$key} = $value;
                }
            }
        }
    };
    if ($@) {
        _debug(__LINE__, "Error parsing upsc output: $@");
    }
    
    _debug(__LINE__, "Completed parsing upsc output");

    return $ups_data;
}

# ============================================================================
# Supporting functions
# ============================================================================

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

# Generic function to check if required executable exists
sub _check_executable {
    my ($exec_path, $type) = @_;
    
    unless (-x $exec_path) {
        _debug(__LINE__, "$exec_path not executable for $type");
        return 0;
    }
    _debug(__LINE__, "$exec_path is executable");
    return 1;
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

sub get_sensors_stats {
    _debug(__LINE__, "get_sensors_stats called");

    # Start PVE Mod
    _pve_mod_starter();

    unless (-f $sensors_state_file) {
        _debug(__LINE__, "Sensors state file does not exist: $sensors_state_file");
        return {};
    }

    my $sensors_data;
    eval {
        open my $fh, '<', $sensors_state_file or die "Failed to open $sensors_state_file: $!";
        local $/;
        my $json = <$fh>;
        close($fh);
        $sensors_data = $json;
        _debug(__LINE__, "Read sensors data, JSON length: " . length($json) . " bytes");
        _debug(__LINE__, "Read sensors data from $sensors_state_file");
    };
    if ($@) {
        _debug(__LINE__, "Failed to read/parse sensors data: $@");
        return {};
    }


    # Notify pve_mod_worker of activity
    _notify_pve_mod_worker();

    return $sensors_data;
}

sub get_ups_stats {
    _debug(__LINE__, "get_ups_stats called");

    # Start PVE Mod
    _pve_mod_starter();

    unless (-f $ups_state_file) {
        _debug(__LINE__, "UPS state file does not exist: $ups_state_file");
        return {};
    }

    my $ups_data;
    eval {
        open my $fh, '<', $ups_state_file or die "Failed to open $ups_state_file: $!";
        local $/;
        my $json = <$fh>;
        close($fh);
        $ups_data = $json;
        _debug(__LINE__, "Read UPS data, JSON length: " . length($json) . " bytes");
        _debug(__LINE__, "Read UPS data from $ups_state_file");
    };
    if ($@) {
        _debug(__LINE__, "Failed to read/parse UPS data: $@");
        return {};
    }

    # Notify pve_mod_worker of activity
    _notify_pve_mod_worker();

    return $ups_data;
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

    # Read existing collectors from lock file
    my %existing_collectors = _read_collector_lock($collectors_pid_file);
    
    # Generalized device collector management for future AMD/NVIDIA support
    my @all_devices;
    my @all_types;
    my @all_collector_subs;

    # Intel
    if ($intel_gpu_enabled) {
        _debug(__LINE__, "Intel GPU support enabled");
        _debug(__LINE__, "Checking for intel_gpu_top");
        
        return unless _check_executable('/usr/bin/intel_gpu_top', 'Intel');
        
        my @intel_devices = _get_intel_gpu_devices();
        unless (@intel_devices) {
            _debug(__LINE__, "No Intel GPU devices found");
        } else {
            _debug(__LINE__, "Found " . scalar(@intel_devices) . " Intel GPU device(s)");
            foreach my $device (@intel_devices) {
                push @all_devices, $device;
                push @all_types, 'intel';
                push @all_collector_subs, \&_collector_for_intel_device;
            }
        }
    }
    
    # AMD (future)
    if ($amd_gpu_enabled) {
        _debug(__LINE__, "AMD GPU support enabled");

        return unless _check_executable('/usr/bin/rocm-smi', 'AMD');

        my @amd_devices = _get_amd_gpu_devices();
        _debug(__LINE__, "Got " . scalar(@amd_devices) . " AMD devices");
        foreach my $device (@amd_devices) {
            push @all_devices, $device;
            push @all_types, 'amd';
            push @all_collector_subs, \&_collector_for_amd_device;
        }
    }
    
    # NVIDIA (future)
    if ($nvidia_gpu_enabled) {
        _debug(__LINE__, "NVIDIA GPU support enabled");

        my @nvidia_devices = get_nvidia_gpu_devices();
        _debug(__LINE__, "Got " . scalar(@nvidia_devices) . " NVIDIA devices");
        foreach my $device (@nvidia_devices) {
            push @all_devices, $device;
            push @all_types, 'nvidia';
            push @all_collector_subs, \&collector_for_nvidia_device;
        }
    }

    _debug(__LINE__, "Finished detecting devices. Total collectors to manage: " . scalar(@all_devices));

    my @collector_entries;
    
    for (my $i = 0; $i < @all_devices; $i++) {
        my $device = $all_devices[$i];
        my $type = $all_types[$i];
        my $collector_sub = $all_collector_subs[$i];
        my $device_name = $device->{card} // $device->{name} // "device$i";
        
        # Check if collector already running
        my $existing_pid = _is_collector_running($device_name, $collectors_pid_file);
        if ($existing_pid) {
            _debug(__LINE__, "Collector for $type $device_name already running with PID $existing_pid");
            push @collector_entries, [$existing_pid, $device_name, $type];
            next;
        }
        
        # Start new collector
        my $pid = _start_child_collector($device_name, $collector_sub, $device);
        if ($pid) {
            push @collector_entries, [$pid, $device_name, $type];
        }
    }
    
    # Write all collector PIDs to lock file
    unless (_write_collector_lock($collectors_pid_file, @collector_entries)) {
        _debug(__LINE__, "Failed to write lock file, terminating collectors");
        foreach my $entry (@collector_entries) {
            kill 'TERM', $entry->[0];
        }
        return;
    }
    
    # Wait briefly to ensure collectors are running
    sleep 0.1;

    # Verify collectors are alive
    my $any_alive = 0;
    foreach my $entry (@collector_entries) {
        my ($pid, $name, $type) = @$entry;
        if (kill(0, $pid)) {
            $any_alive = 1;
            _debug(__LINE__, "Verified $type collector $name (PID $pid) is alive");
        } else {
            _debug(__LINE__, "WARNING - $type collector $name (PID $pid) died immediately!");
        }
    }
    
    unless ($any_alive) {
        _debug(__LINE__, "ERROR - No collectors alive after fork!");
        return;
    }

    _debug(__LINE__, "All graphics collectors started successfully");
}

sub _start_sensors_collector {
    _debug(__LINE__, "Starting temperature sensor collector");
    
    # Check if sensors is available
    unless (-x '/usr/bin/sensors') {
        _debug(__LINE__, "sensors not available, skipping");
        return;
    }
    
    # Check if already running
    my $existing_pid = _is_collector_running('sensors', $collectors_pid_file);
    if ($existing_pid) {
        _debug(__LINE__, "Sensors collector already running with PID $existing_pid");
        return;
    }
    
    # Start the collector
    my $pid = _start_child_collector('sensors', \&_collector_for_temperature_sensors, { name => 'sensors' });
    
    if ($pid) {
        # Read existing entries
        my @collector_entries;
        my %existing = _read_collector_lock($collectors_pid_file);
        foreach my $name (keys %existing) {
            push @collector_entries, [$existing{$name}->{pid}, $name, $existing{$name}->{type}];
        }
        
        # Add sensors entry
        push @collector_entries, [$pid, 'sensors', 'sensors'];
        
        # Write updated lock file
        unless (_write_collector_lock($collectors_pid_file, @collector_entries)) {
            _debug(__LINE__, "Failed to update lock file, terminating sensors collector");
            kill 'TERM', $pid;
            return;
        }
        
        # Verify it's alive
        sleep 0.1;
        if (kill(0, $pid)) {
            _debug(__LINE__, "Verified sensors collector (PID $pid) is alive");
        } else {
            _debug(__LINE__, "WARNING - Sensors collector (PID $pid) died immediately!");
        }
    }
}

sub _start_ups_collector {

    if ($ups_enabled == 0) {
        _debug(__LINE__, "UPS support not enabled, skipping collector startup");
        return;
    }

    _debug(__LINE__, "Starting UPS collector");
    
    # Check if UPS is configured
    unless (defined $ups_device && $ups_device->{ups_name}) {
        _debug(__LINE__, "No UPS configured, skipping collector startup");
        return;
    }
    
    # Check if already running
    my $existing_pid = _is_collector_running('ups', $collectors_pid_file);
    if ($existing_pid) {
        _debug(__LINE__, "UPS collector already running with PID $existing_pid");
        return;
    }
    
    # Start the collector
    my $pid = _start_child_collector('ups', \&_collector_for_ups, $ups_device);
    
    if ($pid) {
        # Read existing entries
        my @collector_entries;
        my %existing = _read_collector_lock($collectors_pid_file);
        foreach my $name (keys %existing) {
            push @collector_entries, [$existing{$name}->{pid}, $name, $existing{$name}->{type}];
        }
        
        # Add UPS entry
        push @collector_entries, [$pid, 'ups', 'ups'];
        
        # Write updated lock file
        unless (_write_collector_lock($collectors_pid_file, @collector_entries)) {
            _debug(__LINE__, "Failed to update lock file, terminating UPS collector");
            kill 'TERM', $pid;
            return;
        }
        
        # Verify it's alive
        sleep 0.1;
        if (kill(0, $pid)) {
            _debug(__LINE__, "Verified UPS collector (PID $pid) is alive");
        } else {
            _debug(__LINE__, "WARNING - UPS collector (PID $pid) died immediately!");
        }
    }
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

    _pve_mod_hello();

    # Ensure directory exists
    _ensure_pve_mod_directory_exists();

    # Try to get the lock
    _debug(__LINE__, "Trying to acquire startup lock: $startup_lock");
    my $startup_fh = _acquire_exclusive_lock($startup_lock, 'startup lock');
    return unless $startup_fh;
    
    # SECOND CHECK (after lock) - verify nothing changed while waiting
    if (_is_pve_mod_worker_running()) {
        _debug(__LINE__, "Worker started by another process while we waited for lock");
        close($startup_fh);
        unlink($startup_lock);
        return "already running";
    }
    
    # Now we KNOW we're the only one starting things
    print $startup_fh "$$\n";
    $startup_fh->flush();
    _debug(__LINE__, "Wrote PID, $$, to startup lock");

    # Start sensors collector first
    _start_sensors_collector();

    # Start graphics collectors
    _start_graphics_collectors();

    # Start UPS collector
    _start_ups_collector();

    _debug(__LINE__, "All collectors started");

    # Start pve mod worker
    _pve_mod_worker();

    # Remove startup lock LAST
    unlink($startup_lock);
    _debug(__LINE__, "Released startup lock");
    
    _debug(__LINE__, "pve_mod_worker started successfully, returning");
}

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
        $0 = "pve_mod_worker_controller";
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
    if (open my $lock_fh, '<', $collectors_pid_file) {
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
    if (-f $collectors_pid_file) {
        unlink $collectors_pid_file or _debug(__LINE__, "Failed to remove $collectors_pid_file: $!");
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
