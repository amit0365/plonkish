# Poseidon2
with additional advice for NUM_PARTIAL_SBOX = 4
witness_count: 24697

WITHOUT 
witness_count: 23767

                // let pid = sysinfo::get_current_pid().expect("Failed to get PID");
                // let (tx, rx) = mpsc::channel();

                // let total_cpu_usage = Arc::new(Mutex::new(0.0));
                // let total_samples = Arc::new(Mutex::new(0));
                // let total_cpu_usage_monitor = Arc::clone(&total_cpu_usage);
                // let total_samples_monitor = Arc::clone(&total_samples);

                // let max_memory = Arc::new(Mutex::new(0u64));
                // let max_cpu_usage = Arc::new(Mutex::new(0.0f32));
                
                // let max_memory_monitor = Arc::clone(&max_memory);
                // let max_cpu_usage_monitor = Arc::clone(&max_cpu_usage);
                
                // let monitoring = thread::spawn(move || {
                //     let mut sys = System::new_all();
                
                //     loop {
                //         sys.refresh_process(pid);
                //         thread::sleep(Duration::from_millis(1)); // Add a delay to measure CPU usage
                //         sys.refresh_process(pid); // Refresh again to get a non-zero CPU usage
                        
                //         if let Some(process) = sys.process(pid) {
                //             let current_memory = process.memory();
                //             let current_cpu = process.cpu_usage();
                
                //             // Update max memory
                //             {
                //                 let mut max_mem = max_memory_monitor.lock().unwrap();
                //                 if current_memory > *max_mem {
                //                     *max_mem = current_memory;
                //                 }
                //             }
                
                //             // Update max CPU usage
                //             {
                //                 let mut max_cpu = max_cpu_usage_monitor.lock().unwrap();
                //                 if current_cpu > *max_cpu {
                //                     *max_cpu = current_cpu;
                //                 }
                //             }

                //             // Update total CPU usage and sample count
                //             {
                //                 let mut total_cpu = total_cpu_usage_monitor.lock().unwrap();
                //                 let mut samples = total_samples_monitor.lock().unwrap();
                //                 *total_cpu += current_cpu;
                //                 *samples += 1;
                //             }
                //         } else {
                //             break; // Process no longer exists
                //         }
                
                //         // Exit if the main thread sends a message
                //         if rx.try_recv().is_ok() {
                //             break;
                //         }
                
                //         thread::sleep(Duration::from_millis(1));
                //     }
                // });
                
                // // Start timing
                // let start = Instant::now();

                //COMPUTATION


                // Notify monitoring thread to stop
                // let _ = tx.send(());
                
                // // Wait for monitoring to finish
                // monitoring.join().unwrap();
                
                // // Stop timing
                // let duration = start.elapsed();
                
                // // Retrieve peak values from the shared variables
                // let max_memory = max_memory.lock().unwrap();
                // let max_cpu_usage = max_cpu_usage.lock().unwrap();
                
                // // Print out the results
                // println!("Time elapsed: {:?}", duration);
                // println!("Peak CPU Usage: {:.2}%", *max_cpu_usage);
                // println!("Peak Memory Usage: {} MB", *max_memory / 1024 / 1024);

                // Retrieve the average CPU usage
                // let total_cpu_usage = total_cpu_usage.lock().unwrap();
                // let total_samples = total_samples.lock().unwrap();
                // let avg_cpu_usage = if *total_samples > 0 {
                //     *total_cpu_usage / *total_samples as f32
                // } else {
                //     0.0
                // };

                // // Print out the results
                // println!("Average CPU Usage: {:.2}%", avg_cpu_usage);