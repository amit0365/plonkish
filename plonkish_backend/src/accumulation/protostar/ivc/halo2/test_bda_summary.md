## IVC without agg - 5s
    const NUM_VARS: usize = 14;
    const NUM_STEPS: usize = 3;
    
## IVC with agg - 140s

    run_secondary_agg_circuit - 72.333µs

    run_prove_secondary_agg - 8.831s
        100 variable-base-msm-4096 worst 160ms
        1 witness collector 15s - expected
        several sumcheck prove but at worse takes 125ms
        1 pcs batch open 1s - expected
        
    run_verify_secondary_agg - 69.785ms
        40 variable_base_msm-37/4096 

    run_primary_agg_circuit - 72.333µs

    run_prove_primary_agg - 119.5s -- 
        100 variable-base-msm-2097152 0.3 - 2s outlier 3.4 seconds, confusing as most have the same scalar length
        1 witness collector 15s - expected
        several sumcheck prove but at worse takes 2ms
        1 pcs batch open 20s - expected

    run_verify_primary_agg - 28ms - expected
        2 variable_base_msm-37/22  

    run_final_pairing_check - 1ms 


        

### IVC without agg - deep analysis

primary_agg_instance_extractor ............................. 13.451s

   primary_agg_verify_ipa_grumpkin_ivc_with_last_nark
        reduce_decider ............................8.640s
            ipa .........................8.052s

   primary_agg_verify_hyrax_hyperplonk.....................................3.278s
··   verify_hyrax_hyperplonk_pcs_batch_verify ..............................244.745ms
··     verify_hyrax_hyperplonk_verify_hyrax ..................................2.656s
····     verify_hyrax_hyperplonk_verify_hyrax_verify_ipa .....................2.323s


primary_agg_preprocess ......55.816s

    input_halo2_circuit .................20s
        same steps as extractor ................ 13.5s
        circuit_info?

    hyperplonk_setup ....................24s
        powers of g1 ....................................7.85s
            window_table .....................................4s
            kzg_fixed_base_msm_powers_of_s_g1-2097152 ........3.220s

        powers of g2 ....................................15.7s
            window_table .....................................5s
            kzg_fixed_base_msm_powers_of_s_g2-2097152 ........10.575s

        
    hyperplonk_preprocess ...............9s
        compute_preprocessed_comms...............4.56s
            17 variable_base_msm-2097152 .....3s

        compute_permutation_polys_and_comms......4.146s
            7 variable_base_msm-2097152 ..... 3s


primary_agg_prove .......... 56s

    witness collector ................ 16s  
        (same steps as extractor)
    7 variable_base_msm-2097152 ...... 2s
    permutation_z_polys-8 ............ 1.325s
    4 variable_base_msm-2097152 ...... 10.5s
    sum_check_prove-21-5 ............. 5.544s

    pcs_batch_open ...................... 20s
        6 variable_base_msm-2097152 ............ 15s 
        other low msms take .................... 4s
        merged poly ............................ 755.520ms
        sum_check_prove-21-2 ................... 307.051ms



## Nova comparison

### SHA256

    Message Length: 64
        Prove Time  ......... 2.5564s.
        Verify Time ........ 77.407ms.
        size ............... 9970 bytes

    Message Length: 128
        Prove Time  ......... 4.5065s.
        Verify Time ........ 142.14ms.
        size ............... 10268 bytes

    Message Length: 256
        Prove Time ......... 8.2349s.
        Verify Time ........ 280.85ms.
        size ............... 10557 bytes


CompressedSNARK-Prove - x^2 = y for 3 steps
    StepCircuitSize:    22949
    time:              1.5770 s 
    size:             9671 bytes 



------
prove_decider-primary-14 and prove_decider_with_last_nark-secondary-14
    two instances of sum_check_prove-14-5/sum_check_prove-14-2
        sum_check_prove_round-0 takes 30ms while for later iterations decay exponentially -- 2 instances in each branch
        degree 5 with 14 variables take 50ms while degree 2 takes 535.250µs
        using karatsuba mult algo for classic sumcheck -- 
        counter-intuitive why later iterations take less time? ask han -- is this exploiting symmetries in the roots of unity like fft

prove_accumulation_from_nark-primary/secondary - 10 instances and prove_accumulation_from_nark-secondary-14(called once) 
-- only 2 instances
    evaluate_compressed_cross_term_sums takes 30ms while evaluate_zeta_cross_term_poly takes 0.5ms 
    done by hadamard evaluator - using lagrange interpolate with x points on bh and eval using a cache
    cross terms expr comes from ProtostarProverParam through pp

prove_accumulation_from_nark-primary-14/secondary - 10 instances and prove_decider_with_last_nark-secondary-14(called once) -- only 2 instances
    witness_collector-0 takes 50ms -- implementing a new multlinear poly which takes in witnesses for rounds, challenges. should depend on length of num_vars which is expected to be large so expected 

used by kzg and other pcs, variable-base-msm -- already uses pipenger 