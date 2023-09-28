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


        

### IVC with agg - deep analysis

secondary_agg_instance_extractor .................1s                             ......180ms?
    aggregate_gemini_kzg_reduce_decider ...............357.087ms
    aggregate_gemini_kzg_pcs_batch_verify .............227.408ms
    aggregate_gemini_kzg_verify_kzg ...................225.905ms

// lot of msms due to hyrax
run_prove_secondary_agg_preprocess ...............4s                              .......350ms?
    same process as extractor ......................... 1s
    hyperplonk_setup_pcs_setup .........................140.507ms

    hyperplonk_preprocess
        compute_preprocessed_comms .................... 1.6s
            500 variable_base_msm-4096 
        
        compute_permutation_polys_and_comms ........... 800ms
            240 variable_base_msm-4096  


run_prove_secondary_agg_prove ....................5s
    witness_collector(same steps as extractor) .........1s

    350 variable_base_msm-4096 .........................

    pcs_batch_open-41 ..................................1s
        100 msm and sum_check

    

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


### Protostar 
#### Trivial Circuit - 0 constraints

    Without Aggregation

        primary acc using prove_steps Hyperplonk<Gemini<UnivariateKzg<Bn256>>>
        secondary acc using prove steps Hyperplonk<MultilinearIpa<grumpkin::G1Affine>>

        primary_proof .............. 7104 bytes, pairing proofs should be smaller?
            Hyperplonk<Gemini<UnivariateKzg<Bn256>>> 
                prove_decider ...... 475.822ms

        secondary_proof ............ 8448 bytes
            Hyperplonk<MultilinearIpa<grumpkin::G1Affine>>
                prove_decider_with_last_nark ................. 1.431s
                    pcs_batch_open-46 ................................. 915.468ms
                        msm and sumcheck take 250ms, missing?


    With Aggregation 

        secondary_agg_proof 32416 - bc of non-native ops, 
                                    using logn ipa proof size should be smaller
                                    
        primary_agg_proof 10208  30ms

    

### NOVA 

TrivialTestCircuit
    prove time ............ 1.0716 s
    size .................. 9347 bytes
        primary_proof ..... 4488 bytes
        secondaryproof..... 4491 bytes
    verify .................38.393 ms

StepCircuit - compute x^2 = y repeatedly for 22949 times for 3 steps
    stepCircuitSize:    22949
    time:              1.5770 s 
    size:             9671 bytes 

//arm64 
TrivialTestCircuit
    Prove: 2.8526s.
    PrimarySNARK_encoded: 4488 bytes.
    SecondarySNARK_encoded: 4491 bytes.
    Verify: 100.02ms. 

    StepCircuitSize-22949
    Prove: 4.3164 s


                      


SHA256

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


//arm64

    Message Length: 64
        Prove Time: 72.499ms.

    Message Length: 128
        Prove Time: 94.022ms.

    Message Length: 256
        Prove Time: 100.90ms.




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