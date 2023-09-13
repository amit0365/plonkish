## IVC without agg - 5s

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