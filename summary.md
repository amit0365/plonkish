### IVC

#### Axiom api
2^k rows, but don’t need to be to power of two
k = 17, advice colns = 7

##### num_steps = 10
no compressing/compressing

Time for preprocess: 13.0877925s/10.246109042s
Time for accumulation_verifier: 379.770584ms called twice

Time for prove_steps: 60.414554542s/56.6916805s
    commit witness_poly      = no of advice colmns * msm 1.5s
    lookup_m_polys commit    = 1 msm   13.7 ms
    lookup_h_polys commit    = 2 msms  320 ms
    --/powers_of_zeta_poly   = 1 msm   356.354ms - can be shortened by CV
    cross_term_polys/zeta_cross_term  = 2/1 msm   200ms/16.4ms


Time for accumulation_verifier: 379.770584ms called 2*num_steps
Degree 2 verifier check - hadamard product, so normal CV doesn’t make any noticeable performance improvement to accumulation_verifier

Time for prove_decider: 17.884145209s/15.238887791s
(sanity-check) Time for verify_decider: 381.394125ms/338.456166ms


##### num_steps = 50
compressing

Time for preprocess: 10.084841083s

Time for prove_steps: 294.541182292s
Time for accumulation_verifier: 374.576542ms

Time for prove_decider: 14.410719s
Time for verify_decider: 338.679584ms

##### stats
k = 17, num_columns = 4, 
Time for prove_steps: 48.716075542s
copy_manager.advice_equalities 201042
copy_manager.assigned_advices 439632
Time for synthesize_accumulation_verifier: 407.343959ms

k = 18, num_columns = 2, 
Time for preprocess: 17.682898209s
Time for prove_steps: 61.899697958s
copy_manager.advice_equalities 166712
copy_manager.assigned_advices 365946
Time for synthesize_accumulation_verifier: 365.940208ms

k = 19, num_columns = 1, 
Time for preprocess: 33.020157417s
Time for prove_steps: 89.373715s
Time for prove_decider: 37.74634575s (batch open takes 80% of the time)
    prove_decider-primary-19 ..........................6.348s   
    prove_decider_with_last_nark-secondary-19 ........31.397s
    
copy_manager.advice_equalities 134351
copy_manager.constant_equalities 83279
copy_manager.assigned_constants 0
copy_manager.assigned_advices 300961
Time for synthesize_accumulation_verifier: 306.515791ms

for compressing decider takes 
Time for prove_decider: 43.251567875s, 5 secs increase from compressing?
Time for verify_decider: 1.130867084s

#### Han incomplete impl

10 steps, no compressing

Time for preprocess: 1.995075083s
Time for prove_steps: 5.060839917s
Time for prove_decider: 1.908527459s

##### TODO

check with no lookups, advice ~ 170k compared to with lookups 253k in nocompressing, why so many advices?

no compressing ~ 253k compressing ~ 300k but only one scalar_mul extra which costs 18k where else?

Start:   prove_accumulation_from_nark-primary-19
··Start:   witness_collector-0

synthesize_accumulation_verifier_start_copy_manager.advice_equalities: 0
synthesize_accumulation_verifier_start_copy_manager.constant_equalities: 0
synthesize_accumulation_verifier_start_copy_manager.assigned_advices: 0
synthesize_accumulation_verifier_start_copy_manager.assigned_constants: 0

before_assign_acc_copy_manager.advice_equalities: 7
before_assign_acc_copy_manager.constant_equalities: 8
before_assign_acc_copy_manager.assigned_advices: 0
before_assign_acc_copy_manager.assigned_constants: 0

acc_verifier_assign_acc_copy_manager.advice_equalities: 209
acc_verifier_assign_acc_copy_manager.constant_equalities: 306
acc_verifier_assign_acc_copy_manager.assigned_advices: 0
acc_verifier_assign_acc_copy_manager.assigned_constants: 0

verify_accumulation_from_nark_instance_copy_manager.advice_equalities: 225
verify_accumulation_from_nark_instance_copy_manager.constant_equalities: 357
verify_accumulation_from_nark_instance_copy_manager.assigned_advices: 0
verify_accumulation_from_nark_instance_copy_manager.assigned_constants: 0

squeeze challenge called 5 times - num_challenge = 1,1,2,1 - 
initialisation - 
    advice_equalities: 5908,
    constant_equalities: 4347
after that each takes 2.5k advice and 1.7k constant eq

verify_accumulation_from_nark_witness_copy_manager.advice_equalities: 15099
verify_accumulation_from_nark_witness_copy_manager.constant_equalities: 10711
verify_accumulation_from_nark_witness_copy_manager.assigned_advices: 0
verify_accumulation_from_nark_witness_copy_manager.assigned_constants: 0


verify_accumulation_from_nark_cross_term_copy_manager.advice_equalities: 15146
verify_accumulation_from_nark_cross_term_copy_manager.constant_equalities: 10799
verify_accumulation_from_nark_cross_term_copy_manager.assigned_advices: 0
verify_accumulation_from_nark_cross_term_copy_manager.assigned_constants: 0

has one squeeze challenge but takes 15k -- seems odd! but its beacause of abosorbing the acc -- checked with halo2lib
verify_accumulation_from_nark_squeeze_challenge_copy_manager.advice_equalities: 36697
verify_accumulation_from_nark_squeeze_challenge_copy_manager.constant_equalities: 26314
verify_accumulation_from_nark_squeeze_challenge_copy_manager.assigned_advices: 0
verify_accumulation_from_nark_squeeze_challenge_copy_manager.assigned_constants: 0

fold_acc_start_copy_manager.advice_equalities: 36697
fold_acc_start_copy_manager.constant_equalities: 26314
fold_acc_start_copy_manager.assigned_advices: 0
fold_acc_start_copy_manager.assigned_constants: 0

witness_comm_start_copy_manager.advice_equalities: 36909
witness_comm_start_copy_manager.constant_equalities: 26742
witness_comm_start_copy_manager.assigned_advices: 0
witness_comm_start_copy_manager.assigned_constants: 0

····Start:   fold_accumulator_from_nark witness_comms-5
····End:     fold_accumulator_from_nark witness_comms-5 ............................32.439ms
1 native scal_mul_secondary here take 33k advice, 18k copies (non-native scalar mul takes 387k advice and 100k advice copies)
5 scal_mul_secondary here take 90k advice copies and 37k constant eq
scalar_mul_secondary_finish_copy_manager.advice_equalities: 122514
scalar_mul_secondary_finish_copy_manager.constant_equalities: 62373
scalar_mul_secondary_finish_copy_manager.assigned_advices: 0
scalar_mul_secondary_finish_copy_manager.assigned_constants: 0

witness_comm_mul_base_finish_copy_manager.advice_equalities: 122726
witness_comm_mul_base_finish_copy_manager.constant_equalities: 62797
witness_comm_mul_base_finish_copy_manager.assigned_advices: 0
witness_comm_mul_base_finish_copy_manager.assigned_constants: 0

····Start:   fold_accumulator_from_nark e_comm
····End:     fold_accumulator_from_nark e_comm .....................................6.880ms
1 scal_mul_secondary here take 18k -- check with halo2lib
e_comm_finish_copy_manager.advice_equalities: 140023
e_comm_finish_copy_manager.constant_equalities: 70045
e_comm_finish_copy_manager.assigned_advices: 0
e_comm_finish_copy_manager.assigned_constants: 0

fold_finish_copy_manager.advice_equalities: 140206
fold_finish_copy_manager.constant_equalities: 70387
fold_finish_copy_manager.assigned_advices: 0
fold_finish_copy_manager.assigned_constants: 0

verify_accumulation_from_nark_copy_manager.advice_equalities: 140206
verify_accumulation_from_nark_copy_manager.constant_equalities: 70393
verify_accumulation_from_nark_copy_manager.assigned_advices: 0
verify_accumulation_from_nark_copy_manager.assigned_constants: 0

assign_default_accumulator_copy_manager.advice_equalities: 140206
assign_default_accumulator_copy_manager.constant_equalities: 70437
assign_default_accumulator_copy_manager.assigned_advices: 0
assign_default_accumulator_copy_manager.assigned_constants: 0

select_accumulator_copy_manager.advice_equalities: 140470
select_accumulator_copy_manager.constant_equalities: 70481
select_accumulator_copy_manager.assigned_advices: 0
select_accumulator_copy_manager.assigned_constants: 0
--check whats taking so many copy constraints in check_state_hash
check_state_hash_1_copy_manager.advice_equalities: 158128
check_state_hash_1_copy_manager.constant_equalities: 83035
check_state_hash_1_copy_manager.assigned_advices: 0
check_state_hash_1_copy_manager.assigned_constants: 0

check_state_hash_2_copy_manager.advice_equalities: 175780
check_state_hash_2_copy_manager.constant_equalities: 95587
check_state_hash_2_copy_manager.assigned_advices: 0
check_state_hash_2_copy_manager.assigned_constants: 0

before_synthesize_copy_manager.advice_equalities: 175780
before_synthesize_copy_manager.constant_equalities: 95587
before_synthesize_copy_manager.assigned_advices: 0
before_synthesize_copy_manager.assigned_constants: 0

after_synthesize_copy_manager.advice_equalities: 175780
after_synthesize_copy_manager.constant_equalities: 95587
after_synthesize_copy_manager.assigned_advices: 371902
after_synthesize_copy_manager.assigned_constants: 0

binding.borrow().statistics().gate_advice: [371902]
binding.borrow().statistics().gate_fixed: 918
binding.borrow().statistics().lookups: [1126, 0, 0]
Time for synthesize_accumulation_verifier: 426.85925ms


scalar_mul 

numbits 800 advice copies, 1.8k
270 multiple ec_double 17 advice copies, 40 advices
300 multiple ec_sub_unequal/add 28 copies, 60 advice
1 ec_sub_strict 60 copies 100 advice

num_to_bits_copy_manager.advice_equalities 37704
num_to_bits_copy_manager.constant_equalities 27268
num_to_bits_copy_manager.assigned_advices 0
k + window_bits = 5
multiple_ec_double_copy_manager.advice_equalities 37789
multiple_ec_double_copy_manager.constant_equalities 27335
multiple_ec_double_copy_manager.assigned_advices 0
ec_sub_unequal_copy_manager.advice_equalities 37817
ec_sub_unequal_copy_manager.constant_equalities 27354
ec_sub_unequal_copy_manager.assigned_advices 0
ec_sub_unequal_copy_manager.advice_equalities 38397
ec_sub_unequal_copy_manager.constant_equalities 27640
ec_sub_unequal_copy_manager.assigned_advices 0
rounded_bitlen = 264
multiple_ec_double_ec_add_unequal_copy_manager.advice_equalities 53973
multiple_ec_double_ec_add_unequal_copy_manager.constant_equalities 33844
multiple_ec_double_ec_add_unequal_copy_manager.assigned_advices 0
ec_sub_strict_copy_manager.advice_equalities 54030
ec_sub_strict_copy_manager.constant_equalities 33869
ec_sub_strict_copy_manager.assigned_advices 0
num_to_bits_copy_manager.advice_equalities 54825
num_to_bits_copy_manager.constant_equalities 34394
num_to_bits_copy_manager.assigned_advices 0


before_squeeze_challenge_copy_manager.advice_equalities 288
copy_manager.constant_equalities 415
copy_manager.assigned_constants 0
before_squeeze_challenge_copy_manager.assigned_advices 0
after_squeeze_challenge_copy_manager.advice_equalities 5945
copy_manager.constant_equalities 4514
copy_manager.assigned_constants 0
after_squeeze_challenge_copy_manager.assigned_advices 0
before_squeeze_challenge_copy_manager.advice_equalities 5968
copy_manager.constant_equalities 4538
copy_manager.assigned_constants 0
before_squeeze_challenge_copy_manager.assigned_advices 0
after_squeeze_challenge_copy_manager.advice_equalities 8448
copy_manager.constant_equalities 6330
copy_manager.assigned_constants 0
after_squeeze_challenge_copy_manager.assigned_advices 0
before_squeeze_challenge_copy_manager.advice_equalities 8494
copy_manager.constant_equalities 6373
copy_manager.assigned_constants 0
before_squeeze_challenge_copy_manager.assigned_advices 0
after_squeeze_challenge_copy_manager.advice_equalities 12561
copy_manager.constant_equalities 9317
copy_manager.assigned_constants 0
after_squeeze_challenge_copy_manager.assigned_advices 0
before_squeeze_challenge_copy_manager.advice_equalities 12584
copy_manager.constant_equalities 9341
copy_manager.assigned_constants 0
before_squeeze_challenge_copy_manager.assigned_advices 0
after_squeeze_challenge_copy_manager.advice_equalities 15064
copy_manager.constant_equalities 11133
copy_manager.assigned_constants 0
after_squeeze_challenge_copy_manager.assigned_advices 0
before_squeeze_challenge_copy_manager.advice_equalities 15197
copy_manager.constant_equalities 11355
copy_manager.assigned_constants 0
before_squeeze_challenge_copy_manager.assigned_advices 0
after_squeeze_challenge_copy_manager.advice_equalities 39923
copy_manager.constant_equalities 29303
copy_manager.assigned_constants 0
after_squeeze_challenge_copy_manager.assigned_advices 0
····Start:   fold_accumulator_from_nark witness_comms-5
before_scalar_mul_secondary_copy_manager.advice_equalities 40219
copy_manager.constant_equalities 29776
copy_manager.assigned_constants 0
before_scalar_mul_secondary_copy_manager.assigned_advices 0
before_scalar_mul_secondary_copy_manager.advice_equalities 48521
copy_manager.constant_equalities 33181
copy_manager.assigned_constants 0
before_scalar_mul_secondary_copy_manager.assigned_advices 0


before_squeeze_challenge_ctx.advice.len() 1245
after_squeeze_challenge_ctx.advice.len() 14778
before_squeeze_challenge_ctx.advice.len() 14840
after_squeeze_challenge_ctx.advice.len() 20792
before_squeeze_challenge_ctx.advice.len() 20911
after_squeeze_challenge_ctx.advice.len() 30649
before_squeeze_challenge_ctx.advice.len() 30711
after_squeeze_challenge_ctx.advice.len() 36663
before_squeeze_challenge_ctx.advice.len() 37326
after_squeeze_challenge_ctx.advice.len() 96366
squeeze_challenge = 95k

before_scalar_mul_secondary_ctx.advice.len() 97791
after_scalar_mul_secondary_ctx.advice.len() 113550
before_scalar_mul_secondary_ctx.advice.len() 113550
after_scalar_mul_secondary_ctx.advice.len() 129309
before_scalar_mul_secondary_ctx.advice.len() 129309
after_scalar_mul_secondary_ctx.advice.len() 145068
before_scalar_mul_secondary_ctx.advice.len() 145068
after_scalar_mul_secondary_ctx.advice.len() 160827
before_scalar_mul_secondary_ctx.advice.len() 160827
after_scalar_mul_secondary_ctx.advice.len() 176586
before_scalar_mul_secondary_ctx.advice.len() 181341
after_scalar_mul_secondary_ctx.advice.len() 197100
scalar_mul_secondary = 100k

before_hash_assigned_state_poseidon_ctx.advice.len() 204899
after_hash_assigned_state_poseidon_ctx.advice.len() 250402
after_hash_assigned_state_num_to_bits_ctx.advice.len() 252178
after_hash_assigned_state_bits_to_num_ctx.advice.len() 252926
before_hash_assigned_state_poseidon_ctx.advice.len() 252934
after_hash_assigned_state_poseidon_ctx.advice.len() 298437
after_hash_assigned_state_num_to_bits_ctx.advice.len() 300213
after_hash_assigned_state_bits_to_num_ctx.advice.len() 300961
hash_assigned_state = 96k

copy_manager.assigned_advices 300961
Constant adds constant_equalities and assigns new advice - 84k 
Existing adds advice_equalities and assigns new advice - 134k
Witness: assigns new advice -  85703
Witness_Fraction - witness_fraction 373

total_dedup_advice 60k


copy_manager.advice_equalities 134349
copy_manager.constant_equalities 83279
copy_manager.assigned_constants 0
copy_manager.assigned_advices 300961
total_advice 134048
total_fixed 901