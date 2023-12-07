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



#### Han incomplete impl

10 steps, no compressing

Time for preprocess: 1.995075083s
Time for prove_steps: 5.060839917s
Time for prove_decider: 1.908527459s






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
5 scal_mul_secondary here take 90k advice and 37k constant eq
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