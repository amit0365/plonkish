### IVC

#### 70 ECDSA signatures

takes 1.5s
cyclefold_circuit_advice_lookup [0, 0, 0]
cyclefold_circuit_copy_manager.advice_equalities 129785
cyclefold_circuit_copy_manager.constant_equalities 59592
cyclefold_circuit_copy_manager.assigned_advices 253699
Time for synthesize_ec: 242.216541ms

takes 5.4s
copy_manager.advice_equalities 356739
copy_manager.constant_equalities 330091
copy_manager.assigned_advices 1077380
Time for synthesize_accumulation_verifier: 1.259557375s

Time for prove_steps: 474.103030833s

primary_proof: 10976
Time for prove_decider: 6.535299166s
Start:   variable_base_msm-31
End:     variable_base_msm-31 ......................................................939.750µs
Start:   variable_base_msm-19
End:     variable_base_msm-19 ......................................................879.458µs
Time for verify_decider: 12.124417ms
test accumulation::protostar::ivc::halo2::test::gemini_kzg_ipa_protostar_hyperplonk_ivc ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 15 filtered out; finished in 495.17s


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



#### Cyclefold time

// todo without lookups  -- check this

// both lookups 1
--main lookups increase, maybe taking from avp check? or maybe coming from cyclefold nark ??

cyclefold_circuit_advice_lookup [0, 0, 0]
cyclefold_circuit_copy_manager.advice_equalities 67952
cyclefold_circuit_copy_manager.constant_equalities 33510
cyclefold_circuit_copy_manager.assigned_constants 0
cyclefold_circuit_copy_manager.assigned_advices 137797
··Start:   lookup_m_polys-1
··End:     lookup_m_polys-1


main_circuit_advice_lookup [2636, 0, 0]
copy_manager.advice_equalities 122037
copy_manager.constant_equalities 74856
copy_manager.assigned_constants 0
copy_manager.assigned_advices 273325


// cyclefold circuit with 0 num_lookups and main circuit with 1 

cyclefold_circuit_advice_lookup [0, 0, 0]

main_circuit_advice_lookup [2010, 0, 0]
copy_manager.advice_equalities 88185
copy_manager.constant_equalities 57643
copy_manager.assigned_constants 0
copy_manager.assigned_advices 203271


// both circuit 0 num_lookups

cyclefold_circuit_advice_lookup [0, 0, 0]

0 lookup columns still give some lookups? WTF CHECK THIS main_circuit_advice_lookup [1614, 0, 0]
copy_manager.advice_equalities 76821
copy_manager.constant_equalities 49106
copy_manager.assigned_constants 0
copy_manager.assigned_advices 175260

cyclefold_circuit_copy_manager.advice_equalities 34548
cyclefold_circuit_copy_manager.constant_equalities 17200
cyclefold_circuit_copy_manager.assigned_constants 0
cyclefold_circuit_copy_manager.assigned_advices 70420


// TODO CHECK MSM TIME WHEN ZERO, LOOKS LIKE IT DOUBLES NOW WITH OR WITHOUT ZEROS. even with 100k less constraints take same time

// save 7k if use 88, 3 for base_chip - needed to do base ops for acc_ec

cyclefold_circuit_copy_manager.advice_equalities 67952
cyclefold_circuit_copy_manager.constant_equalities 33510
cyclefold_circuit_copy_manager.assigned_constants 0
cyclefold_circuit_copy_manager.assigned_advices 137797

copy_manager.advice_equalities 122037
copy_manager.constant_equalities 74856
copy_manager.assigned_constants 0
copy_manager.assigned_advices 273325


// num limbs 2 for only primary_non-native - which only assigns witness, no computation -- saves 48k 

copy_manager.advice_equalities 125719
copy_manager.constant_equalities 77502
copy_manager.assigned_constants 0
copy_manager.assigned_advices 281956


// all i/o hashed as instances -- saves 100k instead of instances.len = 13

copy_manager.advice_equalities 145147
copy_manager.constant_equalities 91542
copy_manager.assigned_constants 0
copy_manager.assigned_advices 328108
Time for synthesize_accumulation_verifier: 266.264166ms

primary_proof: 7808
Time for prove_decider: 7.817340667s
Start:   variable_base_msm-13
End:     variable_base_msm-13 ......................................................842.709µs
Start:   variable_base_msm-20
End:     variable_base_msm-20 ......................................................902.333µs
Time for verify_decider: 14.784791ms
test accumulation::protostar::ivc::halo2::test::gemini_kzg_ipa_protostar_hyperplonk_ivc ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 14 filtered out; finished in 49.40s


// with assign_point unchecked -- saves 20k, 450k -> 430

// decider 
prove_decider-primary-19 ..................................................7.513s
primary_proof: 7808
Time for prove_decider: 7.513353542s
Start:   variable_base_msm-13
End:     variable_base_msm-13 ......................................................836.250µs
Start:   variable_base_msm-20
End:     variable_base_msm-20 ......................................................892.125µs
Time for verify_decider: 15.111833ms
test accumulation::protostar::ivc::halo2::test::gemini_kzg_ipa_protostar_hyperplonk_ivc ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 14 filtered out; finished in 51.05s



Start:   prove_accumulation_from_nark-primary-19
··Start:   witness_collector-0
before_acc_verifier.assign_accumulator_copy_manager.advice_equalities 31
copy_manager.constant_equalities 61
builder.advice.len() 184
after_acc_verifier.assign_accumulator_copy_manager.advice_equalities 175
copy_manager.constant_equalities 385
builder.advice.len() 1176
before_verify_acc_from_nark_copy_manager.advice_equalities 175
copy_manager.constant_equalities 390
builder.advice.len() 1181
num_witness_polys 5
num_challenges 4
num_cross_terms 3
after_squeeze_nark_copy_manager.advice_equalities 5855
copy_manager.constant_equalities 4538
builder.advice.len() 14875
after_squeeze_nark_copy_manager.advice_equalities 11534
copy_manager.constant_equalities 8686
builder.advice.len() 28565
after_squeeze_nark_copy_manager.advice_equalities 20415
copy_manager.constant_equalities 15196
builder.advice.len() 50003
after_squeeze_nark_copy_manager.advice_equalities 26094
copy_manager.constant_equalities 19344
builder.advice.len() 63693
before_nark_copy_manager.advice_equalities 26096
copy_manager.constant_equalities 19346
builder.advice.len() 63698
before_compress_copy_manager.advice_equalities 26096
copy_manager.constant_equalities 19346
builder.advice.len() 63698
before_squeeze_copy_manager.advice_equalities 26120
copy_manager.constant_equalities 19400
builder.advice.len() 63865
before_assign_cyclefold_copy_manager.advice_equalities 55609
copy_manager.constant_equalities 40802
builder.advice.len() 134267
after_check_cyclefold_copy_manager.advice_equalities 55753
copy_manager.constant_equalities 41126
builder.advice.len() 135251
instances_folded
challenges_folded
after_fold_acc_from_nark_copy_manager.advice_equalities 55791
copy_manager.constant_equalities 41144
builder.advice.len() 135326
after_acc_prime_copy_manager.advice_equalities 56199
copy_manager.constant_equalities 41280
builder.advice.len() 135938
cyclefold_avp.num_instances [13]
after_acc_ec_copy_manager.advice_equalities 56565
copy_manager.constant_equalities 41907
builder.advice.len() 137838
after_nark_copy_manager.advice_equalities 89121
copy_manager.constant_equalities 65904
builder.advice.len() 216764
before_squeeze_copy_manager.advice_equalities 89180
copy_manager.constant_equalities 66004
builder.advice.len() 217067
after_squeeze_copy_manager.advice_equalities 131397
copy_manager.constant_equalities 96668
builder.advice.len() 317896
····Start:   fold_accumulator_from_nark witness_comms-5
····End:     fold_accumulator_from_nark witness_comms-5 ............................18.072ms
witness_comms_folded
challenges_folded
r_nark.instances.len() 1
acc.instances.len() 1
acc_prime_instances_folded
acc_prime_witness_comms_folded
acc_prime_challenges_folded
····Start:   fold_accumulator_from_nark e_comm-cross_term_comms.len()-1
····End:     fold_accumulator_from_nark e_comm-cross_term_comms.len()-1 ............3.757ms
after_fold_ec_copy_manager.advice_equalities 184835
copy_manager.constant_equalities 122551
builder.advice.len() 428713
after_acc_ec_prime_copy_manager.advice_equalities 185477
copy_manager.constant_equalities 122765
copy_manager.assigned_constants 0
copy_manager.assigned_advices 0
copy_manager.advice_equalities 185477
copy_manager.constant_equalities 122765
copy_manager.assigned_constants 0
copy_manager.assigned_advices 429676
Time for synthesize_accumulation_verifier: 405.956375ms


with assign pt checked 

··Start:   witness_collector-0
before_acc_verifier.assign_accumulator_copy_manager.advice_equalities 31
copy_manager.constant_equalities 61
builder.advice.len() 184
after_acc_verifier.assign_accumulator_copy_manager.advice_equalities 1909
copy_manager.constant_equalities 2977
builder.advice.len() 8742
before_verify_acc_from_nark_copy_manager.advice_equalities 1909
copy_manager.constant_equalities 2982
builder.advice.len() 8747
num_witness_polys 5
num_challenges 4
num_cross_terms 3
after_squeeze_nark_copy_manager.advice_equalities 7878
copy_manager.constant_equalities 7562
builder.advice.len() 23702
after_squeeze_nark_copy_manager.advice_equalities 13846
copy_manager.constant_equalities 12142
builder.advice.len() 38653
after_squeeze_nark_copy_manager.advice_equalities 23305
copy_manager.constant_equalities 19516
builder.advice.len() 62613
after_squeeze_nark_copy_manager.advice_equalities 29273
copy_manager.constant_equalities 24096
builder.advice.len() 77564
before_nark_copy_manager.advice_equalities 29275
copy_manager.constant_equalities 24098
builder.advice.len() 77569
before_compress_copy_manager.advice_equalities 29275
copy_manager.constant_equalities 24098
builder.advice.len() 77569
before_squeeze_copy_manager.advice_equalities 29588
copy_manager.constant_equalities 24584
builder.advice.len() 78997
before_assign_cyclefold_copy_manager.advice_equalities 59077
copy_manager.constant_equalities 45986
builder.advice.len() 149399
after_check_cyclefold_copy_manager.advice_equalities 60955
copy_manager.constant_equalities 48902
builder.advice.len() 157949
instances_folded
challenges_folded
after_fold_acc_from_nark_copy_manager.advice_equalities 60993
copy_manager.constant_equalities 48920
builder.advice.len() 158024
after_acc_prime_copy_manager.advice_equalities 61401
copy_manager.constant_equalities 49056
builder.advice.len() 158636
cyclefold_avp.num_instances [13]
after_acc_ec_copy_manager.advice_equalities 61767
copy_manager.constant_equalities 49683
builder.advice.len() 160536
after_nark_copy_manager.advice_equalities 94323
copy_manager.constant_equalities 73680
builder.advice.len() 239462
before_squeeze_copy_manager.advice_equalities 94382
copy_manager.constant_equalities 73780
builder.advice.len() 239765
after_squeeze_copy_manager.advice_equalities 136599
copy_manager.constant_equalities 104444
builder.advice.len() 340594
····Start:   fold_accumulator_from_nark witness_comms-5
····End:     fold_accumulator_from_nark witness_comms-5 ............................16.674ms
witness_comms_folded
challenges_folded
r_nark.instances.len() 1
acc.instances.len() 1
acc_prime_instances_folded
acc_prime_witness_comms_folded
acc_prime_challenges_folded
····Start:   fold_accumulator_from_nark e_comm-cross_term_comms.len()-1
····End:     fold_accumulator_from_nark e_comm-cross_term_comms.len()-1 ............3.481ms
after_fold_ec_copy_manager.advice_equalities 190037
copy_manager.constant_equalities 130327
builder.advice.len() 451411
after_acc_ec_prime_copy_manager.advice_equalities 190679
copy_manager.constant_equalities 130541
copy_manager.assigned_constants 0
copy_manager.assigned_advices 0
copy_manager.advice_equalities 190679
copy_manager.constant_equalities 130541
copy_manager.assigned_constants 0
copy_manager.assigned_advices 452374
Time for synthesize_accumulation_verifier: 381.016666ms


instance len 40

cyclefold_circuit_copy_manager.advice_equalities 51065
cyclefold_circuit_copy_manager.constant_equalities 21239
cyclefold_circuit_copy_manager.assigned_constants 0
cyclefold_circuit_copy_manager.assigned_advices 97439
Time for synthesize_ec: 59.065667ms

before_acc_verifier.assign_accumulator_copy_manager.advice_equalities 7
after_acc_verifier.assign_accumulator_copy_manager.advice_equalities 1885
before_verify_acc_from_nark_copy_manager.advice_equalities 1885
num_witness_polys 5
num_challenges 4
num_cross_terms 3
after_squeeze_nark_copy_manager.advice_equalities 7854
after_squeeze_nark_copy_manager.advice_equalities 13822
after_squeeze_nark_copy_manager.advice_equalities 23281
after_squeeze_nark_copy_manager.advice_equalities 29249
before_nark_copy_manager.advice_equalities 29251
before_compress_copy_manager.advice_equalities 29251
before_squeeze_copy_manager.advice_equalities 29564
before_assign_cyclefold_copy_manager.advice_equalities 59053
r_constrained
nark_witness_comms_constrained
cross_term_comms_constrained
acc_e_comm_constrained
acc_witness_comms_constrained
after_check_cyclefold_copy_manager.advice_equalities 64800
instances_folded
challenges_folded
after_fold_acc_from_nark_copy_manager.advice_equalities 64838
after_acc_prime_copy_manager.advice_equalities 65246
after_nark_copy_manager.advice_equalities 141719
before_squeeze_copy_manager.advice_equalities 141778
after_squeeze_copy_manager.advice_equalities 226898
······Start:   fold_accumulator_from_nark witness_comms-5
······End:     fold_accumulator_from_nark witness_comms-5 ..........................17.142ms
witness_comms_folded
challenges_folded
acc_prime_instances_folded
acc_prime_witness_comms_folded
acc_prime_challenges_folded
······Start:   fold_accumulator_from_nark e_comm-cross_term_comms.len()-1
······End:     fold_accumulator_from_nark e_comm-cross_term_comms.len()-1 ..........3.545ms
after_fold_ec_copy_manager.advice_equalities 284008
after_acc_ec_prime_copy_manager.advice_equalities 285460
copy_manager.constant_equalities 207024
copy_manager.assigned_constants 0
copy_manager.assigned_advices 0
copy_manager.advice_equalities 285460
copy_manager.constant_equalities 207024
copy_manager.assigned_constants 0
copy_manager.assigned_advices 699086
Time for synthesize_accumulation_verifier: 610.489709ms


### Without Cyclefold time
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