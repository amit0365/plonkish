| Hierarchy                           | Operation                                | Number | Average Time   |
|-------------------------------------|------------------------------------------|--------|----------------|
| prove_accumulation_from_nark-secondary-14 |                                          |        |                |
| ------------------------------------|------------------------------------------|--------|----------------|
|                                     | witness_collector-0                      |        |                |
|                                     |   - witness_collector-0                  |        | ~50.939 ms     |
|                                     | variable_base_msm-16384                  | 16384  | ~5.315 ms     |
|                                     |   - variable_base_msm-16384              | 16384  | ~5.315 ms     |
|                                     |   - variable_base_msm-16384              | 16384  | ~5.315 ms     |
|                                     |   - ... (repeated instances)             |        |                |
|                                     | lookup_compressed_polys-1                | 1      | ~0.990 ms     |
|                                     |   - compressed_input_poly                | -      | ~0.533 ms     |
|                                     |   - compressed_table_poly                | -      | ~0.306 ms     |
|                                     | lookup_m_polys-1                         | 1      | ~0.833 ms     |
|                                     | lookup_h_polys-1                         | 1      | ~1.248 ms     |
|                                     | powers_of_zeta_poly                      | -      | ~0.617 ms     |
|                                     | evaluate_zeta_cross_term_poly            | -      | ~0.439 ms     |
|                                     | evaluate_compressed_cross_term_sums-3    | 3      | ~25.946 ms    |
|                                     | fold_compressed                          | -      | ~6.830 ms     |
| ------------------------------------|------------------------------------------|--------|----------------|
| prove_accumulation_from_nark-primary-14   |                                          |        |                |
| ------------------------------------|------------------------------------------|--------|----------------|
|                                     | witness_collector-0                      |        |                |
|                                     |   - witness_collector-0                  |        | ~50.960 ms     |
|                                     | variable_base_msm-16384                  | 16384  | ~5.464 ms     |
|                                     |   - variable_base_msm-16384              | 16384  | ~5.464 ms     |
|                                     |   - variable_base_msm-16384              | 16384  | ~5.464 ms     |
|                                     |   - ... (repeated instances)             |        |                |
|                                     | lookup_compressed_polys-1                | 1      | ~0.928 ms     |
|                                     |   - compressed_input_poly                | -      | ~0.421 ms     |
|                                     |   - compressed_table_poly                | -      | ~0.309 ms     |
|                                     | lookup_m_polys-1                         | 1      | ~0.753 ms     |
|                                     | lookup_h_polys-1                         | 1      | ~1.231 ms     |
|                                     | powers_of_zeta_poly                      | -      | ~0.601 ms     |
|                                     | evaluate_zeta_cross_term_poly            | -      | ~0.429 ms     |
|                                     | evaluate_compressed_cross_term_sums-3    | 3      | ~44.197 ms    |
|                                     | fold_compressed                          | -      | ~7.133 ms     |
| ------------------------------------|------------------------------------------|--------|----------------|
| prove_accumulation_from_nark-secondary-14 |                                          |        |                |
| ------------------------------------|------------------------------------------|--------|----------------|
|                                     | witness_collector-0                      |        |                |
|                                     |   - witness_collector-0                  |        | ~50.680 ms     |
|                                     | variable_base_msm-16384                  | 16384  | ~5.605 ms     |
|                                     |   - variable_base_msm-16384              | 16384  | ~5.605 ms     |
|                                     |   - variable_base_msm-16384              | 16384  | ~5.605 ms     |
|                                     |   - ... (repeated instances)             |        |                |
|                                     | lookup_compressed_polys-1                | 1      | ~0.829 ms     |
|                                     |   - compressed_input_poly                | -      | ~0.394 ms     |
|                                     |   - compressed_table_poly                | -      | ~0.253 ms     |
|                                     | lookup_m_polys-1                         | 1      | ~0.908 ms     |
|                                     | lookup_h_polys-1                         | 1      | ~1.151 ms     |
|                                     | powers_of_zeta_poly                      | -      | ~0.628 ms     |
|                                     | evaluate_zeta_cross_term_poly            | -      | ~0.505 ms     |
|                                     | evaluate_compressed_cross_term_sums-3    | 3      | ~49.827 ms    |
|                                     | fold_compressed                          | -      | ~6.840 ms     |
| ------------------------------------|------------------------------------------|--------|----------------|
| prove_accumulation_from_nark-primary-14   |                                          |        |                |
| ------------------------------------|------------------------------------------|--------|----------------|
|                                     | witness_collector-0                      |        |                |
|                                     |   - witness_collector-0                  |        | ~50.043 ms     |
|                                     | variable_base_msm-16384                  | 16384  | ~5.252 ms     |
|                                     |   - variable_base_msm-16384              | 16384  | ~5.252 ms     |
|                                     |   - variable_base_msm-16384              | 16384  | ~5.252 ms     |
|                                     |   - ... (repeated instances)             |        |                |
|                                     | lookup_compressed_polys-1                | 1      | ~0.829 ms     |
|                                     |   - compressed_input_poly                | -      | ~0.394 ms     |
|                                     |   - compressed_table_poly                | -      | ~0.253 ms     |
|                                     | lookup_m_polys-1                         | 1      | ~0.742 ms     |
|                                     | lookup_h_polys-1                         | 1      | ~1.231 ms     |
|                                     | powers_of_zeta_poly                      | -      | ~0.628 ms     |
|                                     | evaluate_zeta_cross_term_poly            | -      | ~0.505 ms     |
|                                     | evaluate_compressed_cross_term_sums-3    | 3      | ~49.827 ms    |
|                                     | fold_compressed                          | -      | ~6.840 ms     |
| ------------------------------------|------------------------------------------|--------|----------------|
| Hierarchy                                           | Operation                              | Number | Average Time   |
|-----------------------------------------------------|----------------------------------------|--------|----------------|
| prove_decider-primary-14                            |                                        |        |                |
|  - permutation_z_polys-8                            |                                        |        |                |
|    - products                                      |                                        |        |                |
|      - products ....................................|......................................|......  | ~4.859 ms      |
|    - z_polys                                       |                                        |        |                |
|      - z_polys .....................................|......................................|......  | ~1.685 ms      |
|    - into_bh_order                                |                                        |        |                |
|      - into_bh_order ..............................|......................................|......  | ~244.709 µs    |
|    - variable_base_msm-16384                      | 16384                                  | 16384  | ~22.606 ms    |
|    - variable_base_msm-16384                      | 16384                                  | 16384  | ~21.442 ms    |
|    - variable_base_msm-16384                      | 16384                                  | 16384  | ~22.395 ms    |
|  - sum_check_prove-14-5                            |                                        |        |                |
|    - sum_check_prove_round-0                      |                                        |        |                |
|      - sum_check_prove_round-0 ....................|......................................|......  | ~34.409 ms     |
|    - sum_check_next_round-0                       |                                        |        |                |
|      - sum_check_next_round-0 .....................|......................................|......  | ~6.475 ms      |
|    - sum_check_prove_round-1                      |                                        |        |                |
|      - sum_check_prove_round-1 ....................|......................................|......  | ~18.348 ms     |
|    - sum_check_next_round-1                       |                                        |        |                |
|      - sum_check_next_round-1 .....................|......................................|......  | ~2.281 ms      |
|    - ... (repeated instances)                      |                                        |        |                |
|    - evals-43                                     |                                        |        |                |
|      - evals-43 ...................................|......................................|......  | ~545.083 µs    |
|    - pcs_batch_open-46                            |                                        |        |                |
|      - merged_polys                               |                                        |        |                |
|        - merged_polys .............................|......................................|......  | ~6.738 ms      |
|      - sum_check_prove-14-2                       |                                        |        |                |
|        - sum_check_prove_round-0                  |                                        |        |                |
|          - sum_check_prove_round-0 ...............|......................................|......  | ~527.667 µs    |
|        - sum_check_next_round-0                   |                                        |        |                |
|          - sum_check_next_round-0 ................|......................................|......  | ~647.583 µs    |
|        - ... (repeated instances)                  |                                        |        |                |
|      - g_prime                                    |                                        |        |                |
|        - g_prime ..................................|......................................|......  | ~515.125 µs    |
|      - variable_base_msm-46                       |                                        |        |                |
|        - variable_base_msm-46 ....................|......................................|......  | ~1.051 ms      |
|      - variable_base_msm-16384                    |                                        |        |                |
|        - variable_base_msm-16384 .................|......................................|......  | ~49.826 ms     |
|      - variable_base_msm-8192                     |                                        |        |                |
|        - variable_base_msm-8192 ..................|......................................|......  | ~30.300 ms     |
|      - ... (repeated instances)                    |                                        |        |                |
|      - variable_base_msm-16382                    |                                        |        |                |
|        - variable_base_msm-16382 .................|......................................|......  | ~47.741 ms     |
| Hierarchy                                       | Operation                               | Number | Average Time  |
|-----------------------------------------------  |-----------------------------------------|--------|-------------- |
| prove_decider_with_last_nark-secondary-14       |                                         |        |              |
|                                                | witness_collector-0                     |        |              |
|                                                |   - witness_collector-0                 |        | ~52.820 ms   |
|                                                | variable_base_msm-16384                 |        |              |
|                                                |   - variable_base_msm-16384             |        | ~5.233 ms    |
|                                                |   - ... (repeated instances)            |        |              |
|                                                | lookup_compressed_polys-1               |        |              |
|                                                |   - compressed_input_poly               |        |              |
|                                                |     - compressed_input_poly             |        | ~364.458 µs  |
|                                                |   - ... (repeated instances)            |        |              |
|                                                | lookup_m_polys-1                        |        |              |
|                                                |   - lookup_m_polys-1                    |        | ~838.625 µs  |
|                                                |   - ... (repeated instances)            |        |              |
|                                                | powers_of_zeta_poly                     |        |              |
|                                                |   - powers_of_zeta_poly                 |        | ~631.000 µs  |
|                                                |   - ... (repeated instances)            |        |              |
|                                                | evaluate_compressed_cross_term_sums-3   |        |              |
|                                                |   - evaluate_compressed_cross_term_sums-3 |      | ~48.887 ms  |
|                                                |   - ... (repeated instances)            |        |              |
|                                                | evaluate_zeta_cross_term_poly           |        |              |
|                                                |   - evaluate_zeta_cross_term_poly       |        | ~411.458 µs  |
|                                                |   - ... (repeated instances)            |        |              |
|                                                | variable_base_msm-16384                 |        |              |
|                                                |   - variable_base_msm-16384             |        | ~4.236 ms    |
|                                                |   - ... (repeated instances)            |        |              |

