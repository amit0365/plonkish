use core::num;
use std::{
    iter::zip, marker::PhantomData, ops::{AddAssign, Range}, time::Instant
};

use crate::{accumulation::protostar::{hyperplonk::prover::powers_of_zeta_poly, ProtostarAccumulator}, backend::hyperplonk::prover::instance_polys, pcs::PolynomialCommitmentScheme, poly::multilinear::MultilinearPolynomial, util::{arithmetic::{div_ceil, field_integers, powers, BooleanHypercube, Field}, end_timer, expression::Rotation, expression_new::constraints::LookupData, izip, izip_eq, parallel::{num_threads, par_map_collect, parallelize_iter}, start_timer, Deserialize, Itertools, Serialize}};
use ark_std::{end_timer, start_timer};
use halo2_base::{halo2_proofs::{arithmetic::lagrange_interpolate, plonk}, utils::PrimeField};
pub use halo2_proofs::halo2curves::CurveAffine;
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator};
use rayon::iter::IndexedParallelIterator;
use rayon::iter::ParallelIterator;
use super::{constraints::Data, IndexedExpression, QueriedExpression, QueryType};
//use halo2curves::CurveAffine;
// use crate::{
//     arithmetic::{field_integers, lagrange_interpolate},
//     protostar::{accumulator::Accumulator, ProvingKey},
// };



/// Defines a QueriedExpression where leaves are references values from two accumulators.
pub struct Paired<'a, F> {
    _marker: PhantomData<&'a F>,
}

impl<'a, F: Field> QueryType for Paired<'a, F> {
    type F = F;
    type Challenge = [&'a F; 2];
    type Fixed = &'a MultilinearPolynomial<F>;
    type Witness = [&'a MultilinearPolynomial<F>; 2];
}

impl<'a, F: PrimeField> Paired<'a, F> {
    /// Create a `Data` object from two accumulators, where each variable contains a pair of references to the
    /// some column from two different accumulators. This allows us to create a QueriedExpression where the leaves
    /// contain these two references.
    pub fn new_data<Pcs>(
        num_vars: usize,
        num_fixed: usize,
        lookups_empty: bool,
        num_witness_polys: usize,
        num_challenges: usize,
        num_theta_primes: usize,
        num_alpha_primes: usize,
        preprocess_polys: &'a [MultilinearPolynomial<F>],
        beta: [&'a MultilinearPolynomial<F>; 2],
        acc0: &'a ProtostarAccumulator<F, Pcs>,
        acc1: &'a ProtostarAccumulator<F, Pcs>,
    ) -> Data<Self>
    where
        Pcs: PolynomialCommitmentScheme<F, Polynomial = MultilinearPolynomial<F>>,
    {
        let fixed = preprocess_polys[..num_fixed].iter().collect();
        let selectors = preprocess_polys[num_fixed..].iter().collect();
        let instance = zip(&acc0.instance_polys, &acc1.instance_polys)
            .map(|(a0, a1)| [a0, a1])
            .collect_vec();

        let total_advice = zip(&acc0.witness_polys, &acc1.witness_polys)
            .map(|(a0, a1)| [a0, a1])
            .collect_vec();

        let total_challenges = zip(&acc0.instance.challenges, &acc1.instance.challenges)
            .map(|(c0, c1)| [c0, c1])
            .collect_vec();

        let advice= total_advice.iter().take(num_witness_polys).cloned().collect_vec();
        let challenges = total_challenges.iter().take(num_challenges).cloned().collect_vec();
        let thetas = total_challenges.iter().skip(num_challenges).take(num_theta_primes).cloned().collect_vec();
        let r = total_challenges.iter().skip(num_challenges + num_theta_primes).take(1).cloned().collect_vec()[0]; // beta_prime 
        let ys = total_challenges.iter().rev().take(num_alpha_primes).cloned().rev().collect_vec();

        let lookups = if lookups_empty {
            Vec::new()
        } else { 
            let lookups_polys = total_advice[num_witness_polys..num_witness_polys + 3].to_vec();
            vec![LookupData::new(lookups_polys, thetas, r)]
        };

        Data::<Self> {
            fixed,
            selectors,
            instance,
            advice,
            challenges,
            beta,
            lookups,
            ys,
        }
    }

    /// Given an expression G where the variables are the linear polynomials interpolating between
    /// the challenges and witness columns from two accumulators,
    /// return the polynomial e(X) = ∑ᵢ βᵢ(X) G(fᵢ, wᵢ(X), rᵢ(X)).
    ///
    /// The strategy for evaluating e(X) is as follows:
    /// - Let D = {0,1,...,d} be the evaluation domain containing the first d + 1 integers, where d is the degree of e(X).
    /// - For each row i, we evaluate the expression eᵢ(X) = βᵢ(X) G(fᵢ, wᵢ(X), rᵢ(X)) over D,
    ///   and add it to the running sum for e(D) = ∑ᵢ eᵢ(D).
    ///   - The input variables βᵢ(X), wᵢ(X), rᵢ(X) are linear polynomials of the form pᵢ(X) = (1−X)⋅pᵢ,₀ + X⋅pᵢ,₁,
    ///     where pᵢ,₀ and pᵢ,₁ are values at the same position but from two different accumulators.
    ///   - For each variable fᵢ, compute fᵢ(D) by setting
    ///     - pᵢ(0) = pᵢ,₀
    ///     - pᵢ(1) = pᵢ,₁
    ///     - pᵢ(j) = pᵢ(j-1) + (pᵢ,₁ − pᵢ,₀) for j = 2, ..., d.
    ///   - Since challenge variables are the same for each row, we compute the evaluations only once.
    /// - Given the Expression for e(X), we evaluate it point-wise as eᵢ(j) = βᵢ(j) G(fᵢ, wᵢ(j), rᵢ(j)) for j in D.
    ///
    /// TODO: As an optimization, we can get away with evaluating the polynomial only at the points 2,...,d,
    /// since e(0) and e(1) are the existing errors from both accumulators. If we let D' = D \ {0,1}, then we can compute
    /// e(D') and reinsert the evaluations at 0 and 1 for the final result before the conversion to coefficients.
    pub fn evaluate_compressed_polynomial_allrows(
        expr: QueriedExpression<Self>,
        rows: Vec<usize>,
        num_vars: usize,
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);

        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective challenge, c₀, c₁,
        // compute the evaluations of the polynomial c(X) = (1−X)⋅c₀ + X⋅c₁
        let challenges: Vec<_> = indexed
            .challenges
            .iter()
            .map(|queried_challenge| {
                EvaluatedError::new_from_boolean_evals(
                    *queried_challenge.value[0],
                    *queried_challenge.value[1],
                    num_evals,
                )
            })
            .collect();

        // For each variable of the expression, we allocate buffers for storing their evaluations at each row.
        // - Fixed variables are considered as constants, so we only need to fetch the value from the proving key
        //   and consider fᵢ(j) = fᵢ for all j
        // - Witness variables are interpolated from the values at the two accumulators,
        //   and the evaluations are stored in a buffer.
        let mut fixed = vec![F::ZERO; indexed.fixed.len()];
        let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let mut sum = EvaluatedError::<F>::new(num_evals);
       
        for row_index in rows {
            // Fetch fixed data
            for (fixed, query) in fixed.iter_mut().zip(indexed.fixed.iter()) {
                let row_idx = query.row_idx(row_index, num_vars);
                *fixed = query.column[row_idx];
            }

            // Fetch witness data and interpolate
            for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
                let row_idx = query.row_idx(row_index, num_vars);
                let eval0 = query.column[0][row_idx];
                let eval1 = query.column[1][row_idx];
                witness.evaluate(eval0, eval1);
            }

            // Evaluate the expression in the current row and add it to e(D)
            for (eval_idx, eval) in sum.evals.iter_mut().enumerate() {
                // For each `eval_idx` j = 0, 1, ..., d, evaluate the expression eᵢ(j) = βᵢ(j) G(fᵢ, wᵢ(j), rᵢ(j))
                *eval += indexed.expr.evaluate(
                    &|&constant| constant,
                    &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                    &|&fixed_idx| fixed[fixed_idx],
                    &|&witness_idx| witness[witness_idx].evals[eval_idx],
                    &|&negated| -negated,
                    &|a, b| a + b,
                    &|a, b| a * b,
                );
            }
        };
        // Convert the evaluations into the coefficients of the polynomial
        sum.to_coefficients()
    }

    pub fn evaluate_compressed_polynomial_allrows_parallel_optimized(
        expr: QueriedExpression<Self>,
        rows: Vec<usize>,
        num_vars: usize,
    ) -> Vec<F> {
        use rayon::prelude::*;

        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
        let num_evals = indexed.expr.degree() + 1;

        let challenges: Vec<_> = indexed
            .challenges
            .iter()
            .map(|queried_challenge| {
                EvaluatedError::new_from_boolean_evals(
                    *queried_challenge.value[0],
                    *queried_challenge.value[1],
                    num_evals,
                )
            })
            .collect();

        let chunk_size = std::cmp::max(1, rows.len() / rayon::current_num_threads());
        let last_row = rows.iter().max().unwrap_or(&0).clone();
        let sum: EvaluatedError<F> = rows.par_chunks(chunk_size)
            .map(|chunk| {
                let mut chunk_sum = EvaluatedError::<F>::new(num_evals);
                let mut fixed = vec![F::ZERO; indexed.fixed.len()];
                let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

                for &row_index in chunk {
                    for (fixed, query) in fixed.iter_mut().zip(indexed.fixed.iter()) {
                        let row_idx = query.row_idx_last_row(row_index, last_row);
                        *fixed = query.column[row_idx];
                    }

                    for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
                        let row_idx = query.row_idx_last_row(row_index, last_row);
                        let eval0 = query.column[0][row_idx];
                        let eval1 = query.column[1][row_idx];
                        witness.evaluate(eval0, eval1);
                    }

                    for eval_idx in 0..num_evals {
                        chunk_sum.evals[eval_idx] += indexed.expr.evaluate(
                            &|&constant| constant,
                            &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                            &|&fixed_idx| fixed[fixed_idx],
                            &|&witness_idx| witness[witness_idx].evals[eval_idx],
                            &|&negated| -negated,
                            &|a, b| a + b,
                            &|a, b| a * b,
                        );
                    }
                }
                chunk_sum
            })
            .reduce(|| EvaluatedError::<F>::new(num_evals), |a, b| {
                let mut result = EvaluatedError::<F>::new(num_evals);
                for i in 0..num_evals {
                    result.evals[i] = a.evals[i] + b.evals[i];
                }
                result
            });

        sum.to_coefficients()
    }

    pub fn evaluate_compressed_polynomial_allrows_parallel(
        expr: QueriedExpression<Self>,
        rows: Vec<usize>,
        num_vars: usize,
    ) -> Vec<F> {
        use rayon::prelude::*;

        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
        let num_evals = indexed.expr.degree() + 1;

        let challenges: Vec<_> = indexed
            .challenges
            .iter()
            .map(|queried_challenge| {
                EvaluatedError::new_from_boolean_evals(
                    *queried_challenge.value[0],
                    *queried_challenge.value[1],
                    num_evals,
                )
            })
            .collect();

        let sum: EvaluatedError<F> = rows.into_par_iter().map(|row_index| {
            let mut fixed = vec![F::ZERO; indexed.fixed.len()];
            let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

            for (fixed, query) in fixed.iter_mut().zip(indexed.fixed.iter()) {
                let row_idx = query.row_idx(row_index, num_vars);
                *fixed = query.column[row_idx];
            }

            for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
                let row_idx = query.row_idx(row_index, num_vars);
                let eval0 = query.column[0][row_idx];
                let eval1 = query.column[1][row_idx];
                witness.evaluate(eval0, eval1);
            }

            let mut row_sum = EvaluatedError::<F>::new(num_evals);
            for eval_idx in 0..num_evals {
                row_sum.evals[eval_idx] = indexed.expr.evaluate(
                    &|&constant| constant,
                    &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                    &|&fixed_idx| fixed[fixed_idx],
                    &|&witness_idx| witness[witness_idx].evals[eval_idx],
                    &|&negated| -negated,
                    &|a, b| a + b,
                    &|a, b| a * b,
                );
            }
            row_sum
        }).reduce(|| EvaluatedError::<F>::new(num_evals), |a, b| {
            let mut result = EvaluatedError::<F>::new(num_evals);
            for i in 0..num_evals {
                result.evals[i] = a.evals[i] + b.evals[i];
            }
            result
        });

        sum.to_coefficients()
    }

    pub fn evaluate_compressed_polynomial_rowwise(
        expr: QueriedExpression<Self>,
        row_index: usize,
        num_vars: usize,
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);

        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective challenge, c₀, c₁,
        // compute the evaluations of the polynomial c(X) = (1−X)⋅c₀ + X⋅c₁
        let challenges: Vec<_> = indexed
            .challenges
            .iter()
            .map(|queried_challenge| {
                EvaluatedError::new_from_boolean_evals(
                    *queried_challenge.value[0],
                    *queried_challenge.value[1],
                    num_evals,
                )
            })
            .collect();

        // For each variable of the expression, we allocate buffers for storing their evaluations at each row.
        // - Fixed variables are considered as constants, so we only need to fetch the value from the proving key
        //   and consider fᵢ(j) = fᵢ for all j
        // - Witness variables are interpolated from the values at the two accumulators,
        //   and the evaluations are stored in a buffer.
        let mut fixed = vec![F::ZERO; indexed.fixed.len()];
        let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let mut sum = EvaluatedError::<F>::new(num_evals);
       
            // Fetch fixed data
            for (fixed, query) in fixed.iter_mut().zip(indexed.fixed.iter()) {
                let row_idx = query.row_idx(row_index, num_vars);
                *fixed = query.column[row_idx];
            }

            // Fetch witness data and interpolate
            for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
                let row_idx = query.row_idx(row_index, num_vars);
                let eval0 = query.column[0][row_idx];
                let eval1 = query.column[1][row_idx];
                witness.evaluate(eval0, eval1);
            }

            // Evaluate the expression in the current row and add it to e(D)
            for (eval_idx, eval) in sum.evals.iter_mut().enumerate() {
                // For each `eval_idx` j = 0, 1, ..., d, evaluate the expression eᵢ(j) = βᵢ(j) G(fᵢ, wᵢ(j), rᵢ(j))
                *eval += indexed.expr.evaluate(
                    &|&constant| constant,
                    &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                    &|&fixed_idx| fixed[fixed_idx],
                    &|&witness_idx| witness[witness_idx].evals[eval_idx],
                    &|&negated| -negated,
                    &|a, b| a + b,
                    &|a, b| a * b,
                );
            };

        // Convert the evaluations into the coefficients of the polynomial
        sum.to_coefficients()
    }

    pub fn evaluate_compressed_polynomial(
        expr: QueriedExpression<Self>,
        rows: Range<usize>,
        num_vars: usize,
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);

        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective challenge, c₀, c₁,
        // compute the evaluations of the polynomial c(X) = (1−X)⋅c₀ + X⋅c₁
        let challenges: Vec<_> = indexed
            .challenges
            .iter()
            .map(|queried_challenge| {
                EvaluatedError::new_from_boolean_evals(
                    *queried_challenge.value[0],
                    *queried_challenge.value[1],
                    num_evals,
                )
            })
            .collect();

        // For each variable of the expression, we allocate buffers for storing their evaluations at each row.
        // - Fixed variables are considered as constants, so we only need to fetch the value from the proving key
        //   and consider fᵢ(j) = fᵢ for all j
        // - Witness variables are interpolated from the values at the two accumulators,
        //   and the evaluations are stored in a buffer.
        let mut fixed = vec![F::ZERO; indexed.fixed.len()];
        let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let mut sum = EvaluatedError::<F>::new(num_evals);
       
        for row_index in rows {
            // Fetch fixed data
            for (fixed, query) in fixed.iter_mut().zip(indexed.fixed.iter()) {
                let row_idx = query.row_idx(row_index, num_vars);
                *fixed = query.column[row_idx];
            }

            // Fetch witness data and interpolate
            for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
                let row_idx = query.row_idx(row_index, num_vars);
                let eval0 = query.column[0][row_idx];
                let eval1 = query.column[1][row_idx];
                witness.evaluate(eval0, eval1);
            }

            // Evaluate the expression in the current row and add it to e(D)
            for (eval_idx, eval) in sum.evals.iter_mut().enumerate() {
                // For each `eval_idx` j = 0, 1, ..., d, evaluate the expression eᵢ(j) = βᵢ(j) G(fᵢ, wᵢ(j), rᵢ(j))
                *eval += indexed.expr.evaluate(
                    &|&constant| constant,
                    &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                    &|&fixed_idx| fixed[fixed_idx],
                    &|&witness_idx| witness[witness_idx].evals[eval_idx],
                    &|&negated| -negated,
                    &|a, b| a + b,
                    &|a, b| a * b,
                );
            }
        };
        // Convert the evaluations into the coefficients of the polynomial
        sum.to_coefficients()
    }

    pub fn evaluate_compressed_polynomial_par(
        expr: QueriedExpression<Self>,
        rows: Range<usize>,
        num_vars: usize,
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);

        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective challenge, c₀, c₁,
        // compute the evaluations of the polynomial c(X) = (1−X)⋅c₀ + X⋅c₁
        let challenges: Vec<_> = indexed
            .challenges
            .iter()
            .map(|queried_challenge| {
                EvaluatedError::new_from_boolean_evals(
                    *queried_challenge.value[0],
                    *queried_challenge.value[1],
                    num_evals,
                )
            })
            .collect();

        // For each variable of the expression, we allocate buffers for storing their evaluations at each row.
        // - Fixed variables are considered as constants, so we only need to fetch the value from the proving key
        //   and consider fᵢ(j) = fᵢ for all j
        // - Witness variables are interpolated from the values at the two accumulators,
        //   and the evaluations are stored in a buffer.
        let mut fixed = vec![F::ZERO; indexed.fixed.len()];
        let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let mut sum = EvaluatedError::<F>::new(num_evals);

        // let (updated_fixed, updated_witness): (Vec<F>, Vec<F>) = rows.into_par_iter()
        //     .flat_map(|row_index| {
        //         indexed.fixed.par_iter().zip(indexed.witness.par_iter())
        //             .map(move |(fixed_query, witness_query)| {
        //                 // Update fixed
        //                 let fixed_row_idx = fixed_query.row_idx(row_index, num_vars);
        //                 let updated_fixed_element = fixed_query.column[fixed_row_idx]; // Assuming direct assignment for simplicity

        //                 // Update witness
        //                 let witness_row_idx = witness_query.row_idx(row_index, num_vars);
        //                 let eval0 = witness_query.column[0][witness_row_idx]; // Assuming witness_query.column is a Vec<Vec<F>>
        //                 let eval1 = witness_query.column[1][witness_row_idx];
        //                 let updated_witness_element = witness_element.evaluate(eval0, eval1);

        //                 (updated_fixed_element, updated_witness_element)
        //             })
        //     })
        //     .unzip(); 

        // let updates: Vec<F> = rows.into_par_iter()
        // .flat_map(|row_index| {
        //     indexed.fixed.par_iter().map(move |query| {
        //         let row_idx = query.row_idx(row_index, num_vars);
        //         query.column[row_idx]
        //     })
        // })
        // .collect();
    
        // Apply updates to `fixed`. Since both `fixed` and `updates` are flat and of the same structure,
        // this operation can be performed directly.
        // fixed.iter_mut().zip(updates.into_iter()).for_each(|(fixed_element, update)| {
        //     *fixed_element = update;
        // });

        // rows.into_par_iter().for_each(|row_index| {
        // // for row_index in rows {
        //     // Fetch fixed data
        //     fixed.iter_mut().enumerate().for_each(|(i, fixed_element)| {
        //         if let Some(query) = indexed.fixed.get(i) {
        //             let row_idx = query.row_idx(row_index, num_vars);
        //             *fixed_element = query.column[row_idx];
        //         }
        //     });

        //     // Fetch witness data and interpolate
        //     witness.iter_mut().enumerate().for_each(|(i, witness_element)| {
        //         if let Some(query) = indexed.witness.get(i) {
        //             let row_idx = query.row_idx(row_index, num_vars);
        //             let eval0 = query.column[0][row_idx];
        //             let eval1 = query.column[1][row_idx];
        //             witness_element.evaluate(eval0, eval1);
        //         }
        //     });

        //     sum.evals.iter_mut().enumerate().for_each(|(eval_idx, eval)| {
        //         *eval += indexed.expr.evaluate(
        //             &|&constant| constant,
        //             &|&challenge_idx| challenges[challenge_idx].evals[eval_idx], // Ensure thread-safe read
        //             &|&fixed_idx| fixed[fixed_idx], // Ensure thread-safe read
        //             &|&witness_idx| witness[witness_idx].evals[eval_idx], // Ensure thread-safe read
        //             &|&negated| -negated,
        //             &|a, b| a + b,
        //             &|a, b| a * b,
        //         );
        //     });
        // });
        // Convert the evaluations into the coefficients of the polynomial
        sum.to_coefficients()
    }

    pub fn evaluate_ys_polynomial(
        expr: QueriedExpression<Self>,
        rows: Range<usize>,
        num_vars: usize,
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);

        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        let num_evals = indexed.expr.degree() + 1;
        // For two transcripts with respective challenge, c₀, c₁,
        // compute the evaluations of the polynomial c(X) = (1−X)⋅c₀ + X⋅c₁
        let challenges: Vec<_> = indexed
            .challenges
            .iter()
            .map(|queried_challenge| {
                EvaluatedError::new_from_boolean_evals(
                    *queried_challenge.value[0],
                    *queried_challenge.value[1],
                    num_evals,
                )
            })
            .collect();

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let mut sum = EvaluatedError::<F>::new(num_evals);
        
        for row_index in rows {
            // Evaluate the expression in the current row and add it to e(D)
            for (eval_idx, eval) in sum.evals.iter_mut().enumerate() {
                // For each `eval_idx` j = 0, 1, ..., d, evaluate the expression eᵢ(j) = βᵢ(j) G(fᵢ, wᵢ(j), rᵢ(j))
                *eval += indexed.expr.evaluate(
                    &|&constant| F::ZERO,
                    &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                    &|&fixed_idx| F::ZERO,
                    &|&witness_idx| F::ZERO,
                    &|&negated| F::ZERO,
                    &|a, b| a + b,
                    &|a, b| a * b,
                );
            }
        }

        // Convert the evaluations into the coefficients of the polynomial
        sum.to_coefficients()
    }
}

/// Represents a polynomial evaluated over the integers 0,1,...,d.
#[derive(Clone, Debug)]
pub struct EvaluatedError<F> {
    pub evals: Vec<F>,
}

// impl<F: Field> AddAssign<&EvaluatedError<F>> for EvaluatedError<F> {
//     fn add_assign(&mut self, rhs: &Self) {
//         for (lhs, rhs) in self.evals.iter_mut().zip(rhs.evals.iter()) {
//             *lhs += rhs;
//         }
//     }
// }

impl<F: Field> EvaluatedError<F> {
    /// Create a set of `num_evals` evaluations of the zero polynomial
    pub fn new(num_evals: usize) -> Self {
        Self {
            evals: vec![F::ZERO; num_evals],
        }
    }

    /// Returns the evaluations of the linear polynomial (1-X)eval0 + Xeval1.
    pub fn new_from_boolean_evals(eval0: F, eval1: F, num_evals: usize) -> Self {
        let mut result = Self::new(num_evals);
        result.evaluate(eval0, eval1);
        result
    }

    /// Overwrites the current evaluations and replaces it with the evaluations of the linear polynomial (1-X)eval0 + Xeval1.
    pub fn evaluate(&mut self, eval0: F, eval1: F) {
        let mut curr = eval0;
        let diff = eval1 - eval0;
        for eval in self.evals.iter_mut() {
            *eval = curr;
            curr += diff;
        }
    }

    /// Convert the n evalations into the coefficients of the polynomial.
    pub fn to_coefficients(&self) -> Vec<F> {
        let points: Vec<_> = field_integers().take(self.evals.len()).collect();
        lagrange_interpolate(&points, &self.evals)
    }
}
