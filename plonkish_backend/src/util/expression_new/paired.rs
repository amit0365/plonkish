use core::num;
use std::{
    collections::HashMap, iter::zip, marker::PhantomData, ops::{AddAssign, Range}, time::Instant
};

use crate::{accumulation::protostar::{hyperplonk::prover::powers_of_zeta_poly, ProtostarAccumulator}, backend::hyperplonk::prover::instance_polys, pcs::PolynomialCommitmentScheme, poly::multilinear::MultilinearPolynomial, util::{arithmetic::{div_ceil, field_integers, powers, BooleanHypercube, Field}, end_timer, expression::Rotation, expression_new::constraints::LookupData, izip, izip_eq, parallel::{num_threads, par_map_collect, parallelize_iter}, start_timer, Deserialize, Itertools, Serialize}};
use ark_std::{end_timer, start_timer};
use halo2_base::{halo2_proofs::{arithmetic::lagrange_interpolate, plonk}};
use halo2_proofs::halo2curves::ff::PrimeField;
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

pub fn split_polys<'a, F>(polys: [&'a MultilinearPolynomial<F>; 2]) -> [(&'a [F], &'a [F]); 2] {
    polys.map(|poly| poly.evals().split_at(poly.evals().len() / 2))
}

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
            let lookups_polys = total_advice[num_witness_polys..num_witness_polys + 3].to_vec(); //todo hardcoded to 3
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
        let indexed = IndexedExpression::<Paired<'a, F>>::new(&expr);

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

    pub fn evaluate_compressed_polynomial_full(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
        beta: &[CombinedQuadraticErrorFull<F>],
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(&expr);

        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        let num_evals = indexed.expr.degree() + 1;
        assert!(rows.len() == beta.len());
        //assert!(beta[0].evals.len() >= num_evals);

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
       
        for (i, row_index) in rows.iter().enumerate() {
            // Fetch fixed data
            for (fixed, query) in fixed.iter_mut().zip(indexed.fixed.iter()) {
                let row_idx = query.row_idx(*row_index, num_vars);
                *fixed = query.column[row_idx];
            }

            // Fetch witness data and interpolate
            for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
                let row_idx = query.row_idx(*row_index, num_vars);
                let eval0 = query.column[0][row_idx];
                let eval1 = query.column[1][row_idx];
                witness.evaluate(eval0, eval1);
            }

            // Evaluate the expression in the current row and add it to e(D)
            for (eval_idx, eval) in sum.evals.iter_mut().enumerate() {
                // For each `eval_idx` j = 0, 1, ..., d, evaluate the expression eᵢ(j) = βᵢ(j) G(fᵢ, wᵢ(j), rᵢ(j))
                let expr_eval = indexed.expr.evaluate(
                    &|&constant| constant,
                    &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                    &|&fixed_idx| fixed[fixed_idx],
                    &|&witness_idx| witness[witness_idx].evals[eval_idx],
                    &|&negated| -negated,
                    &|a, b| a + b,
                    &|a, b| a * b,
                );
                *eval += beta[i].evals[eval_idx] * expr_eval;
            }
        };
        // Convert the evaluations into the coefficients of the polynomial
        sum.to_coefficients()
    }

    //todo is it feasible to fetch all fixed data/wintess at once for all constraints?
    pub fn evaluate_compressed_polynomial_full_parallel(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
        beta: &[CombinedQuadraticErrorFull<F>],
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(&expr);

        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        let num_evals = indexed.expr.degree() + 1;
        assert!(rows.len() == beta.len());
        //assert!(beta[0].evals.len() >= num_evals);

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

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let sum: EvaluatedError<F> = rows.into_par_iter().map(|row_index| {
            let mut fixed = vec![F::ZERO; indexed.fixed.len()];
            let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];
    
            for (fixed, query) in fixed.iter_mut().zip(indexed.fixed.iter()) {
                let row_idx = query.row_idx(*row_index, num_vars);
                *fixed = query.column[row_idx];
            }
    
            for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
                let row_idx = query.row_idx(*row_index, num_vars);
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
        // Convert the evaluations into the coefficients of the polynomial
        sum.to_coefficients()
    }

    pub fn evaluate_compressed_polynomial_allrows_parallel(
        expr: QueriedExpression<Self>,
        rows: Vec<usize>,
        num_vars: usize,
    ) -> Vec<F> {
        use rayon::prelude::*;

        let indexed = IndexedExpression::<Paired<'a, F>>::new(&expr);
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
        let indexed = IndexedExpression::<Paired<'a, F>>::new(&expr);

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
        let indexed = IndexedExpression::<Paired<'a, F>>::new(&expr);

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

    pub fn evaluate_ys_polynomial(
        expr: QueriedExpression<Self>,
        rows: Range<usize>,
        num_vars: usize,
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(&expr);

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

// pub fn evaluate_betas_polynomial_par<F: PrimeField>(
//     beta0: &[F],
//     beta1: &[F],
//     beta_sqrt0: &[F],
//     beta_sqrt1: &[F],
// ) -> Vec<CombinedQuadraticError<F>> {
//     assert_eq!(beta0.len(), beta1.len());
//     assert_eq!(beta_sqrt0.len(), beta_sqrt1.len());
//     let beta_len = beta0.len() * beta_sqrt0.len();

//     let timer = start_timer(|| "precompute beta evals");
//     // Pre-compute evaluations for beta and beta_sqrt
//     let beta_evals: Vec<_> = beta0.iter().zip(beta1).map(|(&b0, &b1)| [b0, b1, b0 + (b1 - b0) * F::from(2u64)]).collect();
//     let beta_sqrt_evals: Vec<_> = beta_sqrt0.iter().zip(beta_sqrt1).map(|(&bs0, &bs1)| [bs0, bs1, bs0 + (bs1 - bs0) * F::from(2u64)]).collect();
//     end_timer(timer);

//     // Use rayon for parallel processing
//     use rayon::prelude::*;
    
//     beta_sqrt_evals.par_iter().flat_map(|bs_eval| {
//         beta_evals.par_iter().map(|b_eval| {
//             CombinedQuadraticError::from_evals(vec![
//                 b_eval[0] * bs_eval[0],
//                 b_eval[1] * bs_eval[1],
//                 b_eval[2] * bs_eval[2]
//             ])
//         })
//     }).collect()
// }

#[derive(Clone, Debug)]
pub struct CombinedQuadraticError<F> {
    pub evals: [F; 3],
}

impl<F: Field> CombinedQuadraticError<F> {
    // pub fn from_evals(evals: Vec<F>) -> Self {
    //     assert_eq!(evals.len(), 3);
    //     Self {
    //         evals: [evals[0], evals[1], evals[2]],
    //     }
    // }

    pub fn iter(&self) -> impl Iterator<Item = &F> {
        self.evals.iter()
    }
}

impl<F: Field> IntoIterator for CombinedQuadraticError<F> {
    type Item = F;
    type IntoIter = std::array::IntoIter<F, 3>;

    fn into_iter(self) -> Self::IntoIter {
        self.evals.into_iter()
    }
}

impl<F: Field> CombinedQuadraticErrorFull<F> {
    pub fn from_evals(evals: Vec<F>) -> Self {
        assert_eq!(evals.len(), 7);
        Self {
            evals: [evals[0], evals[1], evals[2], evals[3], evals[4], evals[5], evals[6]],
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &F> {
        self.evals.iter()
    }
}

impl<F: Field> IntoIterator for CombinedQuadraticErrorFull<F> {
    type Item = F;
    type IntoIter = std::array::IntoIter<F, 7>;

    fn into_iter(self) -> Self::IntoIter {
        self.evals.into_iter()
    }
}

#[derive(Clone, Debug, Default)]
pub struct CombinedQuadraticErrorFull<F> {
    pub evals: [F; 7],
}


pub fn evaluate_betas_polynomial_par<F: PrimeField>(
    beta0: &[F],
    beta1: &[F],
    beta_sqrt0: &[F],
    beta_sqrt1: &[F],
) -> Vec<CombinedQuadraticError<F>> {
    println!("beta0.len(): {:?}", beta0.len());
    assert_eq!(beta0.len(), beta1.len());
    assert_eq!(beta_sqrt0.len(), beta_sqrt1.len());

    let two = F::from(2u64);

    // Pre-compute evaluations for beta and beta_sqrt
    let beta_evals: Vec<[F; 3]> = beta0
        .iter()
        .zip(beta1)
        .map(|(&b0, &b1)| {
            let delta = b1 - b0;
            [b0, b1, b0 + delta * two]
        })
        .collect();

    let beta_sqrt_evals: Vec<[F; 3]> = beta_sqrt0
        .iter()
        .zip(beta_sqrt1)
        .map(|(&bs0, &bs1)| {
            let delta = bs1 - bs0;
            [bs0, bs1, bs0 + delta * two]
        })
        .collect();

    let beta_evals_len = beta_evals.len();
    let beta_sqrt_evals_len = beta_sqrt_evals.len();
    let total_len = beta_evals_len * beta_sqrt_evals_len;

    // Use a single parallel iterator over all combinations
    (0..total_len)
        .into_par_iter()
        .map(|i| {
            let b_eval_idx = i % beta_evals_len;
            let bs_eval_idx = i / beta_evals_len;

            let b_eval = &beta_evals[b_eval_idx];
            let bs_eval = &beta_sqrt_evals[bs_eval_idx];

            CombinedQuadraticError {
                evals: [
                    b_eval[0] * bs_eval[0],
                    b_eval[1] * bs_eval[1],
                    b_eval[2] * bs_eval[2],
                ],
            }
        })
        .collect()
}

pub fn evaluate_betas_selectorwise<F: PrimeField>(
    beta0: &[F],
    beta1: &[F],
    beta_sqrt0: &[F],
    beta_sqrt1: &[F],
) -> Vec<CombinedQuadraticErrorFull<F>> {
    assert_eq!(beta0.len(), beta1.len());
    assert_eq!(beta_sqrt0.len(), beta_sqrt1.len());

    let [two, three, four, five, six] = [F::from(2u64), F::from(3u64), F::from(4u64), F::from(5u64), F::from(6u64)];

    // Pre-compute evaluations for beta and beta_sqrt
    let beta_evals: Vec<[F; 7]> = beta0
        .iter()
        .zip(beta1)
        .map(|(&b0, &b1)| {
            let delta = b1 - b0;
            [b0, b1, b0 + delta * two, b0 + delta * three, b0 + delta * four, b0 + delta * five, b0 + delta * six]
        })
        .collect();

    let beta_sqrt_evals: Vec<[F; 7]> = beta_sqrt0
        .iter()
        .zip(beta_sqrt1)
        .map(|(&bs0, &bs1)| {
            let delta = bs1 - bs0;
            [bs0, bs1, bs0 + delta * two, bs0 + delta * three, bs0 + delta * four, bs0 + delta * five, bs0 + delta * six]
        })
        .collect();

    let beta_evals_len = beta_evals.len();
    let beta_sqrt_evals_len = beta_sqrt_evals.len();
    let total_len = beta_evals_len * beta_sqrt_evals_len;

    // Use a single parallel iterator over all combinations
    (0..total_len)
        .into_par_iter()
        .map(|i| {
            let b_eval_idx = i % beta_evals_len;
            let bs_eval_idx = i / beta_evals_len;

            let b_eval = &beta_evals[b_eval_idx];
            let bs_eval = &beta_sqrt_evals[bs_eval_idx];

            CombinedQuadraticErrorFull {
                evals: [
                    b_eval[0] * bs_eval[0],
                    b_eval[1] * bs_eval[1],
                    b_eval[2] * bs_eval[2],
                    b_eval[3] * bs_eval[3],
                    b_eval[4] * bs_eval[4],
                    b_eval[5] * bs_eval[5],
                    b_eval[6] * bs_eval[6],
                ],
            }
        })
        .collect()
}

pub fn evaluate_betas_polynomial<F: Field>(
    beta0: &[F],
    beta1: &[F],
    beta_sqrt0: &[F],
    beta_sqrt1: &[F],
) -> Vec<CombinedQuadraticError<F>> {
    println!("beta0.len(): {:?}", beta0.len());
    assert!(beta0.len() == beta1.len());
    assert!(beta_sqrt0.len() == beta_sqrt1.len());
    let beta_len = beta0.len() * beta_sqrt0.len();
    // For two transcripts with respective challenge, c₀, c₁,
    // compute the evaluations of the polynomial c(X) = (1−X)⋅c₀ + X⋅c₁
    let challenges0: Vec<_> = beta0
        .iter()
        .zip(beta1)
        .map(|(beta0, beta1)| {
            EvaluatedError::new_from_boolean_evals(
                *beta0,
                *beta1,
                2,
            )
        })
        .collect();

    let challenges1: Vec<_> = beta_sqrt0
        .iter()
        .zip(beta_sqrt1)
        .map(|(beta0, beta1)| {
            EvaluatedError::new_from_boolean_evals(
                *beta0,
                *beta1,
                2,
            )
        })
        .collect();

    // Take the Cartesian product of challenges0 and challenges1
    let combined_challenges = challenges1.iter().flat_map(|c1| {
        challenges0.iter().map(move |c0| {
            CombinedQuadraticError::from_evals(
                    [c0.evals[0] * c1.evals[0],
                     c0.evals[1] * c1.evals[1],
                     c0.evaluate_at_2() * c1.evaluate_at_2()]
            )
        })
    }).collect::<Vec<_>>();

    assert!(combined_challenges.len() == beta_len);
    combined_challenges
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::util::arithmetic::Field;
//     use halo2_proofs::halo2curves::bn256::Fr as F;

//     #[test]
//     fn test_evaluate_betas_polynomial() {
//         let beta0 = vec![F::from(1), F::from(2)];
//         let beta1 = vec![F::from(1), F::from(2)];
//         let beta_sqrt0 = vec![F::from(1), F::from(4)];
//         let beta_sqrt1 = vec![F::from(1), F::from(4)];

//         let result = evaluate_betas_polynomial(beta0, beta1, beta_sqrt0, beta_sqrt1);

//         assert_eq!(result.len(), 4); // 2 * 2 = 4 combined challenges

//         println!("result: {:?}", result);
//     }
// }

/// Represents a polynomial evaluated over the integers 0,1,...,d.
#[derive(Clone, Debug)]
pub struct EvaluatedError<F> {
    pub evals: Vec<F>,
}

// /// Represents a polynomial evaluated over the integers 0,1,...,d.
// #[derive(Clone, Debug)]
// pub struct CombinedQuadraticError<F> {
//     pub evals: Vec<F>,
// }

impl<F: Field> CombinedQuadraticError<F> {
    pub fn from_evals(evals: [F; 3]) -> Self {
        Self {
            evals,
        }
    }
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

    pub fn from_evals(evals: Vec<F>) -> Self {
        Self {
            evals,
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

    //evaluate the linear polynomial (1-X)eval0 + Xeval1 at point 
    pub fn evaluate_point(&self, point: F) -> F {
        point * self.evals[1] + (F::ONE - point) * self.evals[0]
    }

    //evaluate the linear polynomial (1-X)eval0 + Xeval1 at 2 
    pub fn evaluate_at_2(&self) -> F {
        self.evals[1] + self.evals[1] - self.evals[0]
    }

    /// Convert the n evalations into the coefficients of the polynomial.
    pub fn to_coefficients(&self) -> Vec<F> {
        let points: Vec<_> = field_integers().take(self.evals.len()).collect();
        lagrange_interpolate(&points, &self.evals)
    }
}
