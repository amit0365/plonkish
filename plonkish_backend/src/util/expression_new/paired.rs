use std::{
    collections::HashMap, iter::zip, marker::PhantomData, ops::{AddAssign, Range}, time::Instant
};
use crate::util::arithmetic::PrimeField;
use crate::{accumulation::protostar::{hyperplonk::prover::{powers_of_zeta_poly, PolynomialsRefsHolder}, ProtostarAccumulator}, backend::hyperplonk::prover::instance_polys, pcs::PolynomialCommitmentScheme, poly::{multilinear::MultilinearPolynomial, Polynomial}, util::{arithmetic::{div_ceil, field_integers, powers, BooleanHypercube, Field}, end_timer, expression::Rotation, expression_new::constraints::LookupData, izip, izip_eq, parallel::{num_threads, par_map_collect, parallelize_iter}, start_timer, Deserialize, Itertools, Serialize}};
use halo2_proofs::{arithmetic::{lagrange_interpolate, parallelize}, halo2curves::ff::BatchInvert, plonk};
pub use halo2_proofs::halo2curves::CurveAffine;
use rayon::{iter::{IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelExtend}, slice::{ParallelSlice, ParallelSliceMut}};
use rayon::iter::IndexedParallelIterator;
use rayon::iter::ParallelIterator;
use super::{constraints::Data, IndexedExpression, QueriedExpression, QueryType};

pub fn split_polys<'a, F>(polys: [&'a MultilinearPolynomial<F>; 2]) -> [(&'a [F], &'a [F]); 2] {
    polys.map(|poly| poly.evals().split_at(poly.evals().len() / 2))
}

pub fn beta_prime_polys<'a, F>(
    beta_prime_polys_raw: [&'a MultilinearPolynomial<F>; 2],
    beta_polys_len: usize,
    beta_prime_polys_owned: &'a mut Box<[MultilinearPolynomial<F>; 2]>,
) -> Vec<[&'a MultilinearPolynomial<F>; 2]> 
where F: Field {
    beta_prime_polys_owned[0] = MultilinearPolynomial::new(
        beta_prime_polys_raw[0]
            .clone()
            .into_evals()
            .into_iter()
            .flat_map(|x| std::iter::repeat(x).take(beta_polys_len))
            .collect(),
    );

    beta_prime_polys_owned[1] = MultilinearPolynomial::new(
        beta_prime_polys_raw[1]
            .clone()
            .into_evals()
            .into_iter()
            .flat_map(|x| std::iter::repeat(x).take(beta_polys_len))
            .collect(),
    );

    let beta_prime_polys = vec![
        [&beta_prime_polys_owned[0], &beta_prime_polys_owned[1]],
    ];

    beta_prime_polys
}

pub struct ErrorParams {
    num_vars: usize,
    num_fixed: usize,
    lookups_empty: bool,
    num_witness_polys: usize,
    num_challenges: usize,
    num_theta_primes: usize,
    num_alpha_primes: usize,
}

impl ErrorParams {
    pub fn new(num_vars: usize, num_fixed: usize, lookups_empty: bool, num_witness_polys: usize, num_challenges: usize, num_theta_primes: usize, num_alpha_primes: usize) -> Self {
        Self { num_vars, num_fixed, lookups_empty, num_witness_polys, num_challenges, num_theta_primes, num_alpha_primes }
    }
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
    type AccU = F;
}

impl<'a, F: PrimeField> Paired<'a, F> {
    /// Create a `Data` object from two accumulators, where each variable contains a pair of references to the
    /// some column from two different accumulators. This allows us to create a QueriedExpression where the leaves
    /// contain these two references.
    pub fn new_data<Pcs>(
        params: &ErrorParams,
        preprocess_polys: &'a [MultilinearPolynomial<F>],
        beta_polys_owned: &'a [MultilinearPolynomial<F>],
        beta_prime_polys_owned: &'a [MultilinearPolynomial<F>],
        acc0: &'a ProtostarAccumulator<F, Pcs>,
        acc1: &'a ProtostarAccumulator<F, Pcs>,
        acc_u: &F,
    ) -> Data<Self>
    where
        Pcs: PolynomialCommitmentScheme<F, Polynomial = MultilinearPolynomial<F>>,
    {
        let num_vars = params.num_vars;
        let num_fixed = params.num_fixed; 
        let lookups_empty = params.lookups_empty;
        let num_witness_polys = params.num_witness_polys;
        let num_challenges = params.num_challenges;
        let num_theta_primes = params.num_theta_primes;
        let num_alpha_primes = params.num_alpha_primes;

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
        let r = total_challenges.iter().skip(num_challenges + num_theta_primes).take(1).cloned().collect_vec()[0];
        let ys = total_challenges.iter().rev().take(num_alpha_primes).cloned().rev().collect_vec();

        let acc_u = vec![*acc_u];
        let beta_polys = 
            [
                &beta_polys_owned[0],
                &beta_polys_owned[1],
            ];
        let beta_prime_polys = 
            [
                &beta_prime_polys_owned[0],
                &beta_prime_polys_owned[1],
            ];

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
            acc_u,
            beta_polys,
            beta_prime_polys,
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
    // pub fn evaluate_compressed_polynomial(
    //     expr: QueriedExpression<Self>,
    //     rows: Range<usize>,
    //     num_vars: usize,
    // ) -> Vec<F> {
    //     // Convert the expression into an indexed one, where all leaves are extracted into vectors,
    //     // and replaced by the index in these vectors.
    //     // This allows us to separate the evaluation of the variables from the evaluation of the expression,
    //     // since the expression leaves will point to the indices in buffers where the evaluations are stored.
    //     let indexed = IndexedExpression::<Paired<'a, F>>::new(&expr);

    //     // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
    //     // since the polynomial e(X) has d+1 coefficients.
    //     let num_evals = indexed.expr.degree() + 1;

    //     // For two transcripts with respective challenge, c₀, c₁,
    //     // compute the evaluations of the polynomial c(X) = (1−X)⋅c₀ + X⋅c₁
    //     let challenges: Vec<_> = indexed
    //         .challenges
    //         .iter()
    //         .map(|queried_challenge| {
    //             EvaluatedError::new_from_boolean_evals(
    //                 *queried_challenge.value[0],
    //                 *queried_challenge.value[1],
    //                 num_evals,
    //             )
    //         })
    //         .collect();

    //     // For each variable of the expression, we allocate buffers for storing their evaluations at each row.
    //     // - Fixed variables are considered as constants, so we only need to fetch the value from the proving key
    //     //   and consider fᵢ(j) = fᵢ for all j
    //     // - Witness variables are interpolated from the values at the two accumulators,
    //     //   and the evaluations are stored in a buffer.
    //     let mut fixed = vec![F::ZERO; indexed.fixed.len()];
    //     let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

    //     // Running sum for e(D) = ∑ᵢ eᵢ(D)
    //     let mut sum = EvaluatedError::<F>::new(num_evals);
       
    //     for row_index in rows {
    //         // Fetch fixed data
    //         for (fixed, query) in fixed.iter_mut().zip(indexed.fixed.iter()) {
    //             let row_idx = query.row_idx(row_index, num_vars);
    //             *fixed = query.column[row_idx];
    //         }

    //         // Fetch witness data and interpolate
    //         for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
    //             let row_idx = query.row_idx(row_index, num_vars);
    //             let eval0 = query.column[0][row_idx];
    //             let eval1 = query.column[1][row_idx];
    //             witness.evaluate(eval0, eval1);
    //         }

    //         // Evaluate the expression in the current row and add it to e(D)
    //         for (eval_idx, eval) in sum.evals.iter_mut().enumerate() {
    //             // For each `eval_idx` j = 0, 1, ..., d, evaluate the expression eᵢ(j) = βᵢ(j) G(fᵢ, wᵢ(j), rᵢ(j))
    //             *eval += indexed.expr.evaluate(
    //                 &|&constant| constant,
    //                 &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
    //                 &|&fixed_idx| fixed[fixed_idx],
    //                 &|&witness_idx| witness[witness_idx].evals[eval_idx],
    //                 &|&negated| -negated,
    //                 &|a, b| a + b,
    //                 &|a, b| a * b,
    //             );
    //         }
    //     };
    //     // Convert the evaluations into the coefficients of the polynomial
    //     sum.to_coefficients()
    // }

    pub fn evaluate_compressed_polynomial_full(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
        let num_evals = indexed.expr.degree() + 1;
        if indexed.expr.degree() < 4 { // linear gate constraints don't contribute to the error polynomial i.e. 1 + 2(betas) = 3 degree free
            return vec![F::ZERO; num_evals];
        }
        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        // let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective u, 1, acc_u,
        // compute the evaluations of the polynomial u(X) = (1−X)⋅1 + X⋅acc_u
        let acc_u: Vec<_> = indexed
            .acc_u
            .iter()
            .map(|queried_acc_u| {
                EvaluatedError::new_from_boolean_evals(
                    F::ONE, // u = 1 for nark
                    queried_acc_u.value,
                    num_evals,
                )
            })
            .collect();

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
                // For each `eval_idx` j = 0, 1, ..., d, evaluate the expression eᵢ(j) = ��ᵢ(j) G(fᵢ, wᵢ(j), rᵢ(j))
                *eval += indexed.expr.evaluate(
                    &|&u| acc_u[u].evals[eval_idx],
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

    pub fn evaluate_compressed_polynomial_full_beta_selectorwise(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
        betas_error_selectorwise: &[CombinedQuadraticErrorFull<F>],
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
        let num_evals = indexed.expr.degree() + 1 + 2; // + 2 for the betas
        if indexed.expr.degree() < 2 { // linear gate constraints don't contribute to the error polynomial i.e. 1 + 2(betas) = 3 degree free
            return vec![F::ZERO; num_evals];
        }
        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        // let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective u, 1, acc_u,
        // compute the evaluations of the polynomial u(X) = (1−X)⋅1 + X⋅acc_u
        let acc_u: Vec<_> = indexed
            .acc_u
            .iter()
            .map(|queried_acc_u| {
                EvaluatedError::new_from_boolean_evals(
                    F::ONE, // u = 1 for nark
                    queried_acc_u.value,
                    num_evals,
                )
            })
            .collect();

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
                let evaluation = indexed.expr.evaluate(
                    &|&u| acc_u[u].evals[eval_idx],
                    &|&constant| constant,
                    &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                    &|&fixed_idx| fixed[fixed_idx],
                    &|&witness_idx| witness[witness_idx].evals[eval_idx],
                    &|&negated| -negated,
                    &|a, b| a + b,
                    &|a, b| a * b,
                );
                *eval += betas_error_selectorwise[i].evals[eval_idx] * evaluation; 
            }
        };
        // Convert the evaluations into the coefficients of the polynomial
        sum.to_coefficients()
    }

    pub fn evaluate_compressed_polynomial_full_beta_selectorwise_sha256(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
        betas_error_selectorwise: &[CombinedQuadraticErrorFullSha256<F>],
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
        let num_evals = indexed.expr.degree() + 1 + 2; // + 2 for the betas
        if indexed.expr.degree() < 2 { // linear gate constraints don't contribute to the error polynomial i.e. 1 + 2(betas) = 3 degree free
            return vec![F::ZERO; num_evals];
        }
        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        // let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective u, 1, acc_u,
        // compute the evaluations of the polynomial u(X) = (1−X)⋅1 + X⋅acc_u
        let acc_u: Vec<_> = indexed
            .acc_u
            .iter()
            .map(|queried_acc_u| {
                EvaluatedError::new_from_boolean_evals(
                    F::ONE, // u = 1 for nark
                    queried_acc_u.value,
                    num_evals,
                )
            })
            .collect();

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
                let evaluation = indexed.expr.evaluate(
                    &|&u| acc_u[u].evals[eval_idx],
                    &|&constant| constant,
                    &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                    &|&fixed_idx| fixed[fixed_idx],
                    &|&witness_idx| witness[witness_idx].evals[eval_idx],
                    &|&negated| -negated,
                    &|a, b| a + b,
                    &|a, b| a * b,
                );
                *eval += betas_error_selectorwise[i].evals[eval_idx] * evaluation; 
            }
        };
        // Convert the evaluations into the coefficients of the polynomial
        sum.to_coefficients()
    }

    pub fn evaluate_compressed_polynomial_full_beta_selectorwise_combined_sequential(
        expr_vec: &[QueriedExpression<Self>],
        rows: &[usize],
        num_vars: usize,
        betas_error_selectorwise_vec: &[&[CombinedQuadraticErrorFull<F>]],
    ) -> Vec<Vec<F>> {
        let num_constraints = expr_vec.len();
        let indexed_vec = expr_vec.iter().map(IndexedExpression::<Paired<'a, F>>::new).collect_vec();
        let num_evals_vec = indexed_vec.iter().map(|indexed| indexed.expr.degree() + 1 + 2).collect_vec();
        if indexed_vec.iter().any(|indexed| indexed.expr.degree() < 2) {
            return vec![vec![F::ZERO; num_evals_vec[0]]; num_constraints];
        }
    
        let acc_u_vec = indexed_vec.iter().enumerate().map(|(j, indexed)| {
            indexed.acc_u.iter().map(|queried_acc_u| {
                EvaluatedError::new_from_boolean_evals(F::ONE, queried_acc_u.value, num_evals_vec[j])
            }).collect_vec()
        }).collect_vec();
    
        let challenges_vec = indexed_vec.iter().enumerate().map(|(j, indexed)| {
            indexed.challenges.iter().map(|queried_challenge| {
                EvaluatedError::new_from_boolean_evals(
                    *queried_challenge.value[0],
                    *queried_challenge.value[1],
                    num_evals_vec[j],
                )
            }).collect_vec()
        }).collect_vec();
    
        let mut sum_vec = vec![EvaluatedError::<F>::new(num_evals_vec[0]); num_constraints];
    
        for (i, row_index) in rows.iter().enumerate() {
            let mut fixed_vec = indexed_vec.iter().map(|indexed| vec![F::ZERO; indexed.fixed.len()]).collect_vec();
            let mut witness_vec = indexed_vec.iter().enumerate().map(|(j, indexed)| {
                vec![EvaluatedError::<F>::new(num_evals_vec[j]); indexed.witness.len()]
            }).collect_vec();
    
            // Process fixed columns
            for (j, fixed) in fixed_vec.iter_mut().enumerate() {
                for (fixed, query) in fixed.iter_mut().zip(indexed_vec[j].fixed.iter()) {
                    let row_idx = query.row_idx(*row_index, num_vars);
                    *fixed = query.column[row_idx];
                }
            }
    
            // Process witness columns
            for (j, witness) in witness_vec.iter_mut().enumerate() {
                for (witness, query) in witness.iter_mut().zip(indexed_vec[j].witness.iter()) {
                    let row_idx = query.row_idx(*row_index, num_vars);
                    let eval0 = query.column[0][row_idx];
                    let eval1 = query.column[1][row_idx];
                    witness.evaluate(eval0, eval1);
                }
            }
    
            // Evaluate expressions
            for (j, indexed) in indexed_vec.iter().enumerate() {
                for eval_idx in 0..num_evals_vec[j] {
                    let eval = indexed.expr.evaluate(
                        &|&u| acc_u_vec[j][u].evals[eval_idx],
                        &|&constant| constant,
                        &|&challenge_idx| challenges_vec[j][challenge_idx].evals[eval_idx],
                        &|&fixed_idx| fixed_vec[j][fixed_idx],
                        &|&witness_idx| witness_vec[j][witness_idx].evals[eval_idx],
                        &|&negated| -negated,
                        &|a, b| a + b,
                        &|a, b| a * b,
                    );
                    sum_vec[j].evals[eval_idx] += betas_error_selectorwise_vec[j][i].evals[eval_idx] * eval;
                }
            }
        }
    
        sum_vec.into_iter().map(|sum| sum.to_coefficients()).collect_vec()
    }

    pub fn evaluate_compressed_polynomial_full_beta_selectorwise_combined_parallel(
        expr_vec: &[QueriedExpression<Self>],
        rows: &[usize],
        num_vars: usize,
        betas_error_selectorwise_vec: &[&[CombinedQuadraticErrorFull<F>]],
    ) -> Vec<Vec<F>> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let num_constraints = expr_vec.len();
        let indexed_vec = expr_vec.iter().map(IndexedExpression::<Paired<'a, F>>::new).collect_vec();
        let num_evals_vec = indexed_vec.iter().map(|indexed| indexed.expr.degree() + 1 + 2).collect_vec(); // + 2 for the betas
        if indexed_vec.iter().any(|indexed| indexed.expr.degree() < 2) { // linear gate constraints don't contribute to the error polynomial i.e. 1 + 2(betas) = 3 degree free
            return vec![vec![F::ZERO; num_evals_vec[0]]; num_constraints];
        }
        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        // let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective u, 1, acc_u,
        // compute the evaluations of the polynomial u(X) = (1−X)⋅1 + X⋅acc_u
        let acc_u_vec: Vec<Vec<EvaluatedError<F>>> = indexed_vec.par_iter().enumerate().map(|(j, indexed)| indexed.acc_u.iter().map(|queried_acc_u| {
                EvaluatedError::new_from_boolean_evals(
                    F::ONE, // u = 1 for nark
                    queried_acc_u.value,
                    num_evals_vec[j],
                )
            })
            .collect_vec()).collect();

        // For two transcripts with respective challenge, c₀, c₁,
        // compute the evaluations of the polynomial c(X) = (1−X)⋅c₀ + X⋅c₁
        let challenges_vec: Vec<Vec<EvaluatedError<F>>> = indexed_vec.par_iter().enumerate().map(|(j, indexed)| indexed.challenges.iter().map(|queried_challenge| {
                EvaluatedError::new_from_boolean_evals(
                    *queried_challenge.value[0],
                    *queried_challenge.value[1],
                    num_evals_vec[j],
                )
            })
            .collect_vec()).collect();
        // For each variable of the expression, we allocate buffers for storing their evaluations at each row.
        // - Fixed variables are considered as constants, so we only need to fetch the value from the proving key
        //   and consider fᵢ(j) = fᵢ for all j
        // - Witness variables are interpolated from the values at the two accumulators,
        //   and the evaluations are stored in a buffer.
        // let mut fixed = vec![F::ZERO; indexed.fixed.len()];
        // let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let sum_vec: Vec<EvaluatedError<F>> = rows.into_par_iter().enumerate().map(|(i, row_index)| {
            let mut fixed_vec = indexed_vec.iter().map(|indexed| vec![F::ZERO; indexed.fixed.len()]).collect_vec();
            let mut witness_vec = indexed_vec.iter().enumerate().map(|(j, indexed)| vec![EvaluatedError::<F>::new(num_evals_vec[j]); indexed.witness.len()]).collect_vec();
            fixed_vec.par_iter_mut().enumerate().for_each(|(j, fixed)| {
                for (fixed, query) in fixed.iter_mut().zip(indexed_vec[j].fixed.iter()) {
                    let row_idx = query.row_idx(*row_index, num_vars);
                    *fixed = query.column[row_idx];
                }
            });
    
            witness_vec.par_iter_mut().enumerate().for_each(|(j, witness)| {
                for (witness, query) in witness.iter_mut().zip(indexed_vec[j].witness.iter()) {
                    let row_idx = query.row_idx(*row_index, num_vars);
                    let eval0 = query.column[0][row_idx];
                    let eval1 = query.column[1][row_idx];
                    witness.evaluate(eval0, eval1);
                }
            });
            let mut row_sum_vec = vec![EvaluatedError::<F>::new(num_evals_vec[0]); num_constraints];
            row_sum_vec.par_iter_mut().enumerate().zip(indexed_vec.par_iter()).for_each(|((j, row_sum), indexed)| {
                let evals = (0..num_evals_vec[j]).into_par_iter().map(|eval_idx| {
                    let eval = indexed.expr.evaluate(
                        &|&u| acc_u_vec[j][u].evals[eval_idx],
                        &|&constant| constant, 
                        &|&challenge_idx| challenges_vec[j][challenge_idx].evals[eval_idx],
                        &|&fixed_idx| fixed_vec[j][fixed_idx],
                        &|&witness_idx| witness_vec[j][witness_idx].evals[eval_idx],
                        &|&negated| -negated,
                        &|a, b| a + b,
                        &|a, b| a * b,
                    );
                    betas_error_selectorwise_vec[j][i].evals[eval_idx] * eval
                }).collect::<Vec<_>>();
    
                for (idx, eval) in evals.into_iter().enumerate() {
                    row_sum.evals[idx] += eval;
                }
            });
            row_sum_vec
        })
        .collect::<Vec<_>>()
        .into_iter()
        .map(|sum_vec| {
            sum_vec.into_iter().reduce(|a, b| {
                let mut result = a.clone();
                for k in 0..a.evals.len() {
                    result.evals[k] += b.evals[k];
                }
                result
            }).unwrap()
        })
        .collect_vec();

        // Convert the evaluations into the coefficients of the polynomial
        sum_vec.into_iter().map(|sum| sum.to_coefficients()).collect_vec()
    }

    pub fn evaluate_compressed_polynomial_full_beta_selectorwise_sha256_parallel(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
        betas_error_selectorwise: &[CombinedQuadraticErrorFullSha256<F>],
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
        let num_evals = indexed.expr.degree() + 1 + 2; // + 2 for the betas
        if indexed.expr.degree() < 2 { // linear gate constraints don't contribute to the error polynomial i.e. 1 + 2(betas) = 3 degree free
            return vec![F::ZERO; num_evals];
        }
        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        // let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective u, 1, acc_u,
        // compute the evaluations of the polynomial u(X) = (1−X)⋅1 + X⋅acc_u
        let acc_u: Vec<_> = indexed
            .acc_u
            .iter()
            .map(|queried_acc_u| {
                EvaluatedError::new_from_boolean_evals(
                    F::ONE, // u = 1 for nark
                    queried_acc_u.value,
                    num_evals,
                )
            })
            .collect();

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
        // let mut fixed = vec![F::ZERO; indexed.fixed.len()];
        // let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let sum: EvaluatedError<F> = rows.into_par_iter().enumerate().map(|(i, row_index)| {
            let mut fixed = vec![F::ZERO; indexed.fixed.len()];
            let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];
            for (i, (fixed, query)) in fixed.iter_mut().zip(indexed.fixed.iter()).enumerate() {
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
                let eval = indexed.expr.evaluate(
                    &|&u| acc_u[u].evals[eval_idx],
                    &|&constant| constant,
                    &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                    &|&fixed_idx| fixed[fixed_idx],
                    &|&witness_idx| witness[witness_idx].evals[eval_idx],
                    &|&negated| -negated,
                    &|a, b| a + b,
                    &|a, b| a * b,
                );
                row_sum.evals[eval_idx] += betas_error_selectorwise[i].evals[eval_idx] * eval;
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

    pub fn evaluate_compressed_polynomial_full_beta_selectorwise_parallel(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
        betas_error_selectorwise: &[CombinedQuadraticErrorFull<F>],
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
        let num_evals = indexed.expr.degree() + 1 + 2; // + 2 for the betas
        if indexed.expr.degree() < 2 { // linear gate constraints don't contribute to the error polynomial i.e. 1 + 2(betas) = 3 degree free
            return vec![F::ZERO; num_evals];
        }
        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        // let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective u, 1, acc_u,
        // compute the evaluations of the polynomial u(X) = (1−X)⋅1 + X⋅acc_u
        let acc_u: Vec<_> = indexed
            .acc_u
            .iter()
            .map(|queried_acc_u| {
                EvaluatedError::new_from_boolean_evals(
                    F::ONE, // u = 1 for nark
                    queried_acc_u.value,
                    num_evals,
                )
            })
            .collect();

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
        // let mut fixed = vec![F::ZERO; indexed.fixed.len()];
        // let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let sum: EvaluatedError<F> = rows.into_par_iter().enumerate().map(|(i, row_index)| {
            let mut fixed = vec![F::ZERO; indexed.fixed.len()];
            let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];
            for (i, (fixed, query)) in fixed.iter_mut().zip(indexed.fixed.iter()).enumerate() {
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
                let eval = indexed.expr.evaluate(
                    &|&u| acc_u[u].evals[eval_idx],
                    &|&constant| constant,
                    &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                    &|&fixed_idx| fixed[fixed_idx],
                    &|&witness_idx| witness[witness_idx].evals[eval_idx],
                    &|&negated| -negated,
                    &|a, b| a + b,
                    &|a, b| a * b,
                );
                row_sum.evals[eval_idx] += betas_error_selectorwise[i].evals[eval_idx] * eval;
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

    // pub fn evaluate_compressed_polynomial_full_beta_selectorwise_parallel_batch_eval(
    //     expr: &QueriedExpression<Self>,
    //     rows: &[usize],
    //     num_vars: usize,
    //     betas_error_selectorwise: &[CombinedQuadraticErrorFull<F>],
    // ) -> Vec<F> {
    //     // Convert the expression into an indexed one, where all leaves are extracted into vectors,
    //     // and replaced by the index in these vectors.
    //     // This allows us to separate the evaluation of the variables from the evaluation of the expression,
    //     // since the expression leaves will point to the indices in buffers where the evaluations are stored.
    //     let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
    //     let num_evals = indexed.expr.degree() + 1 + 2; // + 2 for the betas
    //     if indexed.expr.degree() < 2 { // linear gate constraints don't contribute to the error polynomial i.e. 1 + 2(betas) = 3 degree free
    //         return vec![F::ZERO; num_evals];
    //     }
    //     // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
    //     // since the polynomial e(X) has d+1 coefficients.
    //     // let num_evals = indexed.expr.degree() + 1;

    //     // For two transcripts with respective u, 1, acc_u,
    //     // compute the evaluations of the polynomial u(X) = (1−X)⋅1 + X⋅acc_u
    //     let acc_u: Vec<EvaluatedError<F>> = indexed
    //         .acc_u
    //         .iter()
    //         .map(|queried_acc_u| {
    //             EvaluatedError::new_from_boolean_evals(
    //                 F::ONE, // u = 1 for nark
    //                 queried_acc_u.value,
    //                 num_evals,
    //             )
    //         })
    //         .collect();

    //     // For two transcripts with respective challenge, c₀, c₁,
    //     // compute the evaluations of the polynomial c(X) = (1−X)⋅c₀ + X⋅c₁
    //     let challenges: Vec<_> = indexed
    //         .challenges
    //         .iter()
    //         .map(|queried_challenge| {
    //             EvaluatedError::new_from_boolean_evals(
    //                 *queried_challenge.value[0],
    //                 *queried_challenge.value[1],
    //                 num_evals,
    //             )
    //         })
    //         .collect();

    //     // For each variable of the expression, we allocate buffers for storing their evaluations at each row.
    //     // - Fixed variables are considered as constants, so we only need to fetch the value from the proving key
    //     //   and consider fᵢ(j) = fᵢ for all j
    //     // - Witness variables are interpolated from the values at the two accumulators,
    //     //   and the evaluations are stored in a buffer.
    //     // let mut fixed = vec![F::ZERO; indexed.fixed.len()];
    //     // let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

    //     // Running sum for e(D) = ∑ᵢ eᵢ(D)
    //     let sum: EvaluatedError<F> = rows.into_par_iter().enumerate().map(|(i, row_index)| {
    //         let mut fixed = vec![F::ZERO; indexed.fixed.len()];
    //         let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];
    //         for (i, (fixed, query)) in fixed.iter_mut().zip(indexed.fixed.iter()).enumerate() {
    //             let row_idx = query.row_idx(*row_index, num_vars);
    //             *fixed = query.column[row_idx];
    //         }
    
    //         for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
    //             let row_idx = query.row_idx(*row_index, num_vars);
    //             let eval0 = query.column[0][row_idx];
    //             let eval1 = query.column[1][row_idx];
    //             witness.evaluate(eval0, eval1);
    //         }
    
    //         let acc_u_fn = |&u: &usize| -> &[F] {acc_u[u].evals.as_slice()};
    //         let constant_fn = |&c| vec![c; num_evals]; // replicate the constant value
    //         let challenge_fn = |&ch: &usize| -> &[F] {challenges[ch].};
    //         let fixed_fn = |&fx: &usize| -> &[F] {vec![fixed[fx]; num_evals].as_slice()};    // or precomputed slice
    //         let witness_fn = |&wx: &usize| -> &[F] {witness[wx].evals.as_slice()};

    //         let negated_fn = |vals: &[F]| vals.iter().map(|x| -*x).collect();
    //         let sum_fn = |lhs: &[F], rhs: &[F]| lhs.iter().zip(rhs).map(|(l, r)| *l + *r).collect();
    //         let product_fn = |lhs: &[F], rhs: &[F]| lhs.iter().zip(rhs).map(|(l, r)| *l * *r).collect();

    //         let evals = indexed.expr.batch_evaluate(
    //             &acc_u_fn,
    //             &constant_fn,
    //             &challenge_fn,
    //             &fixed_fn,
    //             &witness_fn,
    //             &negated_fn,
    //             &sum_fn,
    //             &product_fn,
    //         );
    //         let mut row_sum = EvaluatedError::<F>::new(num_evals);
    //         for eval_idx in 0..num_evals {
    //             row_sum.evals[eval_idx] += betas_error_selectorwise[i].evals[eval_idx] * evals[eval_idx];
    //         }
    //         row_sum
    //     }).reduce(|| EvaluatedError::<F>::new(num_evals), |a, b| {
    //         let mut result = EvaluatedError::<F>::new(num_evals);
    //         for i in 0..num_evals {
    //             result.evals[i] = a.evals[i] + b.evals[i];
    //         }
    //         result
    //     });
    //     // Convert the evaluations into the coefficients of the polynomial
    //     sum.to_coefficients()
    // }

    pub fn evaluate_compressed_polynomial_full_beta_selectorwise_parallel_batch_eval(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
        betas_error_selectorwise: &[CombinedQuadraticErrorFull<F>],
    ) -> Vec<F> {
        // Convert the expression into an indexed one
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
        let num_evals = indexed.expr.degree() + 1 + 2; // +2 for the betas
        if indexed.expr.degree() < 2 {
            // For linear constraints, no contribution
            return vec![F::ZERO; num_evals];
        }
    
        // Precompute acc_u and challenges once
        let acc_u: Vec<EvaluatedError<F>> = indexed
            .acc_u
            .iter()
            .map(|queried_acc_u| EvaluatedError::new_from_boolean_evals(F::ONE, queried_acc_u.value, num_evals))
            .collect();
    
        let challenges: Vec<EvaluatedError<F>> = indexed
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
        
        // Prepare function references that do not depend on row_index
        let negated_fn = |vals: &[F]| vals.iter().map(|x| -*x).collect::<Vec<F>>();
        let sum_fn = |lhs: &[F], rhs: &[F]| lhs.iter().zip(rhs).map(|(l, r)| *l + *r).collect::<Vec<F>>();
        let product_fn = |lhs: &[F], rhs: &[F]| lhs.iter().zip(rhs).map(|(l, r)| *l * *r).collect::<Vec<F>>();
    
        // We'll process each row in parallel. To avoid repeated allocation, use map_init.
        let sum: EvaluatedError<F> = rows
            .par_iter()
            .enumerate()
            .map_init(
                // Initialize thread-local buffers once per thread
                || {
                    let fixed_buf = vec![F::ZERO; indexed.fixed.len()];
                    let witness_buf = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];
                    // A buffer for fixed replicated values (to avoid re-allocating every eval)
                    let mut fixed_eval_buf = vec![F::ZERO; num_evals];
                    (fixed_buf, witness_buf, fixed_eval_buf)
                },
                |(fixed, witness, fixed_eval_buf), (i, &row_index)| {
                    // Fill fixed and witness for this row
                    for (fx_val, query) in fixed.iter_mut().zip(&indexed.fixed) {
                        let row_idx = query.row_idx(row_index, num_vars);
                        *fx_val = query.column[row_idx];
                    }
    
                    for (wit_val, query) in witness.iter_mut().zip(&indexed.witness) {
                        let row_idx = query.row_idx(row_index, num_vars);
                        let eval0 = query.column[0][row_idx];
                        let eval1 = query.column[1][row_idx];
                        wit_val.evaluate(eval0, eval1);
                    }
    
                    // Precompute a vector of vectors, each containing num_evals copies of the fixed value
                    let mut fixed_arrays = Vec::with_capacity(indexed.fixed.len());
                    for &fx_val in fixed.iter() {
                        let mut arr = vec![fx_val; num_evals];
                        fixed_arrays.push(arr);
                    }

                    let acc_u_fn = |&u: &usize| acc_u[u].evals.to_vec();
                    let constant_fn = |&c: &F| vec![c; num_evals];
                    let challenge_fn = |&ch: &usize| challenges[ch].evals.to_vec();
                    let fixed_fn = |&fx: &usize| fixed_arrays[fx].to_vec();
                    let witness_fn = |&wx: &usize| witness[wx].evals.to_vec();
    
                    // Batch evaluate once for all eval indices
                    let evals = indexed.expr.batch_evaluate(
                        &acc_u_fn,
                        &constant_fn,
                        &challenge_fn,
                        &fixed_fn,
                        &witness_fn,
                        &negated_fn,
                        &sum_fn,
                        &product_fn,
                    );
    
                    // Combine with betas_error_selectorwise
                    let mut row_sum = EvaluatedError::<F>::new(num_evals);
                    for eval_idx in 0..num_evals {
                        row_sum.evals[eval_idx] =
                            betas_error_selectorwise[i].evals[eval_idx] * evals[eval_idx];
                    }
                    row_sum
                },
            )
            .reduce(
                || EvaluatedError::<F>::new(num_evals),
                |mut a, b| {
                    for i in 0..num_evals {
                        a.evals[i] += b.evals[i];
                    }
                    a
                },
            );
    
        // Convert to coefficients
        sum.to_coefficients()
    }

    
    pub fn evaluate_compressed_polynomial_full_beta_selectorwise_parallel_chunks(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
        betas_error_selectorwise: &[CombinedQuadraticErrorFull<F>],
    ) -> Vec<F> {
        //let chunk_size = 100;
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
        let num_evals = indexed.expr.degree() + 1 + 2; // + 2 for the betas
        if indexed.expr.degree() < 2 { // linear gate constraints don't contribute to the error polynomial i.e. 1 + 2(betas) = 3 degree free
            return vec![F::ZERO; num_evals];
        }
        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        // let num_evals = indexed.expr.degree() + 1;

        // For two transcripts with respective u, 1, acc_u,
        // compute the evaluations of the polynomial u(X) = (1−X)⋅1 + X⋅acc_u
        let acc_u: Vec<_> = indexed
            .acc_u
            .iter()
            .map(|queried_acc_u| {
                EvaluatedError::new_from_boolean_evals(
                    F::ONE, // u = 1 for nark
                    queried_acc_u.value,
                    num_evals,
                )
            })
            .collect();

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
        // let mut fixed = vec![F::ZERO; indexed.fixed.len()];
        // let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let chunk_size = div_ceil(rows.len(), num_threads());
        let sum: EvaluatedError<F> = rows
            .par_chunks(chunk_size)
            .enumerate()
            .map(|(chunk_idx, row_chunk)| {
                let mut row_sum = EvaluatedError::<F>::new(num_evals);
                let base_idx = chunk_idx * chunk_size;
                
                for (i, row_index) in row_chunk.iter().enumerate() {
                    let mut fixed = vec![F::ZERO; indexed.fixed.len()];
                    let mut witness = vec![EvaluatedError::<F>::new(num_evals); indexed.witness.len()];
                    
                    // Process fixed columns
                    for (fixed, query) in fixed.iter_mut().zip(indexed.fixed.iter()) {
                        let row_idx = query.row_idx(*row_index, num_vars);
                        *fixed = query.column[row_idx];
                    }
                    
                    // Process witness columns
                    for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
                        let row_idx = query.row_idx(*row_index, num_vars);
                        let eval0 = query.column[0][row_idx];
                        let eval1 = query.column[1][row_idx];
                        witness.evaluate(eval0, eval1);
                    }
                    
                    // Evaluate expression for each eval_idx
                    for eval_idx in 0..num_evals {
                        let eval = indexed.expr.evaluate(
                            &|&u| acc_u[u].evals[eval_idx],
                            &|&constant| constant,
                            &|&challenge_idx| challenges[challenge_idx].evals[eval_idx],
                            &|&fixed_idx| fixed[fixed_idx],
                            &|&witness_idx| witness[witness_idx].evals[eval_idx],
                            &|&negated| -negated,
                            &|a, b| a + b,
                            &|a, b| a * b,
                        );
                        row_sum.evals[eval_idx] += betas_error_selectorwise[base_idx + i].evals[eval_idx] * eval;
                    }
                }
                row_sum
            })
            .reduce(|| EvaluatedError::<F>::new(num_evals), |a, b| {
                let mut result = EvaluatedError::<F>::new(num_evals);
                for i in 0..num_evals {
                    result.evals[i] = a.evals[i] + b.evals[i];
                }
                result
            });
        // Convert the evaluations into the coefficients of the polynomial
        sum.to_coefficients()
    }

    //todo is it feasible to fetch all fixed data/wintess at once for all constraints?
    pub fn evaluate_compressed_polynomial_full_parallel(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
        //acc_u: F,
    ) -> Vec<F> {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Paired<'a, F>>::new(expr);
        // Evaluate the polynomial at the points 0,1,...,d, where d is the degree of expr,
        // since the polynomial e(X) has d+1 coefficients.
        let num_evals = indexed.expr.degree() + 1;
        if indexed.expr.degree() < 4 { // linear gate constraints don't contribute to the error polynomial i.e. 1 + 2(betas) = 3 degree free
            return vec![F::ZERO; num_evals];
        }

        // For two transcripts with respective u, 1, acc_u,
        // compute the evaluations of the polynomial u(X) = (1−X)⋅1 + X⋅acc_u
        let acc_u: Vec<_> = indexed
            .acc_u
            .iter()
            .map(|queried_acc_u| {
                EvaluatedError::new_from_boolean_evals(
                    F::ONE, // u = 1 for nark
                    queried_acc_u.value,
                    num_evals,
                )
            })
            .collect();

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
            let mut fixed_size = 0;
            for (i, (fixed, query)) in fixed.iter_mut().zip(indexed.fixed.iter()).enumerate() {
                // if i == 0 {
                //     println!("row_index {}", row_index);
                //     fixed_size = LOOKUP_BITS;
                // } else {
                //     fixed_size = num_vars;
                // }
                fixed_size = num_vars;
                let row_idx = query.row_idx(*row_index, fixed_size);
                *fixed = query.column[row_idx];
            }
    
            for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
                let row_idx = query.row_idx(*row_index, num_vars);
                let eval0 = query.column[0][row_idx];
                let eval1 = query.column[1][row_idx];
                witness.evaluate(eval0, eval1);
            }

            // Fetch witness data and interpolate in parallel
            // witness.par_iter_mut().zip(indexed.witness.par_iter()).for_each(|(witness, query)| {
            //     let row_idx = query.row_idx(*row_index, num_vars);
            //     let eval0 = query.column[0][row_idx];
            //     let eval1 = query.column[1][row_idx];
            //     witness.evaluate(eval0, eval1);
            // });
    
            let mut row_sum = EvaluatedError::<F>::new(num_evals);
            for eval_idx in 0..num_evals {
                row_sum.evals[eval_idx] = indexed.expr.evaluate(
                    &|&u| acc_u[u].evals[eval_idx],
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
}

/// Defines a QueriedExpression where leaves are references values from a single accumulator.
pub struct Single<'a, F> {
    _marker: PhantomData<&'a F>,
}

impl<'a, F: Field> QueryType for Single<'a, F> {
    type F = F;
    type Challenge = &'a F;
    type Fixed = &'a MultilinearPolynomial<F>;
    type Witness = &'a MultilinearPolynomial<F>;
    type AccU = F;
}

impl<'a, F: PrimeField> Single<'a, F> {
    /// Create a `Data` object from a single accumulator, where each variable contains a reference to the
    /// some column from the accumulator. This allows us to create a QueriedExpression where the leaves
    /// contain this reference.
    pub fn new_data<Pcs>(
        params: &ErrorParams,
        preprocess_polys: &'a [MultilinearPolynomial<F>],
        beta_polys: &'a MultilinearPolynomial<F>,
        beta_prime_polys: &'a MultilinearPolynomial<F>,
        acc: &'a ProtostarAccumulator<F, Pcs>,
        acc_u: &'a F,
    ) -> Data<Self>
    where
        Pcs: PolynomialCommitmentScheme<F, Polynomial = MultilinearPolynomial<F>>,
    {
        let num_vars = params.num_vars;
        let num_fixed = params.num_fixed;
        let lookups_empty = params.lookups_empty;
        let num_witness_polys = params.num_witness_polys;
        let num_challenges = params.num_challenges;
        let num_theta_primes = params.num_theta_primes;
        let num_alpha_primes = params.num_alpha_primes;

        let fixed = preprocess_polys[..num_fixed].iter().collect();
        let selectors = preprocess_polys[num_fixed..].iter().collect();
        let instance = acc.instance_polys.iter().collect();
        let total_advice = acc.witness_polys.iter().collect_vec();
        let advice= total_advice.clone().into_iter().take(num_witness_polys).collect_vec();
        let challenges = acc.instance.challenges.iter().take(num_challenges).collect_vec();
        let thetas = acc.instance.challenges.iter().skip(num_challenges).take(num_theta_primes).collect_vec();
        let r = acc.instance.challenges.iter().skip(num_challenges + num_theta_primes).take(1).collect_vec()[0];
        let ys = acc.instance.challenges.iter().rev().take(num_alpha_primes).rev().collect_vec();
        let acc_u = vec![*acc_u];
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
            acc_u,
            beta_polys,
            beta_prime_polys,
            lookups,
            ys,
        }
    }

    pub fn evaluate_compressed_polynomial_full(
        expr: &QueriedExpression<Self>,
        rows: &[usize],
        num_vars: usize,
        betas_selectorwise: &[F],
    ) -> F {
        // Convert the expression into an indexed one, where all leaves are extracted into vectors,
        // and replaced by the index in these vectors.
        // This allows us to separate the evaluation of the variables from the evaluation of the expression,
        // since the expression leaves will point to the indices in buffers where the evaluations are stored.
        let indexed = IndexedExpression::<Single<'a, F>>::new(expr);
        if indexed.expr.degree() < 2 { // linear gate constraints don't contribute to the error polynomial i.e. 1 + 2(betas) = 3 degree free
            return F::ZERO;
        }

        // For two transcripts with respective u, 1, acc_u,
        // compute the evaluations of the polynomial u(X) = (1−X)⋅1 + X⋅acc_u
        let acc_u: Vec<_> = indexed
            .acc_u
            .iter()
            .map(|queried_acc_u| {
                queried_acc_u.value
            })
            .collect();

        // For two transcripts with respective challenge, c₀, c₁,
        // compute the evaluations of the polynomial c(X) = (1−X)⋅c₀ + X⋅c₁
        let challenges: Vec<_> = indexed
            .challenges
            .iter()
            .map(|queried_challenge| {
                queried_challenge.value
            })
            .collect();
        
        // For each variable of the expression, we allocate buffers for storing their evaluations at each row.
        // - Fixed variables are considered as constants, so we only need to fetch the value from the proving key
        //   and consider fᵢ(j) = fᵢ for all j
        // - Witness variables are interpolated from the values at the two accumulators,
        //   and the evaluations are stored in a buffer.
        let mut fixed = vec![F::ZERO; indexed.fixed.len()];
        let mut witness = vec![F::ZERO; indexed.witness.len()];

        // Running sum for e(D) = ∑ᵢ eᵢ(D)
        let mut sum = F::ZERO;
        for (i, row_index) in rows.iter().enumerate() {
            // Fetch fixed data
            for (fixed, query) in fixed.iter_mut().zip(indexed.fixed.iter()) {
                let row_idx = query.row_idx(*row_index, num_vars);
                *fixed = query.column[row_idx];
            }

            // Fetch witness data and interpolate
            for (witness, query) in witness.iter_mut().zip(indexed.witness.iter()) {
                let row_idx = query.row_idx(*row_index, num_vars);
                *witness = query.column[row_idx];
            }

            // Evaluate the expression in the current row and add it to e(D)
            // For each `eval_idx` j = 0, 1, ..., d, evaluate the expression eᵢ(j) = βᵢ(j) G(fᵢ, wᵢ(j), rᵢ(j))
            let eval = indexed.expr.evaluate(
                &|&u| acc_u[u],
                &|&constant| constant,
                &|&challenge_idx| *challenges[challenge_idx],
                &|&fixed_idx| fixed[fixed_idx],
                &|&witness_idx| witness[witness_idx],
                &|&negated| -negated,
                &|a, b| a + b,
                &|a, b| a * b,
            );
            sum += betas_selectorwise[i] * eval;
        };
        // Convert the evaluations into the coefficients of the polynomial
        sum
    }
    
}

// impl<F: Field> CombinedQuadraticErrorFull<F> {
//     pub fn from_evals(evals: Vec<F>) -> Self {
//         assert_eq!(evals.len(), 7);
//         Self {
//             evals: [evals[0], evals[1], evals[2], evals[3], evals[4], evals[5], evals[6], evals[7], evals[8]],
//         }
//     }

//     pub fn iter(&self) -> impl Iterator<Item = &F> {
//         self.evals.iter()
//     }
// }

// impl<F: Field> IntoIterator for CombinedQuadraticErrorFull<F> {
//     type Item = F;
//     type IntoIter = std::array::IntoIter<F, 9>;

//     fn into_iter(self) -> Self::IntoIter {
//         self.evals.into_iter()
//     }
// }

pub const COMBINED_QUADRATIC_ERROR_FULL_LEN_SHA256: usize =11;
pub const QUOTIENT_ERROR_LEN_SHA256: usize = 9;
pub const COMBINED_QUADRATIC_ERROR_FULL_LEN: usize =9; //d+1 //9 for regular, 11 for sha256
pub const QUOTIENT_ERROR_LEN: usize = 7; //d-1 //7 for regular, 9 for sha256


#[derive(Clone, Debug, Default)]
pub struct CombinedQuadraticErrorFullSha256<F> {
    pub evals: [F; COMBINED_QUADRATIC_ERROR_FULL_LEN_SHA256],
}

#[derive(Clone, Debug, Default)]
pub struct CombinedQuadraticErrorFull<F> {
    pub evals: [F; COMBINED_QUADRATIC_ERROR_FULL_LEN],
}


pub fn evaluate_betas_error_selectorwise<F: PrimeField>(
    beta0: &[F],
    beta1: &[F],
    beta_sqrt0: &[F],
    beta_sqrt1: &[F],
) -> Vec<CombinedQuadraticErrorFull<F>> {
    assert_eq!(beta0.len(), beta1.len());
    assert_eq!(beta_sqrt0.len(), beta_sqrt1.len());

    let [two, three, four, five, six, seven, eight] = [F::from(2u64), F::from(3u64), F::from(4u64), F::from(5u64), F::from(6u64), F::from(7u64), F::from(8u64)];

    // Pre-compute evaluations for beta and beta_sqrt
    let beta_evals: Vec<[F; COMBINED_QUADRATIC_ERROR_FULL_LEN]> = beta0
        .iter()
        .zip(beta1)
        .map(|(&b0, &b1)| {
            [b1, b1 + b0, b1 + b0 * two, b1 + b0 * three, b1 + b0 * four, b1 + b0 * five, b1 + b0 * six, b1 + b0 * seven, b1 + b0 * eight]
        })
        .collect();

    let beta_sqrt_evals: Vec<[F; COMBINED_QUADRATIC_ERROR_FULL_LEN]> = beta_sqrt0
        .iter()
        .zip(beta_sqrt1)
        .map(|(&bs0, &bs1)| {
            [bs1, bs1 + bs0, bs1 + bs0 * two, bs1 + bs0 * three, bs1 + bs0 * four, bs1 + bs0 * five, bs1 + bs0 * six, bs1 + bs0 * seven, bs1 + bs0 * eight]
        })
        .collect();

    let beta_evals_len = beta_evals.len();
    beta_sqrt_evals.par_chunks(16)
        .flat_map_iter(|bs_chunk| {
            let mut local_result = Vec::with_capacity(beta_evals_len * bs_chunk.len());
            bs_chunk.iter().for_each(|bs_eval| {
                beta_evals.iter().for_each(|b_eval| {
                    local_result.push(CombinedQuadraticErrorFull {
                        evals: [
                            b_eval[0] * bs_eval[0],
                            b_eval[1] * bs_eval[1],
                            b_eval[2] * bs_eval[2],
                            b_eval[3] * bs_eval[3],
                            b_eval[4] * bs_eval[4],
                            b_eval[5] * bs_eval[5],
                            b_eval[6] * bs_eval[6],
                            b_eval[7] * bs_eval[7],
                            b_eval[8] * bs_eval[8],
                        ],
                    });
                });
            });
            local_result
        })
        .collect()
}

pub fn evaluate_betas_selectorwise<F: PrimeField>(
    betas: &[F],
    betas_sqrt: &[F],
) -> Vec<F> {
    assert_eq!(betas.len(), betas_sqrt.len());

    let beta_len = betas.len();
    let beta_sqrt_len = betas_sqrt.len();
    let total_len = beta_len * beta_sqrt_len;
    // Use a single parallel iterator over all combinations
    (0..total_len)
        .into_par_iter()
        .map(|i| {
            let beta_idx = i % beta_len;
            let beta_sqrt_idx = i / beta_len;
            betas[beta_idx] * betas_sqrt[beta_sqrt_idx]
        })
        .collect()
}

pub fn evaluate_betas_error_selectorwise_full<F: PrimeField>(
    beta0: &[F],
    beta1: &[F],
    beta_sqrt0: &[F],
    beta_sqrt1: &[F],
) -> Vec<CombinedQuadraticErrorFull<F>> {
    assert_eq!(beta0.len(), beta1.len());
    assert_eq!(beta_sqrt0.len(), beta_sqrt1.len());

    let [two, three, four, five, six, seven, eight] = [F::from(2u64), F::from(3u64), F::from(4u64), F::from(5u64), F::from(6u64), F::from(7u64), F::from(8u64)];

    // Pre-compute evaluations for beta and beta_sqrt
    let beta_evals: Vec<[F; 9]> = beta0
        .par_iter()
        .zip(beta1)
        .map(|(&b0, &b1)| {
            let addend = b0;
            [b1, b1 + addend, b1 + addend * two, b1 + addend * three, b1 + addend * four, b1 + addend * five, b1 + addend * six, b1 + addend * seven, b1 + addend * eight]
        })
        .collect();

    let beta_sqrt_evals: Vec<[F; 9]> = beta_sqrt0
        .par_iter()
        .zip(beta_sqrt1)
        .map(|(&bs0, &bs1)| {
            let addend = bs0;
            [bs1, bs1 + addend, bs1 + addend * two, bs1 + addend * three, bs1 + addend * four, bs1 + addend * five, bs1 + addend * six, bs1 + addend * seven, bs1 + addend * eight]
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
                    b_eval[7] * bs_eval[7],
                    b_eval[8] * bs_eval[8],
                ],
            }
        })
        .collect()
}

pub fn evaluate_betas_error_selectorwise_full_sha256<F: PrimeField>(
    beta0: &[F],
    beta1: &[F],
    beta_sqrt0: &[F],
    beta_sqrt1: &[F],
) -> Vec<CombinedQuadraticErrorFullSha256<F>> {
    assert_eq!(beta0.len(), beta1.len());
    assert_eq!(beta_sqrt0.len(), beta_sqrt1.len());

    let [two, three, four, five, six, seven, eight, nine, ten] = [F::from(2u64), F::from(3u64), F::from(4u64), F::from(5u64), F::from(6u64), F::from(7u64), F::from(8u64), F::from(9u64), F::from(10u64)];

    // Pre-compute evaluations for beta and beta_sqrt
    let beta_evals: Vec<[F; 11]> = beta0
        .par_iter()
        .zip(beta1)
        .map(|(&b0, &b1)| {
            let addend = b0;
            [b1, b1 + addend, b1 + addend * two, b1 + addend * three, b1 + addend * four, b1 + addend * five, b1 + addend * six, b1 + addend * seven, b1 + addend * eight, b1 + addend * nine, b1 + addend * ten]
        })
        .collect();

    let beta_sqrt_evals: Vec<[F; 11]> = beta_sqrt0
        .par_iter()
        .zip(beta_sqrt1)
        .map(|(&bs0, &bs1)| {
            let addend = bs0;
            [bs1, bs1 + addend, bs1 + addend * two, bs1 + addend * three, bs1 + addend * four, bs1 + addend * five, bs1 + addend * six, bs1 + addend * seven, bs1 + addend * eight, bs1 + addend * nine, bs1 + addend * ten]
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

            CombinedQuadraticErrorFullSha256 {
                evals: [
                    b_eval[0] * bs_eval[0],
                    b_eval[1] * bs_eval[1],
                    b_eval[2] * bs_eval[2],
                    b_eval[3] * bs_eval[3],
                    b_eval[4] * bs_eval[4],
                    b_eval[5] * bs_eval[5],
                    b_eval[6] * bs_eval[6],
                    b_eval[7] * bs_eval[7],
                    b_eval[8] * bs_eval[8],
                    b_eval[9] * bs_eval[9],
                    b_eval[10] * bs_eval[10],
                ],
            }
        })
        .collect()
}

pub fn evaluate_betas_error_selectorwise_full_chunks<F: PrimeField>(
    beta0: &[F],
    beta1: &[F],
    beta_sqrt0: &[F],
    beta_sqrt1: &[F],
) -> Vec<CombinedQuadraticErrorFull<F>> {
    assert_eq!(beta0.len(), beta1.len());
    assert_eq!(beta_sqrt0.len(), beta_sqrt1.len());

    let [two, three, four, five, six, seven, eight] = [F::from(2u64), F::from(3u64), F::from(4u64), F::from(5u64), F::from(6u64), F::from(7u64), F::from(8u64)];

    // Pre-compute in parallel with larger chunks
    let chunk_size_evals = div_ceil(beta0.len(), num_threads());
    let beta_evals: Vec<[F; 9]> = beta0.par_chunks(chunk_size_evals)
        .zip(beta1.par_chunks(chunk_size_evals))
        .flat_map(|(b0_chunk, b1_chunk)| {
            b0_chunk.iter().zip(b1_chunk).map(|(&b0, &b1)| {
                let addend = b0;
                [b1, b1 + addend, b1 + addend * two, b1 + addend * three, 
                 b1 + addend * four, b1 + addend * five, b1 + addend * six, 
                 b1 + addend * seven, b1 + addend * eight]
            }).collect::<Vec<_>>()
        })
        .collect();

    let beta_sqrt_evals: Vec<[F; 9]> = beta_sqrt0.par_chunks(chunk_size_evals)
        .zip(beta_sqrt1.par_chunks(chunk_size_evals))
        .flat_map(|(bs0_chunk, bs1_chunk)| {
            bs0_chunk.iter().zip(bs1_chunk).map(|(&bs0, &bs1)| {
                let addend = bs0;
                [bs1, bs1 + addend, bs1 + addend * two, bs1 + addend * three,
                 bs1 + addend * four, bs1 + addend * five, bs1 + addend * six,
                 bs1 + addend * seven, bs1 + addend * eight]
            }).collect::<Vec<_>>()
        })
        .collect();

    let beta_evals_len = beta_evals.len();
    let beta_sqrt_evals_len = beta_sqrt_evals.len();
    let total_len = beta_evals_len * beta_sqrt_evals_len;

    let chunk_size = div_ceil(total_len, num_threads());
    (0..total_len).into_par_iter()
        .chunks(chunk_size)
        .map(|chunk| {
            chunk.iter().map(|&i| {
                let b_idx = i % beta_evals_len;
                let bs_idx = i / beta_evals_len;
                let b_eval = &beta_evals[b_idx];
                let bs_eval = &beta_sqrt_evals[bs_idx];

                CombinedQuadraticErrorFull {
                    evals: [
                        b_eval[0] * bs_eval[0],
                        b_eval[1] * bs_eval[1],
                        b_eval[2] * bs_eval[2],
                        b_eval[3] * bs_eval[3],
                        b_eval[4] * bs_eval[4],
                        b_eval[5] * bs_eval[5],
                        b_eval[6] * bs_eval[6],
                        b_eval[7] * bs_eval[7],
                        b_eval[8] * bs_eval[8],
                    ]
                }
            }).collect::<Vec<_>>()
        })
        .flatten()
        .collect()
}

/// Represents a polynomial evaluated over the integers 0,1,...,d.
#[derive(Clone, Debug)]
pub struct EvaluatedError<F> {
    pub evals: Vec<F>,
}

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
        let mut curr = eval1;
        let add = eval0;
        for eval in self.evals.iter_mut() {
            *eval = curr;
            curr += add;
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

// Given a polynomial p(X) of degree d > 1, compute its quotient q(X)
// such that p(X) = (1-X)X⋅q(X).
// Panics if deg(p) ≤ 1 or if p(0) ≠ 0 or p(1) ≠ 0
pub fn quotient_by_boolean_vanishing<F: Field>(poly: &[F]) -> Vec<F> {
    let n = poly.len();
    assert!(n >= 2, "deg(poly) < 2");
    assert!(poly[0].is_zero_vartime(), "poly(0) != 0");

    let mut tmp = F::ZERO;

    let mut quotient = vec![F::ZERO; n - 2];
    for i in 0..(n - 2) {
        tmp += poly[i + 1];
        quotient[i] = tmp;
    }

    // p(1) = ∑p_i = 0
    assert_eq!(
        *quotient.last().unwrap(),
        poly.last().unwrap().neg(),
        "poly(1) != 0"
    );
    quotient
}

/// This evaluates a provided polynomial (in coefficient form) at `point`.
pub fn eval_polynomial<F: Field>(poly: &[F], point: F) -> F {
    fn evaluate<F: Field>(poly: &[F], point: F) -> F {
        poly.iter()
            .rev()
            .fold(F::ZERO, |acc, coeff| acc * point + coeff)
    }
    let n = poly.len();
    let num_threads = rayon::current_num_threads();
    if n * 2 < num_threads {
        evaluate(poly, point)
    } else {
        let chunk_size = (n + num_threads - 1) / num_threads;
        let mut parts = vec![F::ZERO; num_threads];
        rayon::scope(|scope| {
            for (chunk_idx, (out, poly)) in
                parts.chunks_mut(1).zip(poly.chunks(chunk_size)).enumerate()
            {
                scope.spawn(move |_| {
                    let start = chunk_idx * chunk_size;
                    out[0] = evaluate(poly, point) * point.pow_vartime(&[start as u64, 0, 0, 0]);
                });
            }
        });
        parts.iter().fold(F::ZERO, |acc, coeff| acc + coeff)
    }
}

/// This evaluates a provided polynomial (in coefficient form) at `point`.
pub fn multiply_polynomial<F: Field>(poly: &[F], point: F) -> F {
    fn evaluate<F: Field>(poly: &[F], point: F) -> F {
        poly.iter()
            .rev()
            .fold(F::ZERO, |acc, coeff| acc * point + coeff)
    }
    let n = poly.len();
    let num_threads = rayon::current_num_threads();
    if n * 2 < num_threads {
        evaluate(poly, point)
    } else {
        let chunk_size = (n + num_threads - 1) / num_threads;
        let mut parts = vec![F::ZERO; num_threads];
        rayon::scope(|scope| {
            for (chunk_idx, (out, poly)) in
                parts.chunks_mut(1).zip(poly.chunks(chunk_size)).enumerate()
            {
                scope.spawn(move |_| {
                    let start = chunk_idx * chunk_size;
                    out[0] = evaluate(poly, point) * point.pow_vartime(&[start as u64, 0, 0, 0]);
                });
            }
        });
        parts.iter().fold(F::ZERO, |acc, coeff| acc + coeff)
    }
}

pub fn build_m<F: PrimeField>(
    lookup: &Vec<(plonk::Expression<F>, plonk::Expression<F>)>,
    tables_len: usize,
    lookup_witness_len: usize,
    selectors: &[&[F]],
    fixed: &[&[F]],
    instance: &[&[F]],
    advice: &[&[F]],
    challenges: &[F],
) -> Vec<F> {
    let mut row_evals_repr: Vec<u8> = Vec::new();

    let mut map = HashMap::<Vec<u8>, usize>::new();

    for row_idx in 0..tables_len {
        row_evals_repr.clear();

        for (_, table_expr) in lookup {
            let eval = evaluate(
                row_idx, table_expr, selectors, fixed, instance, advice, challenges,
            );
            row_evals_repr.extend(eval.to_repr().as_ref().iter());
        }

        map.insert(row_evals_repr.clone(), row_idx);
    }

    let mut m = vec![F::ZERO; tables_len];

    for row_idx in 0..lookup_witness_len {
        row_evals_repr.clear();

        for (input_expr, _) in lookup {
            let eval = evaluate(
                row_idx, input_expr, selectors, fixed, instance, advice, challenges,
            );
            row_evals_repr.extend(eval.to_repr().as_ref().iter());
        }

        if let Some(index) = map.get(&row_evals_repr) {
            m[*index] += F::ONE;
        }
    }

    m
}

pub fn build_g<F: PrimeField>(
        lookup: &Vec<(plonk::Expression<F>, plonk::Expression<F>)>,
        usable_rows: &Range<usize>,
        num_rows: usize,
        selectors: &[&[F]],
        fixed: &[&[F]],
        instance: &[&[F]],
        advice: &[&[F]],
        challenges: &[F],
        m: &[F],
        thetas: &[F],
        r: F,
    ) -> Vec<F> {
        let mut g = vec![F::ZERO; num_rows];
        let table_exprs = lookup.iter().map(|(table_expr, _)| table_expr.clone()).collect_vec();
        for row_idx in usable_rows.clone() {
            g[row_idx] = evaluate_linear_combination(
                row_idx,
                &table_exprs,
                thetas,
                selectors,
                fixed,
                instance,
                advice,
                challenges,
            ) + r;
        }

        g.iter_mut().batch_invert();

        for row_idx in usable_rows.clone() {
            g[row_idx] *= m[row_idx];
        }
        g
    }

pub fn build_h<F: PrimeField>(
        lookup: &Vec<(plonk::Expression<F>, plonk::Expression<F>)>,
        usable_rows: &Range<usize>,
        num_rows: usize,
        selectors: &[&[F]],
        fixed: &[&[F]],
        instance: &[&[F]],
        advice: &[&[F]],
        challenges: &[F],
        thetas: &[F],
        r: F,
    ) -> Vec<F> {
        let mut h = vec![F::ZERO; num_rows];
        let input_exprs = lookup.iter().map(|(input_expr, _)| input_expr.clone()).collect_vec();
        for row_idx in usable_rows.clone() {
            h[row_idx] = evaluate_linear_combination(
                row_idx,
                &input_exprs,
                thetas,
                selectors,
                fixed,
                instance,
                advice,
                challenges,
            ) + r;
        }

        h.iter_mut().batch_invert();
        h
    }

pub fn evaluate_linear_combination<F: Field>(
    row_idx: usize,
    exprs: &[plonk::Expression<F>],
    coeffs: &[F],
    selectors: &[&[F]],
    fixed: &[&[F]],
    instance: &[&[F]],
    advice: &[&[F]],
    challenges: &[F],
) -> F {
    zip(exprs.iter(), coeffs.iter()).fold(F::ZERO, |acc, (expr, coeff)| {
        acc + evaluate(
            row_idx, expr, selectors, fixed, instance, advice, challenges,
        ) * coeff
    })
}

pub fn evaluate<F: Field>(
    row_idx: usize,
    //num_rows: usize,
    expr: &plonk::Expression<F>,
    selectors: &[&[F]],
    fixed: &[&[F]],
    instance: &[&[F]],
    advice: &[&[F]],
    challenges: &[F],
) -> F {
    //let num_rows_i = num_rows as i32;
    expr.evaluate(
        &|_| F::ONE,
        &|constant| constant,
        &|selector_column| selectors[selector_column.index()][row_idx],
        &|query| {
            let fixed_len = fixed[query.column_index()].len() as i32;
            if row_idx > fixed_len as usize {
                fixed[query.column_index()][get_rotation_idx(row_idx, query.rotation(), fixed_len)]
            } else {
                F::ZERO
            }
        },
        &|query| {
            let advice_len = advice[query.column_index()].len() as i32;
            if row_idx > advice_len as usize {
                advice[query.column_index()][get_rotation_idx(row_idx, query.rotation(), advice_len)]
            } else {
                F::ZERO
            }
        },
        &|query| {
            let instance_len = instance[query.column_index()].len() as i32;
            if row_idx > instance_len as usize {
                instance[query.column_index()][get_rotation_idx(row_idx, query.rotation(), instance_len)]
            } else {
                F::ZERO
            }
        },
        &|challenge| challenges[challenge.index()],
        &|v| -v,
        &|v1, v2| v1 + v2,
        &|v1, v2| v1 * v2,
        &|v, c| v * c,
    )
}

/// Return the index in the polynomial of size `isize` after rotation `rot`.
fn get_rotation_idx(idx: usize, rot: Rotation, isize: i32) -> usize {
    (((idx as i32) + rot.0).rem_euclid(isize)) as usize
}
