use halo2_proofs::{arithmetic::Field, plonk};
use rayon::prelude::*;
use crossbeam::{scope, thread};
use std::{borrow::Cow, hash::Hash, iter, sync::{Arc, Mutex}};

use crate::{
    accumulation::protostar::{ivc::halo2::chips::main_chip::LOOKUP_BITS, ProtostarAccumulator}, backend::hyperplonk::prover::instance_polys, frontend::halo2::convert_expression, pcs::PolynomialCommitmentScheme, poly::{multilinear::MultilinearPolynomial, Polynomial}, util::{
        arithmetic::{div_ceil, powers, repeat_elements, repeat_vector, sum, BatchInvert, BooleanHypercube, PrimeField}, expression::{Expression, Rotation}, expression_new::paired::eval_polynomial, izip, izip_eq, parallel::{num_threads, par_map_collect, parallelize, parallelize_iter}, Itertools
    }
};

pub fn expand_beta_polys<F: Field>(
    beta_polys: &[(&[F], &[F])],
    expansion_factor: usize,
) -> (
    Box<[MultilinearPolynomial<F>]>,
    Box<[MultilinearPolynomial<F>]>,
) {
    // Expand beta_polys using repeat_vector
    let beta_polys_owned: Box<[MultilinearPolynomial<F>]> = vec![
        MultilinearPolynomial::new(repeat_vector(beta_polys[0].0, expansion_factor)),
        MultilinearPolynomial::new(repeat_vector(beta_polys[1].0, expansion_factor)),
    ]
    .into_boxed_slice();

    // Expand beta_prime_polys using repeat_elements
    let beta_prime_polys_owned: Box<[MultilinearPolynomial<F>]> = vec![
        MultilinearPolynomial::new(repeat_elements(beta_polys[0].1, expansion_factor)),
        MultilinearPolynomial::new(repeat_elements(beta_polys[1].1, expansion_factor)),
    ]
    .into_boxed_slice();

    (beta_polys_owned, beta_prime_polys_owned)
}

pub struct PolynomialsRefsHolder<F> {
    polys: [MultilinearPolynomial<F>; 2],
}

impl<F: PrimeField> PolynomialsRefsHolder<F> {
    pub fn new(polys: [MultilinearPolynomial<F>; 2]) -> Self {
        PolynomialsRefsHolder { polys }
    }

    pub fn get_polys_refs(&self) -> [&MultilinearPolynomial<F>; 2] {
        [&self.polys[0], &self.polys[1]]
    }
}

pub struct PolynomialsHolder<F> {
    beta_polys: [MultilinearPolynomial<F>; 2],
    beta_prime_polys: [MultilinearPolynomial<F>; 2],
}

impl<F: PrimeField> PolynomialsHolder<F> {
    pub fn new(num_vars: usize, zeta_values: [F; 2]) -> Self {
        let (beta_polys, beta_prime_polys) = {
            let (beta_poly0, beta_prime_poly0) = powers_of_zeta_sqrt_poly_full(num_vars/2, zeta_values[0]);
            let (beta_poly1, beta_prime_poly1) = powers_of_zeta_sqrt_poly_full(num_vars/2, zeta_values[1]);
            ([beta_poly0, beta_poly1], [beta_prime_poly0, beta_prime_poly1])
        };
        PolynomialsHolder { beta_polys, beta_prime_polys }
    }

    pub fn get_polys_refs(&self) -> ([&MultilinearPolynomial<F>; 2], [&MultilinearPolynomial<F>; 2]) {
        ([&self.beta_polys[0], &self.beta_polys[1]], [&self.beta_prime_polys[0], &self.beta_prime_polys[1]])
    }
}

pub(crate) fn lookup_h_polys<F: PrimeField + Hash>(
    compressed_polys: &[[MultilinearPolynomial<F>; 2]],
    m_polys: &[MultilinearPolynomial<F>],
    beta: &F,
) -> Vec<[MultilinearPolynomial<F>; 2]> {
    compressed_polys
        .iter()
        .zip(m_polys.iter())
        .map(|(compressed_polys, m_poly)| lookup_h_poly(compressed_polys, m_poly, beta))
        .collect()
}

fn lookup_h_poly<F: PrimeField + Hash>(
    compressed_polys: &[MultilinearPolynomial<F>; 2],
    m_poly: &MultilinearPolynomial<F>,
    beta: &F,
) -> [MultilinearPolynomial<F>; 2] {
    let [input, table] = compressed_polys;
    let mut h_input = vec![F::ZERO; 1 << input.num_vars()];
    let mut h_table = vec![F::ZERO; 1 << table.num_vars()];

    parallelize(&mut h_input, |(h_input, start)| {
        for (h_input, input) in h_input.iter_mut().zip(input[start..].iter()) {
            *h_input = *beta + input;
        }
    });
    parallelize(&mut h_table, |(h_table, start)| {
        for (h_table, table) in h_table.iter_mut().zip(table[start..].iter()) {
            *h_table = *beta + table;
        }
    });

    let chunk_size = div_ceil(2 * h_input.len(), num_threads());
    parallelize_iter(
        iter::empty()
            .chain(h_input.chunks_mut(chunk_size))
            .chain(h_table.chunks_mut(chunk_size)),
        |h| {
            h.iter_mut().batch_invert();
        },
    );

    parallelize(&mut h_table, |(h_table, start)| {
        for (h_table, m) in h_table.iter_mut().zip(m_poly[start..].iter()) {
            *h_table *= m;
        }
    });

    if cfg!(feature = "sanity-check") {
        assert_eq!(sum::<F>(&h_input), sum::<F>(&h_table));
    }

    [
        MultilinearPolynomial::new(h_input),
        MultilinearPolynomial::new(h_table),
    ]
}

pub fn powers_of_zeta_poly<F: PrimeField>(
    num_vars: usize,
    zeta: F,
) -> MultilinearPolynomial<F> {
    let powers_of_zeta = powers(zeta).take(1 << num_vars).collect_vec();
    let nth_map = (0..1 << num_vars).collect_vec();
    MultilinearPolynomial::new(par_map_collect(&nth_map, |b| powers_of_zeta[*b]))
}

pub fn powers_of_zeta_sqrt_poly<F: PrimeField>(
    num_vars: usize,
    zeta: F,
) -> MultilinearPolynomial<F> {
    let lsqrt = 1 << (num_vars/2);
    let zeta_pow_lsqrt = zeta.pow([lsqrt as u64]);
    let powers_of_zeta = powers(zeta).take(lsqrt).collect_vec();
    let powers_of_zeta_sqrt = powers(zeta_pow_lsqrt).take(lsqrt).collect_vec();
    MultilinearPolynomial::new(powers_of_zeta.into_iter().chain(powers_of_zeta_sqrt).collect_vec())    
}

pub fn powers_of_zeta_sqrt_poly_ec<F: PrimeField>(
    num_vars: usize,
    zeta: F,
) -> MultilinearPolynomial<F> {
    let lsqrt = 1 << (num_vars/2);
    let zeta_pow_lsqrt = zeta.pow([lsqrt as u64]);
    let powers_of_zeta = powers(zeta).take(lsqrt).collect_vec();
    let powers_of_zeta_sqrt = powers(zeta_pow_lsqrt).take(lsqrt).collect_vec();
    MultilinearPolynomial::new(powers_of_zeta.into_iter().chain(powers_of_zeta_sqrt).collect_vec())    
}

pub fn powers_of_zeta_sqrt_poly_full<F: PrimeField>(
    num_vars: usize,
    zeta: F,
) -> (MultilinearPolynomial<F>, MultilinearPolynomial<F>) {
    let zeta_pow_lsqrt = zeta.pow([num_vars as u64]);
    let powers_of_zeta = powers(zeta).take(1 << num_vars).collect_vec();
    let powers_of_zeta_sqrt = powers(zeta_pow_lsqrt).take(1 << num_vars).collect_vec();
    (MultilinearPolynomial::new(powers_of_zeta), MultilinearPolynomial::new(powers_of_zeta_sqrt))
}

pub(crate) fn evaluate_zeta_sqrt_cross_term_poly<F, Pcs>(
    num_vars: usize,
    accumulator: &ProtostarAccumulator<F, Pcs>,
    incoming: &ProtostarAccumulator<F, Pcs>,
) -> MultilinearPolynomial<F>
where
    F: PrimeField,
    Pcs: PolynomialCommitmentScheme<F, Polynomial = MultilinearPolynomial<F>>,
{
    let lsqrt = 1 << (num_vars/2);
    let [(acc_pow, acc_pow_sqrt, acc_zeta, acc_zeta_sqrt, acc_u), (incoming_pow, incoming_pow_sqrt, incoming_zeta, incoming_zeta_sqrt, incoming_u)] =
        [accumulator, incoming].map(|witness| {
            let pow = witness.witness_polys.last().unwrap();
            let (pow_poly, pow_sqrt_poly) = pow.evals().split_at(lsqrt);
            let zeta = witness
                .instance
                .challenges
                .last()
                .unwrap();
            let zeta_sqrt = zeta.pow([lsqrt as u64]);
            (pow_poly, pow_sqrt_poly, zeta, zeta_sqrt, witness.instance.u)
        });
    assert_eq!(incoming_u, F::ONE);

    let mut cross_term = vec![F::ZERO; lsqrt];        
    let mut cross_term_sqrt = vec![F::ZERO; lsqrt];
    let next_map = (0..lsqrt).collect_vec();
    parallelize(&mut cross_term, |(cross_term, start)| {
        cross_term
            .iter_mut()
            .zip(start..)
            .for_each(|(cross_term, b)| {
                *cross_term = - acc_pow[next_map[b]] - acc_u * incoming_pow[next_map[b]]
                    + (acc_pow[b] * incoming_zeta + incoming_pow[b] * acc_zeta);
            })
    });
    let b_0 = 0;
    let b_last = *next_map.last().unwrap();
    cross_term[b_0] += - acc_pow[b_0] * incoming_zeta - incoming_pow[b_0] * acc_zeta + acc_u.double();
    cross_term[b_last] += - acc_pow[b_last] * incoming_zeta - incoming_pow[b_last] * acc_zeta
        + acc_u * incoming_zeta
        + acc_zeta;

    parallelize(&mut cross_term_sqrt, |(cross_term_sqrt, start)| {
        cross_term_sqrt
            .iter_mut()
            .zip(start..)
            .for_each(|(cross_term_sqrt, b)| {
                *cross_term_sqrt = acc_pow_sqrt[next_map[b]] + acc_u * incoming_pow_sqrt[next_map[b]]
                    - (acc_pow_sqrt[b] * incoming_zeta_sqrt + incoming_pow_sqrt[b] * acc_zeta_sqrt);
            })
    });

    cross_term_sqrt[b_0] += acc_pow_sqrt[b_0] * incoming_zeta_sqrt + incoming_pow_sqrt[b_0] * acc_zeta_sqrt - acc_u.double();
    cross_term_sqrt[b_last] += acc_pow_sqrt[b_last] * incoming_zeta_sqrt + incoming_pow_sqrt[b_last] * acc_zeta_sqrt
        - acc_u * incoming_zeta_sqrt
        - acc_zeta_sqrt;

    MultilinearPolynomial::new(cross_term.into_iter().chain(cross_term_sqrt).collect_vec())
}