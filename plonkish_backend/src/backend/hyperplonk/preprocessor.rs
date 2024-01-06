use generic_array::typenum::Exp;

use crate::{
    backend::PlonkishCircuitInfo,
    poly::{Polynomial, multilinear::MultilinearPolynomial},
    util::{
        arithmetic::{div_ceil, steps, PrimeField},
        chain,
        expression::{Expression, Query, Rotation},
        Itertools,
    },
};
use std::{array, borrow::Cow, iter, mem};

pub(super) fn batch_size<F: PrimeField>(circuit_info: &PlonkishCircuitInfo<F>) -> usize {
    let num_lookups = circuit_info.lookups.len();
    let num_permutation_polys = circuit_info.permutation_polys().len();
    chain![
        [circuit_info.preprocess_polys.len() + circuit_info.permutation_polys().len()],
        circuit_info.num_witness_polys.clone(),
        [num_lookups],
        [num_lookups + div_ceil(num_permutation_polys, max_degree(circuit_info, None) - 1)],
    ]
    .sum()
}

pub(super) fn compose<F: PrimeField>(
    circuit_info: &PlonkishCircuitInfo<F>,
) -> (usize, Expression<F>) {
    let challenge_offset = circuit_info.num_challenges.iter().sum::<usize>();
    let [beta, gamma, alpha] =
        &array::from_fn(|idx| Expression::<F>::Challenge(challenge_offset + idx));

    let (lookup_constraints, lookup_zero_checks) = lookup_constraints(circuit_info, beta, gamma);

    let max_degree = max_degree(circuit_info, Some(&lookup_constraints));
    let (num_permutation_z_polys, permutation_constraints) = permutation_constraints(
        circuit_info,
        max_degree,
        beta,
        gamma,
        2 * circuit_info.lookups.len(),
        None,
    );

    let expression = {
        let constraints = iter::empty()
            .chain(circuit_info.constraints.iter())
            .chain(lookup_constraints.iter())
            .chain(permutation_constraints.iter())
            .collect_vec();
        let eq = Expression::eq_xy(0);
        let zero_check_on_every_row = Expression::distribute_powers(constraints, alpha) * eq;
        Expression::distribute_powers(
            iter::empty()
                .chain(lookup_zero_checks.iter())
                .chain(Some(&zero_check_on_every_row)),
            alpha,
        )
    };

    (num_permutation_z_polys, expression)
}

pub(super) fn max_degree<F: PrimeField>(
    circuit_info: &PlonkishCircuitInfo<F>,
    lookup_constraints: Option<&[Expression<F>]>,
) -> usize {
    let lookup_constraints = lookup_constraints.map(Cow::Borrowed).unwrap_or_else(|| {
        let dummy_challenge = Expression::zero();
        Cow::Owned(self::lookup_constraints(circuit_info, &dummy_challenge, &dummy_challenge).0)
    });
    iter::empty()
        .chain(circuit_info.constraints.iter().map(Expression::degree))
        .chain(lookup_constraints.iter().map(Expression::degree))
        .chain(circuit_info.max_degree)
        .chain(Some(2))
        .max()
        .unwrap()
}

pub(super) fn lookup_constraints<F: PrimeField>(
    circuit_info: &PlonkishCircuitInfo<F>,
    beta: &Expression<F>,
    gamma: &Expression<F>,
) -> (Vec<Expression<F>>, Vec<Expression<F>>) {
    let m_offset = circuit_info.num_poly() + circuit_info.permutation_polys().len();
    let h_offset = m_offset + circuit_info.lookups.len();
    let constraints = circuit_info
        .lookups
        .iter()
        .zip(m_offset..)
        .zip(h_offset..)
        .flat_map(|((lookup, m), h)| {
            let [m, h] = &[m, h]
                .map(|poly| Query::new(poly, Rotation::cur()))
                .map(Expression::<F>::Polynomial);
            let (inputs, tables) = lookup
                .iter()
                .map(|(input, table)| (input, table))
                .unzip::<_, _, Vec<_>, Vec<_>>();
            let input = &Expression::distribute_powers(inputs, beta);
            let table = &Expression::distribute_powers(tables, beta);
            [h * (input + gamma) * (table + gamma) - (table + gamma) + m * (input + gamma)]
        })
        .collect_vec();
    let sum_check = (h_offset..)
        .take(circuit_info.lookups.len())
        .map(|h| Query::new(h, Rotation::cur()).into())
        .collect_vec();
    (constraints, sum_check)
}

pub(crate) fn permutation_constraints<F: PrimeField>(
    circuit_info: &PlonkishCircuitInfo<F>,
    max_degree: usize,
    beta: &Expression<F>,
    gamma: &Expression<F>,
    num_builtin_witness_polys: usize,
    u: Option<usize>,
) -> (usize, Vec<Expression<F>>) {
    let permutation_polys = circuit_info.permutation_polys();
    let chunk_size = max_degree - 1;
    let num_chunks = div_ceil(permutation_polys.len(), chunk_size);
    let permutation_offset = circuit_info.num_poly();
    let z_offset = permutation_offset + permutation_polys.len() + num_builtin_witness_polys;
    let u =  Expression::<F>::Challenge(u.unwrap_or(0));
    let fixed_permutation_idx_for_permutation_constraints = circuit_info.fixed_permutation_idx_for_permutation_constraints.clone();
    let polys = permutation_polys
        .iter()
        .map(|idx| {
            if fixed_permutation_idx_for_permutation_constraints.contains(idx) {
                u.clone() * Expression::Polynomial(Query::new(*idx, Rotation::cur()))
            } else {
                Expression::Polynomial(Query::new(*idx, Rotation::cur()))
            }
        })
        .collect_vec();    
    let ids = (0..polys.len())
        .map(|idx| {
            let offset = F::from((idx << circuit_info.k) as u64);
            Expression::Constant(offset) + Expression::identity()
        })
        .collect_vec();
    let permutations = (permutation_offset..)
        .map(|idx| Expression::Polynomial(Query::new(idx, Rotation::cur())))
        .take(permutation_polys.len())
        .collect_vec();
    let zs = (z_offset..)
        .map(|idx| Expression::Polynomial(Query::new(idx, Rotation::cur())))
        .take(num_chunks)
        .collect_vec();
    let z_0_next = Expression::<F>::Polynomial(Query::new(z_offset, Rotation::next()));
    let l_1 = &Expression::<F>::lagrange(1);
    let l_0 = &Expression::<F>::lagrange(0);
    let one = &Expression::one();
    let constraints = iter::empty()
        .chain(zs.first().map(|z_0| l_1 * (z_0 - one)))
        .chain(
            polys
                .chunks(chunk_size)
                .zip(ids.chunks(chunk_size))
                .zip(permutations.chunks(chunk_size))
                .zip(zs.iter())
                .zip(zs.iter().skip(1).chain(Some(&z_0_next)))
                .map(|((((polys, ids), permutations), z_lhs), z_rhs)| {
                    z_lhs
                        * polys
                            .iter()
                            .zip(ids)
                            .map(|(poly, id)| poly + beta * id + gamma)
                            .product::<Expression<_>>()
                        - z_rhs
                            * polys
                                .iter()
                                .zip(permutations)
                                .map(|(poly, permutation)| poly + beta * permutation + gamma)
                                .product::<Expression<_>>()
                }),
        )
        .collect();
    (num_chunks, constraints)
}

pub(super) fn permutation_polys<F: PrimeField>(
    num_vars: usize,
    permutation_polys: &[usize],
    cycles: &[Vec<(usize, usize)>],
) -> Vec<MultilinearPolynomial<F>> {
    let poly_index = {
        let mut poly_index = vec![0; permutation_polys.last().map(|poly| 1 + poly).unwrap_or(0)];
        for (idx, poly) in permutation_polys.iter().enumerate() {
            poly_index[*poly] = idx;
        }
        poly_index
    };
    let mut permutations = (0..permutation_polys.len() as u64)
        .map(|idx| {
            steps(F::from(idx << num_vars))
                .take(1 << num_vars)
                .collect_vec()
        })
        .collect_vec();
    for cycle in cycles.iter() {
        let (i0, j0) = cycle[0];
        let mut last = permutations[poly_index[i0]][j0];
        for &(i, j) in cycle.iter().cycle().skip(1).take(cycle.len()) {
            // todo this gives error for multiple advice colns, maybe axiom api doing split and copying gates is causing this
            assert_ne!(j, 0);
            mem::swap(&mut permutations[poly_index[i]][j], &mut last);
        }
    }
    permutations
        .into_iter()
        .map(MultilinearPolynomial::new)
        .collect()

}