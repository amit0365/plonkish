use std::{iter::zip, marker::PhantomData};

use crate::util::{arithmetic::Field, expression::Rotation, izip, Deserialize, Itertools, Serialize};
use halo2_proofs::plonk::{self, Expression};

//use halo2curves::CurveAffine;
// use crate::{
//     poly::{Basis, LagrangeCoeff, Polynomial},
// };
// accumulator::Accumulator, ProvingKey,

use super::{ QueriedExpression, QueryType};


/// Used to store references of the variables referenced by an expression.
/// TODO: Merge with Verifier and Prover accumulator
pub struct Data<T: QueryType> {
    pub fixed: Vec<T::Fixed>,
    pub selectors: Vec<T::Fixed>,
    pub instance: Vec<T::Witness>,
    pub advice: Vec<T::Witness>,
    pub challenges: Vec<T::Challenge>,
    pub acc_u: Vec<T::AccU>,
    pub beta_polys: T::Witness,
    pub beta_prime_polys: T::Witness,
    pub lookups: Vec<LookupData<T>>,
    pub ys: Vec<T::Challenge>,
}

pub struct LookupData<T: QueryType> {
    pub m: T::Witness,
    pub g: T::Witness,
    pub h: T::Witness,
    pub thetas: Vec<T::Challenge>,
    pub r: T::Challenge,
}

impl<T: QueryType> LookupData<T> {
    pub fn new(lookups_polys: Vec<T::Witness>, thetas: Vec<T::Challenge>, r: T::Challenge) -> Self {
        let m = lookups_polys[0];
        let h = lookups_polys[1];
        let g = lookups_polys[2];
        LookupData { m, g, h, thetas, r }
    }
}

impl<T: QueryType> Data<T> {
    pub fn all_constraints(
        &self,
        gate_expressions: Vec<plonk::Expression<T::F>>,
        lookup_expressions: Vec<Vec<(plonk::Expression<T::F>, plonk::Expression<T::F>)>>,
    ) -> Vec<QueriedExpression<T>> {
        let gate_constraints = gate_expressions
                .iter()
                .map(|expr| {
                    T::from_expression(
                        expr,
                        &self.acc_u,
                        &self.selectors,
                        &self.fixed,
                        &self.instance,
                        &self.advice,
                        &self.challenges,
                    )
                })
            .collect_vec();

        let lookup_constraints = lookup_expressions
            .iter()
            .zip(self.lookups.iter())
            .flat_map(|(arg, data)| {

            let (inputs, tables): (Vec<QueriedExpression<T>>, Vec<QueriedExpression<T>>) =
                arg.iter().map(|(input_expr, table_expr)| {
                    let input_queried = T::from_expression(
                        input_expr,
                        &self.acc_u,
                        &self.selectors,
                        &self.fixed,
                        &self.instance,
                        &self.advice,
                        &self.challenges,
                    );
            
                    let table_queried = T::from_expression(
                        table_expr,
                        &self.acc_u,
                        &self.selectors,
                        &self.fixed,
                        &self.instance,
                        &self.advice,
                        &self.challenges,
                    );
            
                    (input_queried, table_queried)
                }).unzip();


                // Get expressions for variables r, m, g, h
                let r = T::new_challenge(data.r);
                let m = T::new_witness(data.m);
                let h = T::new_witness(data.h);
                let g = T::new_witness(data.g);

                // Get expressions for variables theta_0, ..., theta_k
                let thetas = data
                    .thetas
                    .iter()
                    .map(|theta| T::new_challenge(*theta))
                    .collect::<Vec<_>>();

                let one = T::new_constant(T::F::ONE);
                let u = T::new_u(self.acc_u[0]);

                // h * (r*u + theta_1 * input_1 + ... + theta_k * input_k ) = 1 * u^2
                let input_constraint =
                    h * zip(inputs, thetas.iter()).fold(r.clone() * u.clone(), |acc, (input, theta)| {
                        acc + (input * theta.clone())
                    }) - one * u.clone() * u.clone();
                // g * (r + theta_1 * table_1 + ... + theta_k * table_k ) = m * u
                let table_constraint = g * zip(tables, thetas.iter())
                    .fold(r, |acc, (table, theta)| acc + (table * theta.clone()))
                    - m * u.clone();
                [input_constraint, table_constraint].into_iter()
            })
            .collect_vec();
        // println!("gate_constraints_len: {:?}", gate_constraints.len());
        // println!("lookup_constraints_len: {:?}", lookup_constraints.len());
        [&gate_constraints[..], &lookup_constraints[..]].concat()
    }

    pub fn full_constraint(
        &self,
        gate_expressions: Vec<plonk::Expression<T::F>>,
        lookup_expressions: Vec<Vec<(plonk::Expression<T::F>, plonk::Expression<T::F>)>>,
    ) -> QueriedExpression<T> {
        let beta = T::new_witness(self.beta_polys);

        let constraints = self.all_constraints(gate_expressions, lookup_expressions);
        let ys = self
            .ys
            .iter()
            .map(|y| T::new_challenge(*y))
            .collect::<Vec<_>>();

        beta * T::linear_combination_constraints(&constraints, &ys)
    }

    pub fn full_constraint_vec(
        &self,
        gate_expressions: Vec<Expression<T::F>>,
        lookup_expressions: Vec<Vec<(Expression<T::F>, Expression<T::F>)>>,
    ) -> Vec<QueriedExpression<T>> {
        let beta = T::new_witness(self.beta_polys);
        let constraints = self.all_constraints(gate_expressions, lookup_expressions);
        constraints.iter().map(|constraint| beta.clone() * constraint.clone()).collect_vec()
    }

    pub fn full_constraint_no_beta_vec(
        &self,
        gate_expressions: Vec<Expression<T::F>>,
        lookup_expressions: Vec<Vec<(Expression<T::F>, Expression<T::F>)>>,
    ) -> Vec<QueriedExpression<T>> {
        self.all_constraints(gate_expressions, lookup_expressions)
    }

    pub fn full_constraint_beta_vec(
        &self,
        gate_expressions: Vec<Expression<T::F>>,
        lookup_expressions: Vec<Vec<(Expression<T::F>, Expression<T::F>)>>,
    ) -> Vec<QueriedExpression<T>> {
        let beta = T::new_witness(self.beta_polys);
        let beta_prime = T::new_witness(self.beta_prime_polys);
        let constraints = self.all_constraints(gate_expressions, lookup_expressions);
        constraints.iter().map(|constraint| beta.clone() * beta_prime.clone() * constraint.clone()).collect_vec()
    }

    pub fn ys_paired_vec(&self) -> Vec<QueriedExpression<T>> {
        self.ys.iter().map(|y| T::new_challenge(*y)).collect_vec()
    }

    pub fn linear_combination_constraints_ys(
        &self,
        constraints: &[QueriedExpression<T>],
        ys: &[QueriedExpression<T>],
    ) -> QueriedExpression<T> {
        T::linear_combination_constraints(constraints, ys)
    }
}
