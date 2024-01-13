use halo2_base::halo2_proofs::{
    poly::Rotation,
    plonk::{Advice, Challenge, Column, ConstraintSystem, FirstPhase, SecondPhase, Selector},

};
use halo2_base::{
    gates::GateInstructions,
    utils::{bit_length, ScalarField},
    AssignedValue, Context,
    QuantumCell::{Constant, Existing, Witness},
};
use itertools::Itertools;
use std::{
    iter,
    marker::PhantomData,
    sync::{RwLock, RwLockReadGuard},
};



#[derive(Clone, Debug)]
/// This config consists of a variable number of advice columns, all in `SecondPhase`.
/// Each advice column has a selector column that enables a custom gate to aid RLC computation.
///
/// The intention is that this chip is only used for the actual RLC computation. All other operations should use `GateInstructions` by advancing the phase to `SecondPhase`.
///
/// Make sure that the `context_id` of `RlcChip` is different from that of any `FlexGateConfig` or `RangeConfig` you are using.
pub struct PoseidonChipCustomConfig<F: ScalarField> {
    pub basic_gates: Vec<(Column<Advice>, Selector)>,
    _marker: PhantomData<F>,
}

impl<F: ScalarField> PoseidonChipCustomConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, num_advice: usize) -> Self {
        let basic_gates = (0..num_advice)
            .map(|_| {
                let a = meta.advice_column();
                meta.enable_equality(a);
                let q = meta.selector();
                (a, q)
            })
            .collect_vec();


        for &(rlc, q) in basic_gates.iter() {
            meta.create_gate("X^5", |meta| {
                let q = meta.query_selector(q);
                let x = meta.query_advice(rlc, Rotation::cur());
                let x_pow5 = meta.query_advice(rlc, Rotation::next());
                let x_sq = x.clone() * x.clone();

                vec![q * (x_pow5  - x* x_sq.clone() *x_sq.clone())]
            });
        }

        Self { basic_gates, _marker: PhantomData }
    }
}

