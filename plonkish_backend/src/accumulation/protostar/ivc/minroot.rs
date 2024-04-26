use halo2_base::{
    gates::{circuit::{builder::BaseCircuitBuilder, BaseCircuitParams, BaseConfig}, GateInstructions, RangeInstructions}, 
    halo2_proofs::{circuit::{Layouter, SimpleFloorPlanner}, plonk::{Circuit, ConstraintSystem, Error}}, 
    utils::{BigPrimeField, CurveAffineExt, FromUniformBytes, PrimeField, ScalarField}, AssignedValue, QuantumCell::{Constant, Existing, Witness}
};
use halo2_proofs::halo2curves::ff::PrimeFieldBits;
use num_bigint::{BigInt, BigUint};
use num_traits::Num;
use rand::RngCore;
use crate::{frontend::halo2::CircuitExt, util::arithmetic::{CurveAffine, Field, TwoChainCurve}};

use super::halo2::StepCircuit;
use halo2_base::halo2_proofs::halo2curves::{
    bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta}};

#[derive(Clone, Debug)]
struct MinRootIteration<F: PrimeField> {
  x_i: F,
  y_i: F,
  x_i_plus_1: F,
  y_i_plus_1: F,
}

impl<F: PrimeField> MinRootIteration<F> {
  // produces a sample non-deterministic advice, executing one invocation of MinRoot per step
  fn new(num_iters: usize, x_0: &F, y_0: &F) -> (Vec<F>, Vec<Self>) {
    // although this code is written generically, it is tailored to Bn254' scalar field
    let bn256_order = BigInt::from_str_radix(
        "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001",
        16,
      )
      .unwrap();
    
    // exp = (p - 3) / 5 == 5^(p-2) * (p - 3) 
    let exp = {
        let p = bn256_order.to_biguint().unwrap();
        let two = BigUint::parse_bytes(b"2", 10).unwrap();
        let three = BigUint::parse_bytes(b"3", 10).unwrap();
        let five = BigUint::parse_bytes(b"5", 10).unwrap();
        let five_inv = five.modpow(&(&p - &two), &p);
        (&five_inv * (&p - &three)) % &p
      };

    let mut res = Vec::new();
    let mut x_i = *x_0;
    let mut y_i = *y_0;
    for _i in 0..num_iters {
      let x_i_plus_1 = (x_i + y_i).pow_vartime(exp.to_u64_digits()); // computes the fifth root of x_i + y_i

      // sanity check
      let sq = x_i_plus_1 * x_i_plus_1;
      let quad = sq * sq;
      let fifth = quad * x_i_plus_1;
      debug_assert_eq!(fifth, x_i + y_i);

      let y_i_plus_1 = x_i;

      res.push(Self {
        x_i,
        y_i,
        x_i_plus_1,
        y_i_plus_1,
      });

      x_i = x_i_plus_1;
      y_i = y_i_plus_1;
    }

    let z0 = vec![*x_0, *y_0];

    (z0, res)
  }
}

#[derive(Clone, Debug, Default)]
pub struct MinRootCircuit<C> 
    where
        C: CurveAffine,
        C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
    step_idx: usize,
    num_iters_per_step: usize,
    setup_done: C::Scalar,
    initial_input: Vec<C::Scalar>,
    input: Vec<C::Scalar>,
    seq: Vec<MinRootIteration<C::Scalar>>,
    output: Vec<C::Scalar>,
}

impl<C> MinRootCircuit<C>
    where
        C: CurveAffine,
        C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
    pub fn new(initial_input: Vec<C::Scalar>, num_iters_per_step: usize) -> Self {
        let (output, seq) = 
            MinRootIteration::new(num_iters_per_step, &initial_input[0], &initial_input[1]);

        Self { 
            step_idx: 0,
            num_iters_per_step,
            setup_done: C::Scalar::ZERO,
            initial_input: initial_input.clone(), 
            input: initial_input.clone(),
            seq, 
            output,
        }
    }
}

impl<C> Circuit<C::Scalar> for MinRootCircuit<C>
    where
        C: CurveAffine,
        C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
    type Config = BaseConfig<C::Scalar>;  
    type FloorPlanner = SimpleFloorPlanner;
    type Params = BaseCircuitParams;

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure_with_params(meta: &mut ConstraintSystem<C::Scalar>, params: BaseCircuitParams) -> Self::Config {
        BaseCircuitBuilder::configure_with_params(meta, params)
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        unreachable!()
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {
        Ok(())
    }
}

impl<C> CircuitExt<C::Scalar> for MinRootCircuit<C>
    where
        C: CurveAffine,
        C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
    fn instances(&self) -> Vec<Vec<C::Scalar>> {
        Vec::new()
    }

    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}


impl<C: TwoChainCurve> StepCircuit<C> for MinRootCircuit<C>
    where
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{

    fn arity() -> usize {
        2
    }

    fn setup(&mut self) -> C::Scalar {
        self.setup_done = C::Scalar::ONE;
        self.setup_done
    }

    fn initial_input(&self) -> &[C::Scalar] {
        &self.initial_input
    }

    fn input(&self) -> &[C::Scalar] {
        &self.input
    }

    fn set_input(&mut self, input: &[C::Scalar]) {
        self.input = input.to_vec();
    }

    fn output(&self) -> &[C::Scalar] {
        &self.output
    }

    // define the calculation logic. This is done out of the zk_circuit
    // Used in recursive_circuit.update to cal hash of the next iteration 
    // And checked with the hash synthesize_accumulation_verifier.check_hash_state
    fn next_output(&mut self) -> Vec<C::Scalar> {

        // produces a sample non-deterministic advice, executing one invocation of MinRoot per step
        let (output, seq) = 
            MinRootIteration::new(self.num_iters_per_step, &self.input[0], &self.input[1]);

        self.seq = seq;

        // use the provided inputs
        let x_0 = self.input()[0].clone();
        let y_0 = self.input()[1].clone();
        let mut z_out: Vec<C::Scalar> = Vec::new();

        // variables to hold running x_i and y_i
        let mut x_i = x_0;
        let mut y_i = y_0;
        for i in 0..self.seq.len() {
        // non deterministic advice
        let x_i_plus_1 = self.seq[i].x_i_plus_1;

        // check the following conditions hold:
        // (i) x_i_plus_1 = (x_i + y_i)^{1/5}, which can be more easily checked with x_i_plus_1^5 = x_i + y_i
        // (ii) y_i_plus_1 = x_i
        let x_i_plus_1_sq = x_i_plus_1 * x_i_plus_1;
        let x_i_plus_1_quad = x_i_plus_1_sq * x_i_plus_1_sq;
        assert_eq!(x_i_plus_1_quad * x_i_plus_1, x_i + y_i);

        if i == self.seq.len() - 1 {
            z_out = vec![x_i_plus_1.clone(), x_i.clone()];
        }

            // update x_i and y_i for the next iteration
            y_i = x_i;
            x_i = x_i_plus_1;
        }

        z_out
    
    }

    fn set_output(&mut self, output: &[C::Scalar]) {
        self.output = output.to_vec();
    }

    fn step_idx(&self) -> usize {
        self.step_idx
    }

    fn num_constraints(&self) -> usize {
        unreachable!()
    }

    fn next(&mut self) {
        self.step_idx += 1;
    }

    fn synthesize(
        &mut self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
        builder: &mut BaseCircuitBuilder<C::Scalar>,
    ) -> Result<
        (
            Vec<AssignedValue<C::Scalar>>,
            Vec<AssignedValue<C::Scalar>>,
        ),
        Error,
    > {
        let range_chip = builder.range_chip();
        let gate_chip = range_chip.gate();
        let ctx = builder.main(0);

        // check for the non-trivial circuit with some input, the other cycle runs trivial circuit with no computation
        let first_input = self.input().get(0).copied(); 
        let (inputs, outputs) = 
        match first_input {
            Some(first_input) => {
                // checks if synthesize has been called for the first time (preprocessing), initiates the input and output same as the intial_input
                // when synthesize is called for second time by prove_steps, updates the input to the output value for the next step
                let one = ctx.load_constant(C::Scalar::ONE);
                let zero = ctx.load_constant(C::Scalar::ZERO);
                let setup_done = ctx.load_witness(self.setup_done);
                let setup_sel = gate_chip.is_equal(ctx, one, setup_done);

                // define the calculation logic for the circuit, also done in the next_output function
                // use the provided inputs
                let x_0 = self.input()[0].clone();
                let y_0 = self.input()[1].clone();
                let mut z_out = Vec::new();
                let x_0_assigned = ctx.load_witness(x_0);
                let y_0_assigned = ctx.load_witness(y_0);
                let z_base = self.input().to_vec();

                // variables to hold running x_i and y_i
                let mut x_i = x_0;
                let mut y_i = y_0;

                for i in 0..self.seq.len() {
                    // non deterministic advice
                    let x_i_assigned = ctx.load_witness(x_i);
                    let y_i_assigned = ctx.load_witness(y_i);
                    let x_i_plus_1 = ctx.load_witness(self.seq[i].x_i_plus_1);

                    // check the following conditions hold:
                    // (i) x_i_plus_1 = (x_i + y_i)^{1/5}, which can be more easily checked with x_i_plus_1^5 = x_i + y_i
                    // (ii) y_i_plus_1 = x_i
                    // (1) constraints for condition (i) are below
                    // (2) constraints for condition (ii) is avoided because we just used x_i wherever y_i_plus_1 is used
                    let x_i_plus_1_sq = gate_chip.mul(ctx, x_i_plus_1, x_i_plus_1);
                    let x_i_plus_1_quad = gate_chip.mul(ctx, x_i_plus_1_sq, x_i_plus_1_sq);
                    let lhs = gate_chip.mul(ctx, x_i_plus_1_quad, x_i_plus_1);
                    let rhs = gate_chip.add(ctx, x_i_assigned, y_i_assigned);
                    let lhs_sel = gate_chip.select(ctx, lhs, zero, setup_sel);
                    let rhs_sel = gate_chip.select(ctx, rhs, zero, setup_sel);
                    ctx.constrain_equal(&lhs_sel, &rhs_sel);

                    if i == self.seq.len() - 1 {
                        z_out = vec![x_i_plus_1.clone(), x_i_assigned.clone()]; // todo check this
                    }

                    // update x_i and y_i for the next iteration
                    y_i = *x_i_assigned.value();
                    x_i = *x_i_plus_1.value();
                }

                let z0 = gate_chip.select(ctx, z_out[0], Constant(z_base[0]), setup_sel);
                let z1 = gate_chip.select(ctx, z_out[1], Constant(z_base[1]), setup_sel);
                // stores the output for the current step
                self.set_output(&[*z0.value(), *z1.value()]);
                // updates the input to the output value for the next step // todo check this
                self.set_input(&[*z0.value(), *z1.value()]);

                (vec![x_0_assigned, y_0_assigned], vec![z0, z1])
                
            },
                None => (Vec::new(), Vec::new()),
        };

        self.setup();

        Ok((inputs, outputs))
    }
} 