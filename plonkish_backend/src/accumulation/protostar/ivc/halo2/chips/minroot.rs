use halo2_base::{
    gates::{circuit::{builder::BaseCircuitBuilder, BaseCircuitParams, BaseConfig}, GateInstructions, RangeInstructions}, 
    halo2_proofs::{circuit::{Layouter, SimpleFloorPlanner}, plonk::{Circuit, ConstraintSystem, Error}}, 
    utils::{BigPrimeField, CurveAffineExt, FromUniformBytes, PrimeField, ScalarField}, AssignedValue, QuantumCell::{Constant, Existing, Witness}
};
use halo2_proofs::halo2curves::ff::PrimeFieldBits;
use num_bigint::{BigInt, BigUint};
use num_traits::Num;
use rand::RngCore;
use crate::{accumulation::protostar::ivc::halo2::ivc_circuits::primary::PrimaryCircuitConfig, frontend::halo2::CircuitExt, util::arithmetic::{CurveAffine, Field, TwoChainCurve}};

use crate::accumulation::protostar::ivc::halo2::StepCircuit;
use halo2_base::halo2_proofs::halo2curves::{
    bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta}};

use super::{main_chip::{MainChip, MainChipConfig, Number}, range::range_check::RangeCheckChip};

#[derive(Clone, Debug)]
struct MinRootIteration<F: PrimeField> {
  i: F,
  x_i: F,
  y_i: F,
  i_plus_1: F,
  x_i_plus_1: F,
  y_i_plus_1: F,
}

impl<F: PrimeField> MinRootIteration<F> {
  // produces a sample non-deterministic advice, executing one invocation of MinRoot per step
  fn new(num_iters: usize, i_0: &F, x_0: &F, y_0: &F) -> (Vec<F>, Vec<Self>) {
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
    let mut i = *i_0;
    let mut x_i = *x_0;
    let mut y_i = *y_0;
    for _i1 in 0..num_iters {
      let x_i_plus_1 = (x_i + y_i).pow_vartime(exp.to_u64_digits()); // computes the fifth root of x_i + y_i

      // sanity check
      let sq = x_i_plus_1 * x_i_plus_1;
      let quad = sq * sq;
      let fifth = quad * x_i_plus_1;
      debug_assert_eq!(fifth, x_i + y_i);

      let i_plus_1 = i + F::ONE;
      let y_i_plus_1 = x_i + i_plus_1;

      res.push(Self {
        i,
        x_i,
        y_i,
        i_plus_1,
        x_i_plus_1,
        y_i_plus_1,
      });

      i = i_plus_1;
      x_i = x_i_plus_1;
      y_i = y_i_plus_1;
    }

    let z0 = vec![*i_0, *x_0, *y_0];

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
    pub num_iters_per_step: usize,
    setup_done: C::Scalar,
    initial_input: Vec<C::Scalar>,
    input: Vec<C::Scalar>,
    seq: Vec<MinRootIteration<C::Scalar>>,
    output: Vec<C::Scalar>,
    pub witness_size: usize,
}

impl<C> MinRootCircuit<C>
    where
        C: CurveAffine,
        C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
    pub fn new(initial_input: Vec<C::Scalar>, num_iters_per_step: usize) -> Self {
        let (output, seq) = 
            MinRootIteration::new(num_iters_per_step, &initial_input[0], &initial_input[1], &initial_input[2]);

        Self { 
            step_idx: 0,
            num_iters_per_step,
            setup_done: C::Scalar::ZERO,
            initial_input: initial_input.clone(), 
            input: initial_input.clone(),
            seq, 
            output,
            witness_size: 0,
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
        3
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
            MinRootIteration::new(self.num_iters_per_step, &self.input[0], &self.input[1], &self.input[2]);

        self.seq = seq;

        // use the provided inputs
        let i_0 = self.input()[0].clone();
        let x_0 = self.input()[1].clone();
        let y_0 = self.input()[2].clone();
        let mut z_out: Vec<C::Scalar> = Vec::new();

        // variables to hold running x_i and y_i
        let mut i = i_0;
        let mut x_i = x_0;
        let mut y_i = y_0;

        for _i in 0..self.seq.len() {
            // non deterministic advice
            let i_plus_1 = self.seq[_i].i_plus_1;
            let x_i_plus_1 = self.seq[_i].x_i_plus_1;

            // check the following conditions hold:
            // (i) x_i_plus_1 = (x_i + y_i)^{1/5}, which can be more easily checked with x_i_plus_1^5 = x_i + y_i
            // (ii) y_i_plus_1 = x_i + i
            let x_i_plus_1_sq = x_i_plus_1 * x_i_plus_1;
            let x_i_plus_1_quad = x_i_plus_1_sq * x_i_plus_1_sq;
            assert_eq!(x_i_plus_1_quad * x_i_plus_1, x_i + y_i);

            if _i == self.seq.len() - 1 {
                z_out = vec![i_plus_1, x_i_plus_1, x_i + i_plus_1];
            }

            // update i, x_i and y_i for the next iteration
            i = i_plus_1;
            y_i = x_i + i_plus_1;
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
        config: PrimaryCircuitConfig<C>,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<
        (
            Vec<Number<C::Scalar>>,
            Vec<Number<C::Scalar>>,
        ),
        Error,
    > {

        let (main_chip, range_chip, pow5_chip, sm_chip) = PrimaryCircuitConfig::initialize_chips(&config, &mut layouter)?;
        let mut witness_idx = 0;
        // let mut assign_witness_auto = |value: &C::Scalar| -> Result<Number<C::Scalar>, Error> {
        //     let res = main_chip.assign_witness(&mut layouter, value, witness_idx)?;
        //     witness_idx += 1;
        //     Ok(res)
        // };

        // check for the non-trivial circuit with some input, the other cycle runs trivial circuit with no computation
        let first_input = self.input().get(0).copied(); 
        let (inputs, outputs) = 
        match first_input {
            Some(first_input) => {
                // checks if synthesize has been called for the first time (preprocessing), initiates the input and output same as the intial_input
                // when synthesize is called for second time by prove_steps, updates the input to the output value for the next step
                let one: Number<C::Scalar> = main_chip.assign_fixed(&mut layouter, &C::Scalar::ONE, 0)?;
                let zero: Number<C::Scalar> = main_chip.assign_fixed(&mut layouter, &C::Scalar::ZERO, 1)?;
                let setup_done: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &self.setup_done, &mut witness_idx)?;
                let setup_sel: Number<C::Scalar> = main_chip.is_equal(&mut layouter, &one, &setup_done)?;

                // define the calculation logic for the circuit, also done in the next_output function
                // use the provided inputs
                let i_0 = self.input()[0].clone();
                let x_0 = self.input()[1].clone();
                let y_0 = self.input()[2].clone();

                let mut z_out = Vec::new();
                
                let i_0_assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &i_0, &mut witness_idx)?;
                let x_0_assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &x_0, &mut witness_idx)?;
                let y_0_assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &y_0, &mut witness_idx)?;
                let z_base: Vec<Number<C::Scalar>> = self.input().iter().map(|x| main_chip.assign_witness_auto(&mut layouter, x, &mut witness_idx).unwrap()).collect();

                // variables to hold running x_i and y_i
                let mut i = i_0;
                let mut x_i = x_0;
                let mut y_i = y_0;

                for _i in 0..self.seq.len() {
                    // non deterministic advice
                    let i_assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &i, &mut witness_idx)?;
                    let x_i_assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &x_i, &mut witness_idx)?;
                    let y_i_assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &y_i, &mut witness_idx)?;
                    let i_plus1_assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &self.seq[_i].i_plus_1, &mut witness_idx)?;
                    let x_i_plus_1assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &self.seq[_i].x_i_plus_1, &mut witness_idx)?;
                    let y_i_plus_1assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &self.seq[_i].y_i_plus_1, &mut witness_idx)?;

                    // check the following conditions hold:
                    // (i) x_i_plus_1 = (x_i + y_i)^{1/5}, which can be more easily checked with x_i_plus_1^5 = x_i + y_i
                    let x_i_plus_1_sq: Number<C::Scalar> = main_chip.mul(&mut layouter, &x_i_plus_1assigned, &x_i_plus_1assigned)?;
                    let x_i_plus_1_quad: Number<C::Scalar> = main_chip.mul(&mut layouter, &x_i_plus_1_sq, &x_i_plus_1_sq)?;
                    let lhs1: Number<C::Scalar> = main_chip.mul(&mut layouter, &x_i_plus_1_quad, &x_i_plus_1assigned)?;
                    let rhs1: Number<C::Scalar> = main_chip.add(&mut layouter, &x_i_assigned, &y_i_assigned)?;
                    let lhs1_sel: Number<C::Scalar> = main_chip.is_equal(&mut layouter, &lhs1, &zero)?;
                    let rhs1_sel: Number<C::Scalar> = main_chip.is_equal(&mut layouter, &rhs1, &zero)?;
                    main_chip.constrain_equal(&mut layouter, &lhs1_sel, &rhs1_sel)?;

                    // (ii) y_i_plus_1 = x_i + i 
                    let lhs2: Number<C::Scalar> = y_i_plus_1assigned.clone();
                    let rhs2: Number<C::Scalar> = main_chip.add(&mut layouter, &x_i_assigned, &i_plus1_assigned)?;
                    let lhs2_sel: Number<C::Scalar> = main_chip.is_equal(&mut layouter, &lhs2, &zero)?;
                    let rhs2_sel: Number<C::Scalar> = main_chip.is_equal(&mut layouter, &rhs2, &zero)?;
                    main_chip.constrain_equal(&mut layouter, &lhs2_sel, &rhs2_sel)?;

                    // (iii) i_plus_1 = i + 1
                    let lhs3: Number<C::Scalar> = i_plus1_assigned.clone();
                    let rhs3: Number<C::Scalar> = main_chip.add(&mut layouter, &i_assigned, &one)?;
                    let lhs3_sel: Number<C::Scalar> = main_chip.is_equal(&mut layouter, &lhs3, &zero)?;
                    let rhs3_sel: Number<C::Scalar> = main_chip.is_equal(&mut layouter, &rhs3, &zero)?;
                    main_chip.constrain_equal(&mut layouter, &lhs3_sel, &rhs3_sel)?;

                    if _i == self.seq.len() - 1 {
                        z_out = vec![i_plus1_assigned.clone(), x_i_plus_1assigned.clone(), y_i_plus_1assigned.clone()]; // todo check this
                    }

                    // update i, x_i and y_i for the next iteration
                    i = i_plus1_assigned.value();
                    y_i = y_i_plus_1assigned.value();
                    x_i = x_i_plus_1assigned.value();
                }

                let z0: Number<C::Scalar> = main_chip.select(&mut layouter, &setup_sel, &z_out[0], &z_base[0])?;
                let z1: Number<C::Scalar> = main_chip.select(&mut layouter, &setup_sel, &z_out[1], &z_base[1])?;
                let z3: Number<C::Scalar> = main_chip.select(&mut layouter, &setup_sel, &z_out[2], &z_base[2])?;
                
                // stores the output for the current step
                self.set_output(&[z0.value(), z1.value(), z3.value()]);
                // updates the input to the output value for the next step // todo check this
                self.set_input(&[z0.value(), z1.value(), z3.value()]);

                (vec![i_0_assigned, x_0_assigned, y_0_assigned], vec![z0, z1, z3])
                
            },
                None => (Vec::new(), Vec::new()),
        };

        self.setup();

        Ok((inputs, outputs))
    }
} 