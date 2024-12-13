use std::marker::PhantomData;

use halo2_base::{
    utils::{BigPrimeField}
};
use halo2_proofs::{
    circuit::{floor_planner::Folding, Layouter, SimpleFloorPlanner}, dev::{CircuitLayout, MockProver}, halo2curves::group::ff::{FromUniformBytes, PrimeField, PrimeFieldBits}, plonk::{Circuit, ConstraintSystem, Error}
};
use num_bigint::{BigInt, BigUint};
use num_traits::Num;
use rand::RngCore;
use crate::{accumulation::protostar::ivc::halo2::ivc_circuits::primary::PrimaryCircuitConfig, frontend::halo2::CircuitExt, util::arithmetic::{CurveAffine, Field, TwoChainCurve}};

use crate::accumulation::protostar::ivc::halo2::StepCircuit;
use halo2_base::halo2_proofs::halo2curves::{
    bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta}};

use super::{main_chip::{MainChip, MainChipConfig, Number, NUM_MAIN_ADVICE, NUM_MAIN_FIXED}, range::range_check::RangeCheckChip};

pub struct MinrootGateInputs<F: PrimeField> {
    pub i: F,
    pub x_i: F,
    pub y_i: F,
    pub i_plus_1: F,
    pub x_i_plus_1: F,
    pub y_i_plus_1: F,
    pub i_plus_2: F,
    pub x_i_plus_2: F,
    pub y_i_plus_2: F,
}

pub struct MinrootGateOutputs<F: PrimeField> {
    pub i_plus_1: Number<F>,
    pub x_i_plus_1: Number<F>,
    pub y_i_plus_1: Number<F>,
    pub i_plus_2: Number<F>,
    pub x_i_plus_2: Number<F>,
    pub y_i_plus_2: Number<F>,
}

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
    type Config = MainChipConfig;  
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        self.clone()
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
        let i_0 = self.input()[0];
        let x_0 = self.input()[1];
        let y_0 = self.input()[2];
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

        let (main_chip, _, _, _, _) = PrimaryCircuitConfig::initialize_chips(&config, &mut layouter)?;
        let mut witness_idx = 0;
        // let mut assign_witness_auto = |value: &C::Scalar| -> Result<Number<C::Scalar>, Error> {
        //     let res = main_chip.assign_witness(&mut layouter, value, witness_idx)?;
        //     witness_idx += 1;
        //     Ok(res)
        // };

        // check for the non-trivial circuit with some input, the other cycle runs trivial circuit with no computation
        let first_input = self.input().first(); 
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
                let i_0 = self.input()[0];
                let x_0 = self.input()[1];
                let y_0 = self.input()[2];

                let mut z_out = Vec::new();
                
                let i_0_assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &i_0, &mut witness_idx)?;
                let x_0_assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &x_0, &mut witness_idx)?;
                let y_0_assigned: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &y_0, &mut witness_idx)?;
                let z_base: Vec<Number<C::Scalar>> = self.input().iter().map(|x| main_chip.assign_witness_auto(&mut layouter, x, &mut witness_idx).unwrap()).collect(); // todo check shouldnt this be initial input

                // variables to hold running x_i and y_i
                let mut i = i_0;
                let mut x_i = x_0;
                let mut y_i = y_0;

                for _i in (0..self.seq.len()).step_by(2) {
                    // non deterministic advice
                    let inputs = MinrootGateInputs { i, x_i, y_i, i_plus_1: self.seq[_i].i_plus_1, x_i_plus_1: self.seq[_i].x_i_plus_1, y_i_plus_1: self.seq[_i].y_i_plus_1, i_plus_2: self.seq[_i+1].i_plus_1, x_i_plus_2: self.seq[_i+1].x_i_plus_1, y_i_plus_2: self.seq[_i+1].y_i_plus_1 };
                    
                    // check the following conditions hold:
                    // (i) x_i_plus_1 = (x_i + y_i)^{1/5}, which can be more easily checked with x_i_plus_1^5 = x_i + y_i
                    // (ii) y_i_plus_1 = x_i + i 
                    // (iii) i_plus_1 = i + 1
                    let outputs = main_chip.minroot_gate_double(&mut layouter, inputs)?;
                    if _i == self.seq.len() - 2 {
                        z_out = vec![outputs.i_plus_2.clone(), outputs.x_i_plus_2.clone(), outputs.y_i_plus_2.clone()]; // todo check this
                    }

                    // update i, x_i and y_i for the next iteration
                    i = outputs.i_plus_2.value();
                    y_i = outputs.y_i_plus_2.value();
                    x_i = outputs.x_i_plus_2.value();
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

struct MinRootStepCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    marker: PhantomData<C>,
}


impl<C> Circuit<C::Scalar> for MinRootStepCircuit<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    type Config = PrimaryCircuitConfig<C>;  
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {
            marker: PhantomData::<C>,
        }
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        PrimaryCircuitConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {
        let mut circuit = MinRootCircuit::<C>::new(vec![C::Scalar::ZERO; 3], 1024);
        StepCircuit::<C>::synthesize(&mut circuit, config, layouter)?;
        Ok(())
    }
}

#[test]
fn minroot_test() {
    let k = 11;
    let circuit = MinRootStepCircuit::<bn256::G1Affine>{ marker: PhantomData::<bn256::G1Affine> };
    let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();
    println!("Witness count: {}", prover.witness_count);
    println!("Copy count: {}", prover.copy_count);
    //prover.assert_satisfied();
}

#[test]
fn minroot_test_layout() {
    use plotters::prelude::*;
    let root = BitMapBackend::new("MinRootStepCircuit.png", (5024, 3680)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("MinRoot Step Circuit", ("sans-serif", 60))
        .unwrap();

    let k = 11;
    let circuit = MinRootStepCircuit::<bn256::G1Affine>{ marker: PhantomData::<bn256::G1Affine> };
    let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();
    println!("Witness count: {}", prover.witness_count);
    println!("Copy count: {}", prover.copy_count);
    // prover.assert_satisfied();

    let circuit_layout = CircuitLayout{
        hide_labels: false,
        mark_equality_cells: false,
        show_equality_constraints: false,
        view_width: Some(0..24),
        view_height: Some(0..(1<<k)),
    };

    circuit_layout.render(k, &circuit, &root)
    .unwrap();

}