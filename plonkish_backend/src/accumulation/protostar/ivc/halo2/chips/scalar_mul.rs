use std::marker::PhantomData;
use ethereum_types::U256;
use halo2_proofs::{arithmetic::Field, circuit::Value, dev::CircuitLayout, halo2curves::CurveAffineExt};
use halo2_base::utils::{BigPrimeField, FromUniformBytes};
use halo2_proofs::{arithmetic::CurveAffine, circuit::{AssignedCell, Layouter, SimpleFloorPlanner}, dev::MockProver, halo2curves::{bn256, ff::PrimeFieldBits}, plonk::{Circuit, ConstraintSystem, Error}};
use rand::RngCore;
use rand::Rng;
use itertools::Itertools;
use halo2_proofs::halo2curves::group::Group;
use sm_chip_primary::ScalarMulConfigInputs;
use crate::{accumulation::protostar::{hyperplonk::NUM_CHALLENGE_BITS, ivc::halo2::{ivc_circuits::primary::PrimaryCircuitConfig, StepCircuit}}, frontend::halo2::CircuitExt, util::arithmetic::TwoChainCurve};

use super::main_chip::{MainChipConfig, Number};

pub mod ec_chip_strawman;
pub mod ec_chip_deg10;
pub mod ec_chip_deg9;
pub mod ec_chip_deg6;
pub mod ec_chip_proj_deg6_full;
pub mod ec_chip_proj_deg12;
pub mod full_ecc_deg6;
pub mod ecc_deg6_hash;
pub mod sm_chip_primary;
pub mod ecc_deg6_hash_opt;

#[derive(Clone, Debug)]
pub struct ScalarMulChainInput<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
    C::Base: BigPrimeField + PrimeFieldBits,
{   
    pub rbits: Vec<C::Scalar>,
    pub comm1: [C::Scalar; 2],
    pub comm2: [C::Scalar; 2],
}

impl<C> ScalarMulChainInput<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub fn random(rng: &mut impl RngCore) -> Self {
        let rbits = (0..NUM_CHALLENGE_BITS).map(|_| rng.gen_bool(1.0 / 3.0))
            .map(|bit| if bit { C::Scalar::ONE } else { C::Scalar::ZERO })
            .collect_vec();
        let grumpkin_random = C::Secondary::from_xy(
            C::Scalar::from_str_vartime("19834382608297447889961323302677467055070110053155139740545148874538063289754").unwrap(),
            C::Scalar::from_str_vartime("20084669131162155340423162249467328031170931348295785825029782732565818853520").unwrap(),
        ).unwrap();
        let x = grumpkin_random.coordinates().unwrap().x().clone();
        let y = grumpkin_random.coordinates().unwrap().y().clone();
        Self { rbits, comm1: [x, y], comm2: [x, y] }
    }
}

#[derive(Clone, Debug)]
pub struct ScalarMulChainCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    step_idx: usize,
    setup_done: C::Scalar,
    initial_input: Vec<C::Scalar>,
    input: Vec<C::Scalar>,
    output: Vec<C::Scalar>,
    num_sm_per_step: usize,
    inputs_i: Vec<ScalarMulChainInput<C>>, 
    pub witness_size: usize,
}

impl<C> ScalarMulChainCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
    C::Base: BigPrimeField + PrimeFieldBits,
{
  // produces a preimage to be hashed
  pub fn new(num_sm_per_step: usize) -> Self {
    let mut rng = rand::thread_rng();
    let inputs_i = (0..num_sm_per_step)
      .map(|_| ScalarMulChainInput::<C>::random(&mut rng))
      .collect::<Vec<_>>();

    Self {
      step_idx: 0,
      setup_done: C::Scalar::ZERO,
      initial_input: vec![C::Scalar::ZERO, C::Scalar::ZERO],
      input: vec![C::Scalar::ZERO, C::Scalar::ZERO],
      output: vec![C::Scalar::ZERO, C::Scalar::ZERO],
      num_sm_per_step,
      inputs_i,
      witness_size: 0,
    }
  }
}

impl<C> Circuit<C::Scalar> for ScalarMulChainCircuit<C>
    where
        C: TwoChainCurve,
        C::Scalar: BigPrimeField + FromUniformBytes<64>,
        C::Base: BigPrimeField + PrimeFieldBits,
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

impl<C> CircuitExt<C::Scalar> for ScalarMulChainCircuit<C>
    where
        C: TwoChainCurve,
        C::Scalar: BigPrimeField + FromUniformBytes<64>,
        C::Base: BigPrimeField + PrimeFieldBits,
{
    fn instances(&self) -> Vec<Vec<C::Scalar>> {
        Vec::new()
    }

    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}

impl<C: TwoChainCurve> StepCircuit<C> for ScalarMulChainCircuit<C>
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
        let mut output_x = C::Scalar::ZERO;
        let mut output_y = C::Scalar::ZERO;
        for i in 0..self.num_sm_per_step {
            let outputs: ScalarMulConfigInputs<C> = sm_chip_primary::ScalarMulChip::get_outputs_raw(self.inputs_i[i].rbits.to_vec(), &self.inputs_i[i].comm1, &self.inputs_i[i].comm2).unwrap();
            outputs.X3.map(|val| output_x = val);
            outputs.Y3.map(|val| output_y = val);
        }
        vec![output_x, output_y]
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

        let (main_chip, _, _, scalar_mul_chip) = PrimaryCircuitConfig::initialize_chips(&config, &mut layouter)?;
        let mut witness_idx = 0;

        // check for the non-trivial circuit with some input, the other cycle runs trivial circuit with no computation
        let first_input = self.input().first(); 
        let (inputs, outputs) = 
        match first_input {
            Some(first_input) => {
                // checks if synthesize has been called for the first time (preprocessing), initiates the input and output same as the intial_input
                // when synthesize is called for second time by prove_steps, updates the input to the output value for the next step
                let one: Number<C::Scalar> = main_chip.assign_fixed(&mut layouter, &C::Scalar::ONE, 0)?;
                let setup_done: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &self.setup_done, &mut witness_idx)?;
                let setup_sel: Number<C::Scalar> = main_chip.is_equal(&mut layouter, &one, &setup_done)?;
                let z_base: Vec<Number<C::Scalar>> = self.input().iter().map(|x| main_chip.assign_witness_auto(&mut layouter, x, &mut witness_idx).unwrap()).collect();
                let results = (0..self.num_sm_per_step)
                    .map(|i| scalar_mul_chip.assign_raw(
                        layouter.namespace(|| "scalar_mul_witness_comms"), 
                        self.inputs_i[i].rbits.to_vec(), 
                        &self.inputs_i[i].comm1, 
                        &self.inputs_i[i].comm2
                    ).unwrap())
                    .collect_vec();
                
                let (z_x, z_y) = results.last().unwrap();                
                let z0_x: Number<C::Scalar> = main_chip.select(&mut layouter, &setup_sel, z_x, &z_base[0])?;
                let z0_y: Number<C::Scalar> = main_chip.select(&mut layouter, &setup_sel, z_y, &z_base[1])?;
                // stores the output for the current step
                self.set_output(&[z0_x.value(), z0_y.value()]);
                // updates the input to the output value for the next step // todo check this
                self.set_input(&[z0_x.value(), z0_y.value()]);

                (vec![z_base[0].clone(), z_base[1].clone()], vec![z0_x.clone(), z0_y.clone()])
                
            },
                None => (Vec::new(), Vec::new()),
        };

        self.setup();

        Ok((inputs, outputs))
    }
} 
struct ScalarMulChainStepCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    marker: PhantomData<C>,
}


impl<C> Circuit<C::Scalar> for ScalarMulChainStepCircuit<C>
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
        let mut circuit = ScalarMulChainCircuit::<C>::new(1);
        StepCircuit::<C>::synthesize(&mut circuit, config, layouter)?;
        Ok(())
    }
}

#[test]
fn scalar_mul_test() {
    let k = 8;
    let circuit = ScalarMulChainStepCircuit::<bn256::G1Affine>{ marker: PhantomData::<bn256::G1Affine> };
    let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();
    println!("Witness count: {}", prover.witness_count);
    println!("Copy count: {}", prover.copy_count);
    //prover.assert_satisfied();
}

#[test]
fn circuit_test_layout() {
    use plotters::prelude::*;
    let root = BitMapBackend::new("ScalarMulChain_debug.png", (5024, 3680)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("Scalar Mul Chain Layout", ("sans-serif", 60))
        .unwrap();

    let k = 8;
    let circuit = ScalarMulChainStepCircuit::<bn256::G1Affine>{ marker: PhantomData::<bn256::G1Affine> };
    MockProver::run(k, &circuit, vec![vec![]]).unwrap(); //.assert_satisfied();

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