use std::marker::PhantomData;

use halo2_gadgets::poseidon::PoseidonHash;
use halo2_proofs::{arithmetic::CurveAffine, circuit::{AssignedCell, Layouter, SimpleFloorPlanner}, dev::{CircuitLayout, MockProver}, halo2curves::{bn256, ff::PrimeFieldBits}, plonk::{Circuit, ConstraintSystem, Error}};
use halo2_base::utils::BigPrimeField;
use poseidon2::circuit::hash_chip::Poseidon2SpongeChip;
use rand::RngCore;
use crate::{accumulation::protostar::ivc::halo2::{chips::poseidon::spec::{R_F, R_P, SECURE_MDS}, ivc_circuits::primary::PrimaryCircuitConfig, StepCircuit}, frontend::halo2::CircuitExt, util::arithmetic::{Field, FromUniformBytes, TwoChainCurve}};
use crate::accumulation::protostar::ivc::halo2::chips::transcript::{T, RATE};
use super::main_chip::{MainChipConfig, Number};

#[derive(Clone, Debug)]
pub struct HashChainCircuit<C> 
where
    C: CurveAffine,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
    step_idx: usize,
    setup_done: C::Scalar,
    initial_input: Vec<C::Scalar>,
    input: Vec<C::Scalar>,
    output: Vec<C::Scalar>,
    num_elts_per_step: usize,
    x_i: Vec<C::Scalar>, // whats this?
    pub witness_size: usize,
}

impl<C> HashChainCircuit<C> 
where
    C: CurveAffine,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
  // produces a preimage to be hashed
  pub fn new(num_elts_per_step: usize) -> Self {
    let mut rng = rand::thread_rng();
    let x_i = (0..num_elts_per_step)
      .map(|_| C::Scalar::random(&mut rng))
      .collect::<Vec<_>>();

    Self {
      step_idx: 0,
      setup_done: C::Scalar::ZERO,
      initial_input: vec![C::Scalar::ZERO],
      input: vec![C::Scalar::ZERO],
      output: vec![C::Scalar::ZERO],
      num_elts_per_step,
      x_i,
      witness_size: 0,
    }
  }
}

impl<C> Circuit<C::Scalar> for HashChainCircuit<C>
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

impl<C> CircuitExt<C::Scalar> for HashChainCircuit<C>
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

impl<C: TwoChainCurve> StepCircuit<C> for HashChainCircuit<C>
    where
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{

    fn arity() -> usize {
        1
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
        let mut poseidon_hash = PoseidonHash::<C::Scalar, T, RATE>::new::<R_F, R_P, SECURE_MDS>();
        let mut m = self.output.to_vec();
        m.extend(self.x_i.iter().cloned());
        poseidon_hash.update(&m);
        vec![poseidon_hash.squeeze()]
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

        let (main_chip, _, poseidon_chip, _) = PrimaryCircuitConfig::initialize_chips(&config, &mut layouter)?;
        let mut sponge_chip = Poseidon2SpongeChip::<C::Scalar, {T}, {RATE}>::new(poseidon_chip, layouter.namespace(|| "sponge chip"));
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

                let mut m = self.output.to_vec();
                m.extend(self.x_i.iter().cloned());
                let m_vec: Vec<AssignedCell<C::Scalar, C::Scalar>> = m.iter().map(|x_i| main_chip.assign_witness_auto(&mut layouter, x_i, &mut witness_idx).unwrap().0).collect::<Vec<_>>();
                sponge_chip.update(&m_vec);
                let z = sponge_chip.squeeze(layouter.namespace(|| "squeeze"))?;

                let z0: Number<C::Scalar> = main_chip.select(&mut layouter, &setup_sel, &Number(z), &z_base[0])?;
                
                // stores the output for the current step
                self.set_output(&[z0.value()]);
                // updates the input to the output value for the next step // todo check this
                self.set_input(&[z0.value()]);

                (vec![z_base[0].clone()], vec![z0.clone()])
                
            },
                None => (Vec::new(), Vec::new()),
        };

        self.setup();

        Ok((inputs, outputs))
    }
} 

struct HashChainStepCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    marker: PhantomData<C>,
}


impl<C> Circuit<C::Scalar> for HashChainStepCircuit<C>
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
        let mut circuit = HashChainCircuit::<C>::new(1024);
        StepCircuit::<C>::synthesize(&mut circuit, config, layouter)?;
        Ok(())
    }
}

#[test]
fn hashchain_test() {
    let k = 14;
    let circuit = HashChainStepCircuit::<bn256::G1Affine>{ marker: PhantomData::<bn256::G1Affine> };
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
    let circuit = HashChainStepCircuit::<bn256::G1Affine>{ marker: PhantomData::<bn256::G1Affine> };
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