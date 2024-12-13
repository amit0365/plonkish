
use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Value}, dev::{CircuitLayout, MockProver}, halo2curves::bn256::{self, Fr}, plonk::{Circuit, ConstraintSystem, Error}
};
use itertools::Itertools;
use plotters::{prelude::BitMapBackend, style::WHITE};
use rand::{rngs::StdRng, RngCore};
use crate::{
    accumulation::protostar::ivc::halo2::{chips::sha256::{INPUT_RAW_2, INPUT_RAW_3, INPUT_RAW_5, INPUT_RAW_9, INPUT_RAW_17, INPUT_RAW_33, INPUT_RAW_65, INPUT_RAW_129, INPUT_RAW_257, INPUT_RAW_513, INPUT_RAW_1025}, ivc_circuits::primary::PrimaryCircuitConfig, StepCircuit}, frontend::halo2::CircuitExt, util::arithmetic::{
        fe_to_fe, CurveAffine, Field, FromUniformBytes, MultiMillerLoop, PrimeFieldBits,
        TwoChainCurve,
    }};
use halo2_base::utils::BigPrimeField;
use sha2::{Sha256, Digest};
use crate::accumulation::protostar::ivc::halo2::chips::sha256::Sha256 as Sha256Chip;
use super::{main_chip::{MainChipConfig, Number}, sha256::{BlockWord, Table16Chip, INPUT_1025, INPUT_129, INPUT_17, INPUT_2, INPUT_257, INPUT_3, INPUT_33, INPUT_5, INPUT_513, INPUT_65, INPUT_9}};

#[derive(Clone, Debug)]
pub struct Sha256ChainCircuit<C> 
where
    C: CurveAffine,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
    step_idx: usize,
    setup_done: C::Scalar,
    initial_input: Vec<C::Scalar>,
    input: Vec<C::Scalar>,
    output: Vec<C::Scalar>,
    input_size: usize,
    pub witness_size: usize,
}

impl<C> Sha256ChainCircuit<C> 
where
    C: CurveAffine,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
  // produces a preimage to be hashed
  pub fn new(input_size: usize) -> Self {
    let mut rng = rand::thread_rng();

    Self {
      step_idx: 0,
      setup_done: C::Scalar::ZERO,
      initial_input: vec![C::Scalar::ZERO],
      input: vec![C::Scalar::ZERO],
      output: vec![C::Scalar::ZERO],
      input_size,
      witness_size: 0,
    }
  }
}

impl<C> Circuit<C::Scalar> for Sha256ChainCircuit<C>
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

impl<C> CircuitExt<C::Scalar> for Sha256ChainCircuit<C>
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

impl<C: TwoChainCurve> StepCircuit<C> for Sha256ChainCircuit<C>
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
        // let mut hasher = Sha256::new();
        // let input = match self.input_size {
        //     2 => INPUT_RAW_2.as_slice(),
        //     3 => INPUT_RAW_3.as_slice(),
        //     5 => INPUT_RAW_5.as_slice(),
        //     9 => INPUT_RAW_9.as_slice(),
        //     17 => INPUT_RAW_17.as_slice(),
        //     33 => INPUT_RAW_33.as_slice(),
        //     65 => INPUT_RAW_65.as_slice(),
        //     129 => INPUT_RAW_129.as_slice(),
        //     257 => INPUT_RAW_257.as_slice(),
        //     513 => INPUT_RAW_513.as_slice(),
        //     1025 => INPUT_RAW_1025.as_slice(),
        //     _ => panic!("Unexpected input_size: {}", self.input_size),
        // };

        // let input_u8 = input.iter()
        //     .flat_map(|&x| x.to_le_bytes())
        //     .collect::<Vec<u8>>();
        // m_u8.extend(input_u8);
        // hasher.update(&m_u8);
        // let hash = hasher.finalize();
        // let hash_bytes: [u8; 64] = hash.as_slice().try_into().unwrap();
        // println!("hash_bytes next_output done");
        // vec![C::Scalar::from_uniform_bytes(&hash_bytes)]
        vec![]
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

        let (main_chip, _, _, _, table16_chip) = PrimaryCircuitConfig::initialize_chips(&config, &mut layouter)?;
        //Table16Chip::load(config.sha256_config.clone(), &mut layouter)?;
        let mut witness_idx = 0;

        // check for the non-trivial circuit with some input, the other cycle runs trivial circuit with no computation
        let first_input = self.input().first(); 
        let (inputs, outputs) = 
        match first_input {
            Some(first_input) => {
                // checks if synthesize has been called for the first time (preprocessing), initiates the input and output same as the intial_input
                // when synthesize is called for second time by prove_steps, updates the input to the output value for the next step

                // let one: Number<C::Scalar> = main_chip.assign_fixed(&mut layouter, &C::Scalar::ONE, 0)?;
                // let setup_done: Number<C::Scalar> = main_chip.assign_witness_auto(&mut layouter, &self.setup_done, &mut witness_idx)?;
                // let setup_sel: Number<C::Scalar> = main_chip.is_equal(&mut layouter, &one, &setup_done)?;
                // let z_base: Vec<Number<C::Scalar>> = self.input().iter().map(|x| main_chip.assign_witness_auto(&mut layouter, x, &mut witness_idx).unwrap()).collect();

                // let m_u8: Vec<u8> = self.output[0].to_repr().to_vec();  
                // let m_u32: [u32; 8] = m_u8.chunks(4)
                //     .map(|chunk| u32::from_le_bytes(chunk.try_into().unwrap()))
                //     .collect::<Vec<u32>>()
                //     .try_into()
                //     .unwrap();

                // let mut m_u32_16 = [0; 16]; // if not multiple of 16, fails so pad with 0s
                // m_u32_16[0..8].copy_from_slice(&m_u32);

                // let mut m_block = m_u32_16.iter().map(|x| BlockWord(Value::known(*x))).collect_vec();   
                let input = match self.input_size {
                    2 => INPUT_2.as_slice(),
                    3 => INPUT_3.as_slice(),
                    5 => INPUT_5.as_slice(),
                    9 => INPUT_9.as_slice(),
                    17 => INPUT_17.as_slice(),
                    33 => INPUT_33.as_slice(),
                    65 => INPUT_65.as_slice(),
                    129 => INPUT_129.as_slice(),
                    257 => INPUT_257.as_slice(),
                    513 => INPUT_513.as_slice(),
                    1025 => INPUT_1025.as_slice(),
                    _ => panic!("Unexpected input_size: {}", self.input_size),
                };
                let _ = Sha256Chip::digest(table16_chip, &mut layouter, input);

                // m_block.extend(input);
                // let mut digest_u32: [u32; 8] = [0; 8];
                // let _ = Sha256Chip::digest(table16_chip, &mut layouter, input)?.0.iter().enumerate().map(|(i, x)| {
                //     x.0.map(|x| digest_u32[i] = x)
                // });

                // let digest_u8: [u8; 32] = digest_u32.iter()
                //     .flat_map(|&x| x.to_le_bytes())
                //     .collect::<Vec<u8>>()
                //     .try_into()
                //     .unwrap(); 

                // let digest_fe = main_chip.assign_witness_auto(&mut layouter, &C::Scalar::from_repr(digest_u8).unwrap(), &mut witness_idx).unwrap();
                // let z0: Number<C::Scalar> = main_chip.select(&mut layouter, &setup_sel, &digest_fe, &z_base[0])?;
                
                // // stores the output for the current step
                // self.set_output(&[z0.value()]);
                // // updates the input to the output value for the next step // todo check this
                // self.set_input(&[z0.value()]);

                // (vec![z_base[0].clone()], vec![z0.clone()])
                (Vec::new(), Vec::new())
            },
                None => (Vec::new(), Vec::new()),
        };

        self.setup();

        Ok((inputs, outputs))
    }
} 

struct Sha256ChainStepCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    input_size: usize,
    marker: PhantomData<C>,
}


impl<C> Circuit<C::Scalar> for Sha256ChainStepCircuit<C>
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
            input_size: self.input_size,
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
        let mut circuit = Sha256ChainCircuit::<C>::new(self.input_size);
        StepCircuit::<C>::synthesize(&mut circuit, config, layouter)?;
        Ok(())
    }
}

#[test]
fn sha256chain_test() {
    let k = 17;
    let circuit = Sha256ChainStepCircuit::<bn256::G1Affine>{ input_size: 33, marker: PhantomData::<bn256::G1Affine> };
    let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();
    println!("Witness count: {}", prover.witness_count);
    println!("Copy count: {}", prover.copy_count);
    prover.assert_satisfied();
}

#[test]
fn sha256chain_test_layout() {
    use plotters::prelude::*;
    let root = BitMapBackend::new("SHA256ChainStepCircuit.png", (10024, 10080)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("SHA256 Chain Step Circuit", ("sans-serif", 60))
        .unwrap();

    let k = 17;
    let circuit = Sha256ChainStepCircuit::<bn256::G1Affine>{ input_size: 33, marker: PhantomData::<bn256::G1Affine> };
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