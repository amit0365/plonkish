use halo2_base::{
    gates::{circuit::{builder::BaseCircuitBuilder, BaseCircuitParams, BaseConfig}, GateInstructions, RangeInstructions}, 
    halo2_proofs::{circuit::{Layouter, SimpleFloorPlanner}, plonk::{Circuit, ConstraintSystem, Error}}, 
    utils::{BigPrimeField, CurveAffineExt, FromUniformBytes, PrimeField, ScalarField}, AssignedValue
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
    pub fn new(num_constraints: usize, initial_input: Vec<C::Scalar>, num_iter_per_step: usize) -> Self {
        let seq = vec![
                    MinRootIteration {
                      x_i: C::Scalar::ZERO,
                      y_i: C::Scalar::ZERO,
                      x_i_plus_1: C::Scalar::ZERO,
                      y_i_plus_1: C::Scalar::ZERO }; num_iter_per_step];

        Self { 
            step_idx: 0,
            setup_done: C::Scalar::from(0u64),
            initial_input: initial_input.clone(), 
            input: initial_input.clone(),
            seq, 
            output: initial_input.clone(),
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
        self.setup_done = C::Scalar::from(1u64);
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
    fn next_output(&self) -> Vec<C::Scalar> {
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
                let setup_done = ctx.load_witness(self.setup_done);
                let setup_sel = gate_chip.is_equal(ctx, one, setup_done);

                // define the calculation logic for the circuit, also done in the next_output function
                // use the provided inputs
                let x_0 = self.input()[0].clone();
                let y_0 = self.input()[0].clone();
                let mut z_out = Vec::new();
                let x_0_assigned = ctx.load_witness(x_0);
                let y_0_assigned = ctx.load_witness(y_0);
                let z_base = vec![ctx.load_zero(), ctx.load_zero()];

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
                    ctx.constrain_equal(&lhs, &rhs);

                    if i == self.seq.len() - 1 {
                        z_out = vec![x_i_plus_1.clone(), x_i_assigned.clone()]; // todo check this
                    }

                    // update x_i and y_i for the next iteration
                    y_i = *x_i_assigned.value();
                    x_i = *x_i_plus_1.value();
                }

                let z0 = gate_chip.select(ctx, z_out[0], z_base[0], setup_sel);
                let z1 = gate_chip.select(ctx, z_out[1], z_base[1], setup_sel);
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



// fn main() {
//   println!("Nova-based VDF with MinRoot delay function");
//   println!("=========================================================");

//   let num_steps = 10;
//   for num_iters_per_step in [1024, 2048, 4096, 8192, 16384, 32768, 65535] {
//     // number of iterations of MinRoot per Nova's recursive step
//     let circuit_primary = MinRootCircuit {
//       seq: vec![
//         MinRootIteration {
//           x_i: <G1 as Group>::Scalar::zero(),
//           y_i: <G1 as Group>::Scalar::zero(),
//           x_i_plus_1: <G1 as Group>::Scalar::zero(),
//           y_i_plus_1: <G1 as Group>::Scalar::zero(),
//         };
//         num_iters_per_step
//       ],
//     };

//     let circuit_secondary = TrivialTestCircuit::default();

//     println!("Proving {num_iters_per_step} iterations of MinRoot per step");

//     // produce public parameters
//     let start = Instant::now();
//     println!("Producing public parameters...");
//     let pp = PublicParams::<
//       G1,
//       G2,
//       MinRootCircuit<<G1 as Group>::Scalar>,
//       TrivialTestCircuit<<G2 as Group>::Scalar>,
//     >::setup(&circuit_primary, &circuit_secondary);
//     println!("PublicParams::setup, took {:?} ", start.elapsed());

//     println!(
//       "Number of constraints per step (primary circuit): {}",
//       pp.num_constraints().0
//     );
//     println!(
//       "Number of constraints per step (secondary circuit): {}",
//       pp.num_constraints().1
//     );

//     println!(
//       "Number of variables per step (primary circuit): {}",
//       pp.num_variables().0
//     );
//     println!(
//       "Number of variables per step (secondary circuit): {}",
//       pp.num_variables().1
//     );

//     // produce non-deterministic advice
//     let (z0_primary, minroot_iterations) = MinRootIteration::new(
//       num_iters_per_step * num_steps,
//       &<G1 as Group>::Scalar::zero(),
//       &<G1 as Group>::Scalar::one(),
//     );
//     let minroot_circuits = (0..num_steps)
//       .map(|i| MinRootCircuit {
//         seq: (0..num_iters_per_step)
//           .map(|j| MinRootIteration {
//             x_i: minroot_iterations[i * num_iters_per_step + j].x_i,
//             y_i: minroot_iterations[i * num_iters_per_step + j].y_i,
//             x_i_plus_1: minroot_iterations[i * num_iters_per_step + j].x_i_plus_1,
//             y_i_plus_1: minroot_iterations[i * num_iters_per_step + j].y_i_plus_1,
//           })
//           .collect::<Vec<_>>(),
//       })
//       .collect::<Vec<_>>();

//     let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

//     type C1 = MinRootCircuit<<G1 as Group>::Scalar>;
//     type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;
//     // produce a recursive SNARK
//     println!("Generating a RecursiveSNARK...");
//     let mut recursive_snark: RecursiveSNARK<G1, G2, C1, C2> = RecursiveSNARK::<G1, G2, C1, C2>::new(
//       &pp,
//       &minroot_circuits[0],
//       &circuit_secondary,
//       z0_primary.clone(),
//       z0_secondary.clone(),
//     );

//     for (i, circuit_primary) in minroot_circuits.iter().take(num_steps).enumerate() {
//       let start = Instant::now();
//       let res = recursive_snark.prove_step(
//         &pp,
//         circuit_primary,
//         &circuit_secondary,
//         z0_primary.clone(),
//         z0_secondary.clone(),
//       );
//       assert!(res.is_ok());
//       println!(
//         "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
//         i,
//         res.is_ok(),
//         start.elapsed()
//       );
//     }

//     // verify the recursive SNARK
//     println!("Verifying a RecursiveSNARK...");
//     let start = Instant::now();
//     let res = recursive_snark.verify(&pp, num_steps, &z0_primary, &z0_secondary);
//     println!(
//       "RecursiveSNARK::verify: {:?}, took {:?}",
//       res.is_ok(),
//       start.elapsed()
//     );
//     assert!(res.is_ok());

//     // produce a compressed SNARK
//     println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
//     let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

//     let start = Instant::now();
//     type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
//     type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
//     type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<G1, EE1>;
//     type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<G2, EE2>;

//     let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
//     println!(
//       "CompressedSNARK::prove: {:?}, took {:?}",
//       res.is_ok(),
//       start.elapsed()
//     );
//     assert!(res.is_ok());
//     let compressed_snark = res.unwrap();

//     let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
//     bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
//     let compressed_snark_encoded = encoder.finish().unwrap();
//     println!(
//       "CompressedSNARK::len {:?} bytes",
//       compressed_snark_encoded.len()
//     );

//     // verify the compressed SNARK
//     println!("Verifying a CompressedSNARK...");
//     let start = Instant::now();
//     let res = compressed_snark.verify(&vk, num_steps, z0_primary, z0_secondary);
//     println!(
//       "CompressedSNARK::verify: {:?}, took {:?}",
//       res.is_ok(),
//       start.elapsed()
//     );
//     assert!(res.is_ok());
//     println!("=========================================================");
//   }
// }
