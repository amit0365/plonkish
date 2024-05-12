use halo2_base::{
    gates::{circuit::{builder::BaseCircuitBuilder, BaseCircuitParams, BaseConfig}, GateInstructions, RangeInstructions}, 
    halo2_proofs::{circuit::{Layouter, SimpleFloorPlanner}, halo2curves::grumpkin::G1Affine, plonk::{Circuit, ConstraintSystem, Error}}, 
    utils::{BigPrimeField, CurveAffineExt, FromUniformBytes, PrimeField, ScalarField}, AssignedValue, QuantumCell::{Constant, Existing, Witness}
};
use halo2_ecc::{ecc::EccChip, fields::native_fp::NativeFieldChip};
use halo2_proofs::{arithmetic::CurveExt, halo2curves::{ff::PrimeFieldBits, group::{Group, GroupOps}}};
use num_bigint::{BigInt, BigUint};
use num_traits::Num;
use rand::RngCore;
use crate::{frontend::halo2::CircuitExt, util::arithmetic::{fe_mod_from_le_bytes, CurveAffine, Field, TwoChainCurve}};
use halo2_base::halo2_proofs::halo2curves::group::prime::PrimeCurveAffine;
use super::halo2::StepCircuit;
use halo2_base::halo2_proofs::halo2curves::{
    bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta}};

#[derive(Clone, Debug)]
pub struct MinRootOutput<C: TwoChainCurve> 
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{ 
    pub i: C::Scalar,
    pub pt_ai: C::Secondary,
    pub pt_bi: C::Secondary,
}

// here x and y represent two diff curve points 
#[derive(Clone, Debug)]
struct MinRootIteration<C: TwoChainCurve> 
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
  i: C::Scalar,
  pt_ai: C::Secondary,
  pt_bi: C::Secondary,
  i_plus_1: C::Scalar,
  pt_ai_plus_1: C::Secondary,
  pt_bi_plus_1: C::Secondary,
}

impl<C: TwoChainCurve> MinRootIteration<C> 
where
C::Base: BigPrimeField + PrimeFieldBits,
C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
  // produces a sample non-deterministic advice, executing one invocation of MinRoot per step
  fn new(num_iters: usize, i_0: &C::Scalar, pt_a0: &C::Secondary, pt_b0: &C::Secondary) -> (Vec<C::Scalar>, Vec<Self>) 
  {
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
    let mut pt_ai = *pt_a0;
    let mut pt_bi = *pt_b0;

    for _i1 in 0..num_iters {

      // implement double and add
      let i_plus_1 = i + C::Scalar::ONE;
      let i_bits = <C::Scalar as PrimeFieldBits>::to_le_bits(&i_plus_1);
      let mut scalar_mul = C::Secondary::identity();
      let mut multiple = pt_ai.clone() + scalar_mul;
      for bit in i_bits {
          let tmp = scalar_mul.clone() + multiple.into();
          scalar_mul = if bit { tmp.into() } else { scalar_mul };
          multiple = multiple.double();
      }

      let pt_ai_plus_1 = (pt_ai + pt_bi).double().into();
      let pt_bi_plus_1 = scalar_mul.into();

      res.push(Self {
        i,
        pt_ai,
        pt_bi,
        i_plus_1,
        pt_ai_plus_1,
        pt_bi_plus_1,
      });

      i = i_plus_1;
      pt_ai = pt_ai_plus_1; 
      pt_bi = pt_bi_plus_1;
    }

    let z0 = vec![i, *pt_ai.coordinates().unwrap().x(), *pt_ai.coordinates().unwrap().y(), *pt_bi.coordinates().unwrap().x(), *pt_bi.coordinates().unwrap().y()];

    (z0, res)
  }
}

#[derive(Clone, Debug, Default)]
pub struct MinRootCircuit<C: TwoChainCurve> 
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    step_idx: usize,
    pub num_iters_per_step: usize,
    setup_done: C::Scalar,
    initial_input: Vec<C::Scalar>,
    input: Vec<C::Scalar>,
    seq: Vec<MinRootIteration<C>>,
    output: Vec<C::Scalar>,
    pub witness_size: usize,
}

impl<C: TwoChainCurve> MinRootCircuit<C>
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    pub fn new(initial_input: MinRootOutput<C>, num_iters_per_step: usize) -> Self {
        let (output, seq) = 
            MinRootIteration::new(num_iters_per_step, &initial_input.i, &initial_input.pt_ai, &initial_input.pt_bi);

        let initial_input = vec![initial_input.i, *initial_input.pt_ai.coordinates().unwrap().x(), *initial_input.pt_ai.coordinates().unwrap().y(), *initial_input.pt_bi.coordinates().unwrap().x(), *initial_input.pt_bi.coordinates().unwrap().y()];
        
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

impl<C: TwoChainCurve> Circuit<C::Scalar> for MinRootCircuit<C>
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
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

impl<C: TwoChainCurve> CircuitExt<C::Scalar> for MinRootCircuit<C>
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
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

        let pt_a0 = C::Secondary::from_xy(self.input[1], self.input[2]).unwrap();
        let pt_b0 = C::Secondary::from_xy(self.input[3], self.input[4]).unwrap();

        let (output, seq) = 
            MinRootIteration::new(self.num_iters_per_step, &self.input[0], &pt_a0, &pt_b0);

        self.seq = seq;

        // use the provided inputs
        let i_0 = self.input[0].clone();
        let pt_ai_0 = pt_a0.clone();
        let pt_bi_0 = pt_b0.clone();
        let mut z_out: Vec<C::Scalar> = Vec::new();

        // variables to hold running x_i and y_i
        let mut i = i_0;
        let mut pt_ai = pt_ai_0;
        let mut pt_bi = pt_bi_0;

        for _i in 0..self.seq.len() {
            let i_plus_1 = self.seq[_i].i_plus_1;
            let pt_ai_plus_1 = self.seq[_i].pt_ai_plus_1;
            let pt_bi_plus_1 = self.seq[_i].pt_bi_plus_1;

            if _i == self.seq.len() - 1 {
                z_out = vec![i_plus_1, *pt_ai_plus_1.coordinates().unwrap().x(), *pt_ai_plus_1.coordinates().unwrap().y(), *pt_bi_plus_1.coordinates().unwrap().x(), *pt_bi_plus_1.coordinates().unwrap().y()];
            }

            // update i, pt_ai and pt_bi for the next iteration
            i = i_plus_1;
            pt_ai = pt_ai_plus_1;
            pt_bi = pt_bi_plus_1;
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
        let native_chip = NativeFieldChip::new(&range_chip);
        let ecc_chip = EccChip::new(&native_chip);
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
                let i_0 = self.input()[0].clone();
                let pta_x0 = self.input()[1].clone();
                let pta_y0 = self.input()[2].clone();
                let pt_a0 = C::Secondary::from_xy(pta_x0, pta_y0).unwrap();
                let ptb_x0 = self.input()[3].clone();
                let ptb_y0 = self.input()[4].clone();
                let pt_b0 = C::Secondary::from_xy(ptb_x0, ptb_y0).unwrap();

                let mut z_out = Vec::new();
                let i_0_assigned = ctx.load_witness(i_0);
                let pt_a0_assigned = ecc_chip.assign_point_unchecked(ctx, pt_a0);
                let pt_b0_assigned = ecc_chip.assign_point_unchecked(ctx, pt_b0);
                let z_base = self.input().to_vec();

                // variables to hold running x_i and y_i
                let mut i = i_0;
                let mut pt_ai = pt_a0;
                let mut pt_bi = pt_b0;

                for _i in 0..self.seq.len() {
                    // non deterministic advice
                    let one = ctx.load_constant(C::Scalar::ONE);
                    let i_assigned = ctx.load_witness(i);
                    let pt_ai_assigned = ecc_chip.assign_point_unchecked(ctx, pt_ai);
                    let pt_bi_assigned = ecc_chip.assign_point_unchecked(ctx, pt_bi);
                    let i_plus1_assigned = ctx.load_witness(self.seq[_i].i_plus_1);
                    let pt_ai_plus_1assigned = ecc_chip.assign_point_unchecked(ctx, self.seq[_i].pt_ai_plus_1);
                    let pt_bi_plus_1assigned = ecc_chip.assign_point_unchecked(ctx, self.seq[_i].pt_bi_plus_1);

                    println!("pt_ai_assigned: {:?}", pt_ai_assigned);
                    println!("pt_bi_assigned: {:?}", pt_bi_assigned);

                    // check the following conditions hold:
                    // (i) pt_ai_plus_1 = (pt_ai + pt_bi).double()
                    let identity = ecc_chip.assign_constant_point(ctx, C::Secondary::identity());
                    let lhs1 = pt_ai_plus_1assigned.clone();
                    let rhs_add = ecc_chip.add_unequal(ctx, pt_ai_assigned.clone(), pt_bi_assigned.clone(), false);
                    let rhs_double = ecc_chip.double(ctx, rhs_add);
                    let lhs1_sel = ecc_chip.select(ctx, lhs1, identity.clone(), setup_sel);
                    let rhs1_sel = ecc_chip.select(ctx, rhs_double, identity.clone(), setup_sel);
                    ecc_chip.assert_equal(ctx, lhs1_sel, rhs1_sel);

                    // (iii) pt_bi_plus_1 = pt_ai * i 
                    let lhs2 = pt_bi_plus_1assigned.clone();
                    let i_bits = gate_chip.num_to_bits(ctx, i_plus1_assigned, 254); 
                    let rhs2 = ecc_chip.scalar_mult::<C::Secondary>(ctx, pt_ai_assigned, i_bits, 1, 4);
                    let lhs2_sel = ecc_chip.select(ctx, lhs2, identity.clone(), setup_sel);
                    let rhs2_sel = ecc_chip.select(ctx, rhs2, identity.clone(), setup_sel);
                    ecc_chip.assert_equal(ctx, lhs2_sel, rhs2_sel);
                    println!("second_pass");

                    // (v) i_plus_1 = i + 1
                    let lhs3 = i_plus1_assigned.clone();
                    let rhs3 = gate_chip.add(ctx, i_assigned, one);
                    let lhs3_sel = gate_chip.select(ctx, lhs3, zero, setup_sel);
                    let rhs3_sel = gate_chip.select(ctx, rhs3, zero, setup_sel);
                    ctx.constrain_equal(&lhs3_sel, &rhs3_sel);
                    println!("third_pass");

                    if _i == self.seq.len() - 1 {
                        z_out = vec![i_plus1_assigned.clone(), pt_ai_plus_1assigned.x().clone(), pt_ai_plus_1assigned.y().clone(), pt_bi_plus_1assigned.x().clone(), pt_bi_plus_1assigned.y().clone()]; 
                    }

                    // update i, x_i and y_i for the next iteration
                    i = *i_plus1_assigned.value();
                    pt_ai = C::Secondary::from_xy(*pt_ai_plus_1assigned.x().value(), *pt_ai_plus_1assigned.y().value()).unwrap();
                    pt_bi = C::Secondary::from_xy(*pt_bi_plus_1assigned.x().value(), *pt_bi_plus_1assigned.y().value()).unwrap();
                }

                let z0 = gate_chip.select(ctx, z_out[0], Constant(z_base[0]), setup_sel);
                let z1 = gate_chip.select(ctx, z_out[1], Constant(z_base[1]), setup_sel);
                let z3 = gate_chip.select(ctx, z_out[2], Constant(z_base[2]), setup_sel);
                let z4 = gate_chip.select(ctx, z_out[3], Constant(z_base[3]), setup_sel);
                let z5 = gate_chip.select(ctx, z_out[4], Constant(z_base[4]), setup_sel);
                
                // stores the output for the current step
                self.set_output(&[*z0.value(), *z1.value(), *z3.value(), *z4.value(), *z5.value()]);
                // updates the input to the output value for the next step // todo check this
                self.set_input(&[*z0.value(), *z1.value(), *z3.value(), *z4.value(), *z5.value()]);

                (vec![i_0_assigned, pt_a0_assigned.x().clone(), pt_a0_assigned.y().clone(), pt_b0_assigned.x().clone(), pt_b0_assigned.y().clone()], vec![z0, z1, z3, z4, z5])
                
            },
                None => (Vec::new(), Vec::new()),
        };

        self.setup();

        Ok((inputs, outputs))
   }
} 

