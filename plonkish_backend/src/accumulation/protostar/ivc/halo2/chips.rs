pub mod poseidon;
pub mod scalar_mul;
pub mod main_chip;
pub mod transcript;
pub mod range;
pub mod sha256;
pub mod minroot;
pub mod hashchain;

use halo2_gadgets::poseidon::{primitives::{ConstantLength, Spec, Hash as inlineHash}, Hash, Pow5Chip, Pow5Config};
use halo2_base::utils::{CurveAffineExt, ScalarField, BigPrimeField};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Chip, Value},
    halo2curves::{bn256::Fr as Fp, grumpkin::Fr as Fq},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance}, dev::MockProver
};
use halo2_proofs::arithmetic::Field;
use poseidon2::circuit::{hash_chip::NUM_PARTIAL_SBOX, spec::PoseidonSpec as Poseidon2ChipSpec};
use crate::accumulation::protostar::ivc::halo2::chips::poseidon::hash_chip::{Poseidon2Config, Poseidon2Chip};
use rand::rngs::OsRng;
use std::marker::PhantomData;
use scalar_mul::ec_chip_strawman::ScalarMulChip;
use crate::util::arithmetic::{PrimeFieldBits, CurveAffine, TwoChainCurve, fe_to_fe, fe_from_bits_le, fe_to_bits_le, fe_truncated};
use rand::RngCore;
use self::{poseidon::{hash_chip::{PoseidonChip, PoseidonConfig}, spec::PoseidonSpec}, scalar_mul::ecc_deg6_hash::{ScalarMulChipConfig, ScalarMulConfigInputs, NUM_ADVICE_SM, NUM_FIXED_SM, NUM_INSTANCE_SM}};

pub const T: usize = 4;
pub const R: usize = 3;
pub const L: usize = 13;
pub const L1: usize = 13;

pub const NUM_ADVICE: usize = T+1;
pub const NUM_CONSTANTS: usize = 2*T + NUM_PARTIAL_SBOX;

#[derive(Clone)]
pub struct CycleFoldChipConfig<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    poseidon: Poseidon2Config<C, T, R, L>,
    scalar_mul: ScalarMulChipConfig<C>,
    instance: Column<Instance>,
}

#[derive(Clone, Default)]
pub struct CyclefoldChip<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{ 
    pub inputs: Vec<ScalarMulConfigInputs<C>> 
}

impl<C> Circuit<C::Scalar> for CyclefoldChip<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    type Params = ();
    type Config = CycleFoldChipConfig<C>; 
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {

        let instance = [0; NUM_INSTANCE_SM].map(|_| meta.instance_column());
        for col in &instance {
            meta.enable_equality(*col);
        }

        let advices = [0; NUM_ADVICE_SM + 1].map(|_| meta.advice_column());
        for col in &advices {
            meta.enable_equality(*col);
        }

        let constants = [0; NUM_CONSTANTS + 1].map(|_| meta.fixed_column());
        for col in &constants {
            meta.enable_constant(*col);
            meta.enable_equality(*col);
        }

        let scalar_mul = ScalarMulChipConfig::<C>::configure(meta, advices[..NUM_ADVICE_SM].try_into().unwrap(), [constants[NUM_CONSTANTS]]);
        
        let poseidon = 
            Poseidon2Chip::<C, Poseidon2ChipSpec, T, R, L>::configure(
                meta,
                advices[..T].try_into().unwrap(),
                advices[T..2*T].try_into().unwrap(),
                advices[2*T],
                constants[..T].try_into().unwrap(), 
                constants[T..T + NUM_PARTIAL_SBOX].try_into().unwrap(), 
                constants[T+ NUM_PARTIAL_SBOX..2*T + NUM_PARTIAL_SBOX].try_into().unwrap(), 
            );

        Self::Config {
            poseidon,
            scalar_mul,
            instance: instance[0],
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {

        let mut hash_inputs = Vec::new();
        let hash_chip = Poseidon2Chip::<C, Poseidon2ChipSpec, T, R, L>::construct(
            config.poseidon,
        );

        for i in 0..self.inputs.len() {
            if i == 0 {
                hash_inputs.extend_from_slice(&config.scalar_mul.assign(layouter.namespace(|| "ScalarMulChip"), self.inputs[i].clone())?);
            } else {
                hash_inputs.extend_from_slice(&config.scalar_mul.assign(layouter.namespace(|| "ScalarMulChip"), self.inputs[i].clone())?[1..]);
            }
        }

        let message: [AssignedCell<C::Scalar, C::Scalar>; L] =
        match hash_inputs.try_into() {
            Ok(arr) => arr,
            Err(_) => panic!("Failed to convert Vec to Array"),
        };

        let hash = hash_chip.hash(
            layouter.namespace(|| "perform poseidon hash"),
            message,
        )?;

        // layouter.constrain_instance(hash.cell(), config.instance, 0)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    //use halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fr, Fq, G1Affine, G1}, grumpkin}};
    use halo2_gadgets::poseidon::{primitives::{ConstantLength, Spec, Hash as inlineHash}, Hash, Pow5Chip, Pow5Config};
    //use halo2_proofs::{arithmetic::Field, halo2curves::{ff::BatchInvert, group::{cofactor::CofactorCurveAffine, Curve, Group}, Coordinates, CurveAffine}};
    //use crate::{accumulation::protostar::ivc::halo2::{chips::{poseidon::spec::{PoseidonSpec, PoseidonSpecFp}, scalar_mul::ecc_deg6_hash::ScalarMulConfigInputs}, test::strawman::into_coordinates}, util::arithmetic::{fe_to_fe, fe_from_bits_le}};
    use super::{CyclefoldChip, L};
    //use rand::{rngs::OsRng, Rng};
    //use itertools::Itertools;
    use std::{fs::File, iter};

    use bitvec::vec;
    use itertools::Itertools;
    use std::{marker::PhantomData, time::Instant};
    use halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fq, Fr, G1Affine, G1}, grumpkin}, plonk::Assigned};
    use halo2_proofs::{arithmetic::Field, halo2curves::{ff::BatchInvert, group::{cofactor::CofactorCurveAffine, Curve, Group}, Coordinates, CurveAffine}};
    use crate::util::{arithmetic::{add_proj_comp, double_proj_comp, fe_from_bits_le, fe_to_fe, into_coordinates, is_identity_proj, is_scaled_identity_proj, powers, sub_proj, sub_proj_comp, ProjectivePoint}, izip_eq};
    use crate::accumulation::protostar::ivc::halo2::chips::poseidon::spec::{PoseidonSpec, PoseidonSpecFp};
    use super::{ScalarMulChip, ScalarMulConfigInputs};
    use rand::{rngs::OsRng, Rng};
    
    pub const NUM_CHALLENGE_BITS: usize = 128;

    #[test]
    fn cyclefold_chip() {

        use plotters::prelude::*;
        let root = BitMapBackend::new("CyclefoldChip_t7.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("CyclefoldChip", ("sans-serif", 60)).unwrap();

        let k = 10; 
        let mut rng = OsRng;
        let scalar_bits = NUM_CHALLENGE_BITS;

        let mut rbits = Vec::new();
        rbits.extend((0..scalar_bits).map(|_| rng.gen_bool(1.0 / 3.0)));   
        let rbits_rev = rbits.iter().rev().cloned().collect_vec();
        let mut rbits_vec = rbits.iter().map(|bit| 
            Value::known(if *bit {Fq::ONE} else {Fq::ZERO}))
            .rev()
            .collect_vec();

        let witness_gen_time = Instant::now();
        let re2_vec = powers(Fq::from(2)).take(scalar_bits + 1).map(Value::known).collect_vec().into_iter().rev().collect_vec();
        let mut rlc_vec = vec![Value::known(Fq::ZERO)]; 
        for i in 0..scalar_bits {
            let rlc = if rbits_rev[i] { rlc_vec[i] + re2_vec[i] } else { rlc_vec[i] };
            rlc_vec.push(rlc);
        }
        // let zero = ProjectivePoint {
        //     x: Fq::zero(),
        //     y: Fq::one(),
        //     z: Fq::zero(),
        // };
        let zero = G1::identity();
        let mut p = G1::identity();
        while p == G1::identity() {
            p = G1::random(&mut rng);
        }

        let p_single = p.to_affine(); 
        let mut ptx_vec = Vec::new();
        let mut pty_vec = Vec::new();
        for i in 0..scalar_bits {
            ptx_vec.push(Value::known(p_single.x));
            pty_vec.push(Value::known(p_single.y));
        }

        let comm = G1::random(rng);
        //let mut acc_prev = ProjectivePoint::identity();
        let mut acc_prev = G1::identity();
        let mut acc_prev_xvec = Vec::new();
        let mut acc_prev_yvec = Vec::new();
        let mut acc_prev_zvec = Vec::new();

        let mut lhs_double_xvec = Vec::new();
        let mut lhs_double_yvec = Vec::new();
        let mut lhs_double_zvec = Vec::new();
        let mut lhs_zvec = Vec::new();
        let mut rhs_zvec = Vec::new();

        acc_prev_xvec.push(acc_prev.x);
        acc_prev_yvec.push(acc_prev.y); 
        acc_prev_zvec.push(acc_prev.z);

        for i in 0..scalar_bits {
            let choice_proj = if rbits_rev[i] { 
                p
                // ProjectivePoint::new(p_single.x, p_single.y, Fq::one())
            } else { zero };
            
            acc_prev = G1::double(&acc_prev); //double_proj_comp(acc_prev);
            let lhs = acc_prev;
            acc_prev = acc_prev + choice_proj; //add_proj_comp(acc_prev, choice_proj);
            acc_prev_xvec.push(acc_prev.x);
            acc_prev_yvec.push(acc_prev.y);
            acc_prev_zvec.push(acc_prev.z);

            lhs_double_xvec.push(lhs.x);
            lhs_double_yvec.push(lhs.y);
            lhs_double_zvec.push(lhs.z);

            let lhs_double_proj = ProjectivePoint::new(lhs_double_xvec[i], lhs_double_yvec[i], lhs_double_zvec[i]);
            let rhs = acc_prev - choice_proj; //sub_proj_comp(acc_prev_proj, p_single_proj);
            let rhs_proj = ProjectivePoint::new(rhs.x, rhs.y, rhs.z);
            if is_identity_proj(rhs_proj) && is_identity_proj(lhs_double_proj) {
                lhs_zvec.push(Fq::one());
                rhs_zvec.push(Fq::one());
            } else if is_identity_proj(rhs_proj) && is_scaled_identity_proj(lhs_double_proj) {
                lhs_zvec.push(lhs_double_proj.y);
                rhs_zvec.push(Fq::one());
            } else if is_identity_proj(lhs_double_proj) && is_scaled_identity_proj(rhs_proj) {
                lhs_zvec.push(Fq::one());
                rhs_zvec.push(rhs.y);
            } else {
                lhs_zvec.push(lhs_double_zvec[i]);
                rhs_zvec.push(rhs.z);
            }
        }

        let batch_invert_time = Instant::now();
        lhs_zvec.batch_invert();
        println!("batch_invert_time2: {:?}", batch_invert_time.elapsed());
        
        let lambda_vec = lhs_zvec.iter().zip(rhs_zvec).map(|(lhs, rhs)| Value::known(lhs*rhs)).collect_vec();

        let rbits_native = rbits.iter().map(|bit| 
            if *bit {Fr::ONE} else {Fr::ZERO})
            .collect_vec();

        let r = fe_from_bits_le(rbits_native);
        let r_non_native: Fq = fe_to_fe(r);
        let scalar_mul_given = p * r;
        let scalar_mul_proj = ProjectivePoint::new(acc_prev_xvec.last().unwrap().clone(), acc_prev_yvec.last().unwrap().clone(), acc_prev_zvec.last().unwrap().clone());
        assert_eq!(scalar_mul_given.x * scalar_mul_proj.z, scalar_mul_proj.x * scalar_mul_given.z);
        assert_eq!(scalar_mul_given.y * scalar_mul_proj.z, scalar_mul_proj.y * scalar_mul_given.z);

        // do point addition of comm and sm
        let result_given = comm + scalar_mul_given;
        let comm_proj = ProjectivePoint::new(comm.x, comm.y, comm.z);
        let result_calc = add_proj_comp(comm_proj, scalar_mul_proj);
        // assert_eq!(result_given.x * result_calc.z, result_calc.x * result_given.z);
        // assert_eq!(result_given.y * result_calc.z, result_calc.y * result_given.z);

        let comm_affine = comm.to_affine();
        let scalar_mul_given_affine = scalar_mul_given.to_affine();
        let result_given_affine = result_given.to_affine();
        let acc_x_vec = acc_prev_xvec.iter().map(|fe| Value::known(*fe)).collect_vec();
        let acc_y_vec = acc_prev_yvec.iter().map(|fe| Value::known(*fe)).collect_vec();
        let acc_z_vec = acc_prev_zvec.iter().map(|fe| Value::known(*fe)).collect_vec();
        println!("witness_gen_time: {:?}", witness_gen_time.elapsed());

        let inputs =
            ScalarMulConfigInputs::<grumpkin::G1Affine> { 
                rbits_vec, 
                re2_vec,
                rlc_vec,
                ptx_vec,
                pty_vec,
                acc_x_vec, 
                acc_y_vec, 
                acc_z_vec,
                lambda_vec, 
                comm_X: Value::known(comm_affine.x),
                comm_Y: Value::known(comm_affine.y),
                sm_X: Value::known(scalar_mul_given_affine.x),
                sm_Y: Value::known(scalar_mul_given_affine.y),
                X3: Value::known(result_given_affine.x),
                Y3: Value::known(result_given_affine.y),
            };  

        let mut messages_vec = Vec::new();
        let message_vec = iter::empty()
            .chain([r_non_native])
            .chain(into_coordinates(&p_single))
            .chain(into_coordinates(&comm_affine))
            .collect_vec();
        
        let input_len = L/4;
        for i in 0..input_len {
            if i == 0 {
                messages_vec.extend_from_slice(&message_vec);
            } else {
                messages_vec.extend_from_slice(&message_vec[1..]);
            }
        }

        let message: [Fq; L] =
        match messages_vec.try_into() {
            Ok(arr) => arr,
            Err(_) => panic!("Failed to convert Vec to Array"),
        };
        assert_eq!(L, message.len());

        let hash =
            inlineHash::<Fq, PoseidonSpec, ConstantLength<L>, 5, 4>::init().hash(message);

        let circuit = CyclefoldChip::<grumpkin::G1Affine> { inputs: vec![inputs; input_len] };
        let prover = MockProver::run(k, &circuit, vec![vec![hash]]).unwrap(); //.unwrap().assert_satisfied()
        println!("Witness count: {}", prover.witness_count);
        println!("Copy count: {}", prover.copy_count);

        halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }

}

