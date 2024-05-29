pub mod poseidon;
pub mod scalar_mul;
pub mod primary_gate;
pub mod main_chip;
pub mod transcript;

use halo2_gadgets::poseidon::{primitives::{ConstantLength, Spec, Hash as inlineHash}, Hash, Pow5Chip, Pow5Config};
use halo2_base::{
    halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Chip, Value},
    halo2curves::{bn256::Fr as Fp, grumpkin::Fr as Fq},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance}, dev::MockProver},
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
};
use halo2_base::halo2_proofs::arithmetic::Field;
use rand::rngs::OsRng;
use std::marker::PhantomData;
use scalar_mul::ec_chip_strawman::ScalarMulChip;
use crate::{   
    util::arithmetic::{PrimeFieldBits, CurveAffine, TwoChainCurve, fe_to_fe, fe_from_bits_le, fe_to_bits_le, fe_truncated}, 
};
use rand::RngCore;
use self::{poseidon::{hash_chip::{PoseidonChip, PoseidonConfig}, spec::PoseidonSpec}, scalar_mul::ecc_deg6_hash::{ScalarMulChipConfig, ScalarMulConfigInputs, NUM_ADVICE_SM, NUM_FIXED_SM, NUM_INSTANCE_SM}};

pub const T: usize = 3;
pub const R: usize = 2;
pub const L: usize = 13;

pub const NUM_ADVICE: usize = T+1;
pub const NUM_CONSTANTS: usize = 2*T;

#[derive(Clone)]
pub struct CycleFoldChipConfig<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    poseidon: PoseidonConfig<C, T, R, L>,
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
        
        // let advices = [0; NUM_ADVICE].map(|_| meta.advice_column());
        // let constants = [0; NUM_CONSTANTS].map(|_| meta.fixed_column());
        // meta.enable_constant(constants[T]);

        // for col in &advices {
        //     meta.enable_equality(*col);
        // }

        // for col in &constants {
        //     meta.enable_equality(*col);
        // }

        // let instance = meta.instance_column();
        // meta.enable_equality(instance);

        // let poseidon = 
        //     PoseidonChip::<C, PoseidonSpec, T, R, L>::configure(
        //         meta,
        //         advices[..T].try_into().unwrap(),
        //         advices[T],
        //         constants[..T].try_into().unwrap(), 
        //         constants[T..].try_into().unwrap(), 
        //     );

        // let scalar_mul = ScalarMulChipConfig::<C>::configure(meta, advices[..NUM_ADVICE_SM].try_into().unwrap());

        let instance = [0; NUM_INSTANCE_SM].map(|_| meta.instance_column());
        for col in &instance {
            meta.enable_equality(*col);
        }

        let advices = [0; NUM_ADVICE_SM].map(|_| meta.advice_column());
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
            PoseidonChip::<C, PoseidonSpec, T, R, L>::configure(
                meta,
                advices[..T].try_into().unwrap(),
                advices[T],
                constants[..T].try_into().unwrap(), 
                constants[T..2*T].try_into().unwrap(), 
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
        let hash_chip = PoseidonChip::<C, PoseidonSpec, T, R, L>::construct(
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
    //use halo2_base::halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fr, Fq, G1Affine, G1}, grumpkin}};
    use halo2_gadgets::poseidon::{primitives::{ConstantLength, Spec, Hash as inlineHash}, Hash, Pow5Chip, Pow5Config};
    //use halo2_proofs::{arithmetic::Field, halo2curves::{ff::BatchInvert, group::{cofactor::CofactorCurveAffine, Curve, Group}, Coordinates, CurveAffine}};
    //use crate::{accumulation::protostar::ivc::halo2::{chips::{poseidon::spec::{PoseidonSpec, PoseidonSpecFp}, scalar_mul::ecc_deg6_hash::ScalarMulConfigInputs}, test::strawman::into_coordinates}, util::arithmetic::{fe_to_fe, fe_from_bits_le}};
    use super::{CyclefoldChip, L};
    //use rand::{rngs::OsRng, Rng};
    //use itertools::Itertools;
    use std::iter;

    use bitvec::vec;
    use itertools::Itertools;
    use std::{marker::PhantomData, time::Instant};
    use halo2_base::halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fq, Fr, G1Affine, G1}, grumpkin}, plonk::Assigned};
    use halo2_proofs::{arithmetic::Field, halo2curves::{ff::BatchInvert, group::{cofactor::CofactorCurveAffine, Curve, Group}, Coordinates, CurveAffine}};
    use crate::util::{arithmetic::{add_proj_comp, double_proj_comp, fe_from_bits_le, fe_to_fe, into_coordinates, is_identity_proj, is_scaled_identity_proj, powers, sub_proj, sub_proj_comp, ProjectivePoint}, izip_eq};
    use crate::accumulation::protostar::ivc::halo2::chips::poseidon::spec::{PoseidonSpec, PoseidonSpecFp};
    use super::{ScalarMulChip, ScalarMulConfigInputs};
    use rand::{rngs::OsRng, Rng};
    
    pub const NUM_CHALLENGE_BITS: usize = 128;

    // #[test]
    // fn cyclefold_chip() {

    //     use plotters::prelude::*;
    //     let root = BitMapBackend::new("CyclefoldChip.png", (1024, 3096)).into_drawing_area();
    //     root.fill(&WHITE).unwrap();
    //     let root = root.titled("CyclefoldChip", ("sans-serif", 60)).unwrap();

    //     let k = 11; 
    //     let mut rng = OsRng;
    //     let vec_len: usize = 129;
    //     let mut nark_x_vec = Vec::new();
    //     let mut nark_y_vec = Vec::new();
    //     let mut rnark_x_vec = Vec::new();
    //     let mut rnark_y_vec = Vec::new();
    //     let rbits = (0..vec_len-1).map(|_| rng.gen_bool(1.0 / 3.0)).collect_vec();
    //     let r_window_bits = rbits[1..].chunks(2).collect_vec();
    //     let r_le_bits = rbits.iter().map(|bit| 
    //         Value::known(if *bit {Fq::ONE} else {Fq::ZERO}))
    //         .collect_vec();

    //     // push after rbits, its first rbit
    //     let mut rbits_vec = Vec::new();
    //     rbits_vec = r_le_bits.clone();
    //     rbits_vec.push(r_le_bits[0]);

    //     let zero = G1Affine::identity();
    //     let mut p = G1Affine::random(&mut rng); 
    //     let acc = G1Affine::random(&mut rng);
    //     let p_single = p;
        
    //     // initial assumption: rbits[0] = 1
    //     nark_x_vec.push(Value::known(p_single.x));
    //     nark_y_vec.push(Value::known(p_single.y));
    //     rnark_x_vec.push(Value::known(p_single.x));
    //     rnark_y_vec.push(Value::known(p_single.y)); 


    //     // | row | r_bits_le | witness.x | witness.y | witness.x  |  witness.y |
    //     // | 0   |   0       |     x     |   y       |    x       |    y       |
    //     // | 1   |   0       |    2x     |  2y       |    6x      |   6y       |
    //     // | 2   |   1       |    4x     |  4y       |    5x      |   5y       |
    //     // | 3   |   1       |    8x     |  8y       |    24x     |   24y      |
    //     // | 4   |   1       |    16x    |  16y      |    29x     |   29y      |
    //     // | 5   |   1       |    32x    |  32y      |    61x     |   61y      |
    //     // |last | rbits[0]  |    x      |   y       |    60x     |   60y      |
    //     // |last | rbits[0]  |   acc.x   |  acc.y    |    62x     |   62y      |
    //     // |last | rbits[0]  |   acc`.x  |  acc`.y   |            |            |


    //     for idx in (1..vec_len-2).step_by(2) {
    //         p = <G1Affine as CurveAffine>::CurveExt::double(&p.into()).into(); 
    //         nark_x_vec.push(Value::known(p.x));
    //         nark_y_vec.push(Value::known(p.y));
    //         let p_single = p;

    //         p = <G1Affine as CurveAffine>::CurveExt::double(&p.into()).into();
    //         nark_x_vec.push(Value::known(p.x));
    //         nark_y_vec.push(Value::known(p.y)); 

    //         let p_triple = (p + p_single).to_affine();
    //         rnark_x_vec.push(Value::known(p_triple.x));
    //         rnark_y_vec.push(Value::known(p_triple.y)); 

    //         let acc_sel = match r_window_bits[idx/2] {
    //             [false, false] => zero,                             // 00
    //             [true, false] => p_single,                          // 10
    //             [false, true] => p,                                 // 01
    //             [true, true] =>  p_triple,                          // 11
    //             _ => panic!("Invalid window"),
    //         };

    //         let acc_prev = G1Affine::from_xy(rnark_x_vec[idx-1].assign().unwrap(), rnark_y_vec[idx-1].assign().unwrap()).unwrap();
    //         let acc_next = (acc_prev + acc_sel).to_affine();

    //         rnark_x_vec.push(Value::known(acc_next.x));
    //         rnark_y_vec.push(Value::known(acc_next.y));
    //     }

    //     // push last rbit 
    //     p = <G1Affine as CurveAffine>::CurveExt::double(&p.into()).into(); 
    //     nark_x_vec.push(Value::known(p.x));
    //     nark_y_vec.push(Value::known(p.y));

    //     if rbits[vec_len-2] {
    //         let acc_prev = G1Affine::from_xy(rnark_x_vec[vec_len-3].assign().unwrap(), rnark_y_vec[vec_len-3].assign().unwrap()).unwrap();
    //         let acc_next = (acc_prev + p).to_affine();
    //         rnark_x_vec.push(Value::known(acc_next.x));
    //         rnark_y_vec.push(Value::known(acc_next.y));
    //     } else {
    //         rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-3].assign().unwrap()));
    //         rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-3].assign().unwrap()));
    //     }

    //     // push last element as the first rbit
    //     nark_x_vec.push(Value::known(p_single.x));
    //     nark_y_vec.push(Value::known(p_single.y));

    //     // correct initial assumption
    //     if rbits[0] {
    //         rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-2].assign().unwrap()));
    //         rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-2].assign().unwrap()));
    //     } else {
    //         let acc_prev = G1Affine::from_xy(rnark_x_vec[vec_len-2].assign().unwrap(), rnark_y_vec[vec_len-2].assign().unwrap()).unwrap();
    //         let acc_next = (acc_prev - p_single).to_affine();
    //         rnark_x_vec.push(Value::known(acc_next.x));
    //         rnark_y_vec.push(Value::known(acc_next.y));
    //     }

    //     let r_lebits = rbits.iter().map(|bit| 
    //         if *bit {Fr::ONE} else {Fr::ZERO})
    //         .collect_vec();

    //     let r = fe_from_bits_le(r_lebits);
    //     let r_non_native: Fq = fe_to_fe(r);
    //     rbits_vec.push(Value::known(r_non_native)); // push last element as r
    //     let scalar_mul_given = (p_single * r).to_affine();
    //     let scalar_mul_calc = G1Affine::from_xy(rnark_x_vec[vec_len-1].assign().unwrap(), rnark_y_vec[vec_len-1].assign().unwrap()).unwrap();
    //     let acc_prime_calc  = (scalar_mul_calc + acc).to_affine();
    //     let acc_prime_given = (scalar_mul_given + acc).to_affine(); // todo this should be from cyclefold struct
    //     assert_eq!(scalar_mul_given, scalar_mul_calc);
    //     assert_eq!(acc_prime_calc, acc_prime_given);

    //     let inputs =
    //         ScalarMulConfigInputs::<grumpkin::G1Affine> { 
    //             nark_x_vec: nark_x_vec.clone(), nark_y_vec: nark_y_vec.clone(), r: Value::known(r_non_native),
    //             rbits_vec: rbits_vec.clone(), rnark_x_vec: rnark_x_vec.clone(), rnark_y_vec: rnark_y_vec.clone(), 
    //             acc_x: Value::known(acc.x), acc_y: Value::known(acc.y), 
    //             acc_prime_calc_x: Value::known(acc_prime_calc.x), 
    //             acc_prime_calc_y: Value::known(acc_prime_calc.y), 
    //             acc_prime_given_x: Value::known(acc_prime_given.x), 
    //             acc_prime_given_y: Value::known(acc_prime_given.y) 
    //         };

    //     let mut messages_vec = Vec::new();
    //     let message_vec = iter::empty()
    //         .chain([r_non_native])
    //         .chain(into_coordinates(&p_single).into_iter())
    //         .chain(into_coordinates(&acc).into_iter())
    //         .collect_vec();
        
    //     let input_len = L/4;
    //     for i in 0..input_len {
    //         if i == 0 {
    //             messages_vec.extend_from_slice(&message_vec);
    //         } else {
    //             messages_vec.extend_from_slice(&message_vec[1..]);
    //         }
    //     }

    //     let message: [Fq; L] =
    //     match messages_vec.try_into() {
    //         Ok(arr) => arr,
    //         Err(_) => panic!("Failed to convert Vec to Array"),
    //     };
    //     assert_eq!(L, message.len());

    //     let hash =
    //         inlineHash::<Fq, PoseidonSpec, ConstantLength<L>, 5, 4>::init().hash(message);

    //     let circuit = CyclefoldChip::<grumpkin::G1Affine> { inputs: vec![inputs; input_len] };
    //     MockProver::run(k, &circuit, vec![vec![hash]]).unwrap().assert_satisfied();

    //     halo2_base::halo2_proofs::dev::CircuitLayout::default()
    //         .render(k, &circuit, &root)
    //         .unwrap();
    // }

    #[test]
    fn cyclefold_chip() {

        use plotters::prelude::*;
        let root = BitMapBackend::new("CyclefoldChip_t3.png", (1024, 3096)).into_drawing_area();
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
            .chain(into_coordinates(&p_single).into_iter())
            .chain(into_coordinates(&comm_affine).into_iter())
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
        MockProver::run(k, &circuit, vec![vec![hash]]).unwrap().assert_satisfied();

        halo2_base::halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }

}

