pub mod poseidon;
pub mod scalar_mul;

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
use scalar_mul::ec_chip::ScalarMulChip;
use crate::{   
    accumulation::protostar::ivc::cyclefold::CycleFoldInputs, 
    util::arithmetic::{PrimeFieldBits, CurveAffine, TwoChainCurve, fe_to_fe, fe_from_bits_le, fe_to_bits_le, fe_truncated}, 
};
use rand::RngCore;
use self::{poseidon::{hash_chip::{PoseidonChipTest, PoseidonConfigTest}, spec::PoseidonSpecFp as PoseidonSpec}, scalar_mul::ec_chip::{ScalarMulChipConfig, ScalarMulConfigInputs, NUM_ADVICE}};

pub const T: usize = 5;
pub const R: usize = 4;
pub const L: usize = 25;

#[derive(Clone)]
pub struct CycleFoldTestChipConfig {
    poseidon: PoseidonConfigTest<T, R, L>,
    scalar_mul: ScalarMulChipConfig,
    instance: Column<Instance>,
}

#[derive(Clone, Default)]
pub struct CyclefoldTestChip { pub inputs: Vec<ScalarMulConfigInputs> }

impl Circuit<Fq> for CyclefoldTestChip
{
    type Params = ();
    type Config = CycleFoldTestChipConfig; 
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        
        let advices = [0; 6].map(|_| meta.advice_column());
        let constants = [0; 10].map(|_| meta.fixed_column());
        meta.enable_constant(constants[5]);

        for col in &advices {
            meta.enable_equality(*col);
        }

        for col in &constants {
            meta.enable_equality(*col);
        }

        let instance = meta.instance_column();
        meta.enable_equality(instance);

        let poseidon = 
            PoseidonChipTest::<PoseidonSpec, T, R, L>::configure(
                meta,
                advices[..5].try_into().unwrap(),
                advices[5],
                constants[..5].try_into().unwrap(), 
                constants[5..].try_into().unwrap(), 
            );

        let scalar_mul = ScalarMulChipConfig::configure(meta, advices[..NUM_ADVICE].try_into().unwrap());

        Self::Config {
            poseidon,
            scalar_mul,
            instance,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), Error> {

        let mut hash_inputs = Vec::new();
        let hash_chip = PoseidonChipTest::<PoseidonSpec, 5, 4, L>::construct(
            config.poseidon,
        );

        for i in 0..self.inputs.len() {
            if i == 0 {
                hash_inputs.extend_from_slice(&config.scalar_mul.assign(layouter.namespace(|| "ScalarMulChip"), self.inputs[i].clone(), 1)?);
            } else {
                hash_inputs.extend_from_slice(&config.scalar_mul.assign(layouter.namespace(|| "ScalarMulChip"), self.inputs[i].clone(), 1)?[1..]);
            }
        }

        let message: [AssignedCell<Fq, Fq>; L] =
        match hash_inputs.try_into() {
            Ok(arr) => arr,
            Err(_) => panic!("Failed to convert Vec to Array"),
        };

        let hash = hash_chip.hash(
            layouter.namespace(|| "perform poseidon hash"),
            message,
        )?;

        layouter.constrain_instance(hash.cell(), config.instance, 0)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use halo2_base::halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fr, Fq, G1Affine, G1}, grumpkin}};
    use halo2_gadgets::poseidon::{primitives::{ConstantLength, Spec, Hash as inlineHash}, Hash, Pow5Chip, Pow5Config};
    use halo2_proofs::{halo2curves::{Coordinates, group::{Group, Curve, cofactor::CofactorCurveAffine}, CurveAffine}, arithmetic::Field};
    use crate::{accumulation::protostar::ivc::halo2::{chips::{poseidon::spec::{PoseidonSpec, PoseidonSpecFp}, scalar_mul::ec_chip::ScalarMulConfigInputs}, test::strawman::into_coordinates}, util::arithmetic::{fe_to_fe, fe_from_bits_le}};
    use super::{CyclefoldTestChip, L};
    use rand::{rngs::OsRng, Rng};
    use itertools::Itertools;
    use std::iter;

    // fn form_circuit(){
        
    // }
        
    #[test]
    fn cyclefold_chip() {

        use plotters::prelude::*;
        let root = BitMapBackend::new("CyclefoldTestChip.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("CyclefoldTestChip", ("sans-serif", 60)).unwrap();

        let k = 11; 
        let mut rng = OsRng;
        let vec_len: usize = 129;
        let mut nark_x_vec = Vec::new();
        let mut nark_y_vec = Vec::new();
        let mut rnark_x_vec = Vec::new();
        let mut rnark_y_vec = Vec::new();
        let rbits = (0..vec_len-1).map(|_| rng.gen_bool(1.0 / 3.0)).collect_vec();
        let r_window_bits = rbits[1..].chunks(2).collect_vec();
        let r_le_bits = rbits.iter().map(|bit| 
            Value::known(if *bit {Fq::ONE} else {Fq::ZERO}))
            .collect_vec();

        // push after rbits, its first rbit
        let mut rbits_vec = Vec::new();
        rbits_vec = r_le_bits.clone();
        rbits_vec.push(r_le_bits[0]);

        let zero = G1Affine::identity();
        let mut p = G1Affine::random(&mut rng); 
        let acc = G1Affine::random(&mut rng);
        let p_single = p;
        
        // initial assumption: rbits[0] = 1
        nark_x_vec.push(Value::known(p_single.x));
        nark_y_vec.push(Value::known(p_single.y));
        rnark_x_vec.push(Value::known(p_single.x));
        rnark_y_vec.push(Value::known(p_single.y)); 


        // | row | r_bits_le | witness.x | witness.y | witness.x  |  witness.y |
        // | 0   |   0       |     x     |   y       |    x       |    y       |
        // | 1   |   0       |    2x     |  2y       |    6x      |   6y       |
        // | 2   |   1       |    4x     |  4y       |    5x      |   5y       |
        // | 3   |   1       |    8x     |  8y       |    24x     |   24y      |
        // | 4   |   1       |    16x    |  16y      |    29x     |   29y      |
        // | 5   |   1       |    32x    |  32y      |    61x     |   61y      |
        // |last | rbits[0]  |    x      |   y       |    60x     |   60y      |
        // |last | rbits[0]  |   acc.x   |  acc.y    |    62x     |   62y      |
        // |last | rbits[0]  |   acc`.x  |  acc`.y   |            |            |


        for idx in (1..vec_len-2).step_by(2) {
            p = <G1Affine as CurveAffine>::CurveExt::double(&p.into()).into(); 
            nark_x_vec.push(Value::known(p.x));
            nark_y_vec.push(Value::known(p.y));
            let p_single = p;

            p = <G1Affine as CurveAffine>::CurveExt::double(&p.into()).into();
            nark_x_vec.push(Value::known(p.x));
            nark_y_vec.push(Value::known(p.y)); 

            let p_triple = (p + p_single).to_affine();
            rnark_x_vec.push(Value::known(p_triple.x));
            rnark_y_vec.push(Value::known(p_triple.y)); 

            let acc_sel = match r_window_bits[idx/2] {
                [false, false] => zero,                             // 00
                [true, false] => p_single,                          // 10
                [false, true] => p,                                 // 01
                [true, true] =>  p_triple,                          // 11
                _ => panic!("Invalid window"),
            };

            let acc_prev = G1Affine::from_xy(rnark_x_vec[idx-1].assign().unwrap(), rnark_y_vec[idx-1].assign().unwrap()).unwrap();
            let acc_next = (acc_prev + acc_sel).to_affine();

            rnark_x_vec.push(Value::known(acc_next.x));
            rnark_y_vec.push(Value::known(acc_next.y));
        }

        // push last rbit 
        p = <G1Affine as CurveAffine>::CurveExt::double(&p.into()).into(); 
        nark_x_vec.push(Value::known(p.x));
        nark_y_vec.push(Value::known(p.y));

        if rbits[vec_len-2] {
            let acc_prev = G1Affine::from_xy(rnark_x_vec[vec_len-3].assign().unwrap(), rnark_y_vec[vec_len-3].assign().unwrap()).unwrap();
            let acc_next = (acc_prev + p).to_affine();
            rnark_x_vec.push(Value::known(acc_next.x));
            rnark_y_vec.push(Value::known(acc_next.y));
        } else {
            rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-3].assign().unwrap()));
            rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-3].assign().unwrap()));
        }

        // push last element as the first rbit
        nark_x_vec.push(Value::known(p_single.x));
        nark_y_vec.push(Value::known(p_single.y));

        // correct initial assumption
        if rbits[0] {
            rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-2].assign().unwrap()));
            rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-2].assign().unwrap()));
        } else {
            let acc_prev = G1Affine::from_xy(rnark_x_vec[vec_len-2].assign().unwrap(), rnark_y_vec[vec_len-2].assign().unwrap()).unwrap();
            let acc_next = (acc_prev - p_single).to_affine();
            rnark_x_vec.push(Value::known(acc_next.x));
            rnark_y_vec.push(Value::known(acc_next.y));
        }

        let r_lebits = rbits.iter().map(|bit| 
            if *bit {Fr::ONE} else {Fr::ZERO})
            .collect_vec();

        let r = fe_from_bits_le(r_lebits);
        let r_non_native: Fq = fe_to_fe(r);
        rbits_vec.push(Value::known(r_non_native)); // push last element as r
        let scalar_mul_given = (p_single * r).to_affine();
        let scalar_mul_calc = G1Affine::from_xy(rnark_x_vec[vec_len-1].assign().unwrap(), rnark_y_vec[vec_len-1].assign().unwrap()).unwrap();
        let acc_prime_calc  = (scalar_mul_calc + acc).to_affine();
        let acc_prime_given = (scalar_mul_given + acc).to_affine(); // todo this should be from cyclefold struct
        assert_eq!(scalar_mul_given, scalar_mul_calc);
        assert_eq!(acc_prime_calc, acc_prime_given);

        let inputs =
            ScalarMulConfigInputs { 
                nark_x_vec: nark_x_vec.clone(), nark_y_vec: nark_y_vec.clone(), r: Value::known(r_non_native),
                rbits_vec: rbits_vec.clone(), rnark_x_vec: rnark_x_vec.clone(), rnark_y_vec: rnark_y_vec.clone(), 
                acc_x: Value::known(acc.x), acc_y: Value::known(acc.y), 
                acc_prime_calc_x: Value::known(acc_prime_calc.x), 
                acc_prime_calc_y: Value::known(acc_prime_calc.y), 
                acc_prime_given_x: Value::known(acc_prime_given.x), 
                acc_prime_given_y: Value::known(acc_prime_given.y) 
            };

        let mut messages_vec = Vec::new();
        let message_vec = iter::empty()
            .chain([r_non_native])
            .chain(into_coordinates(&p_single).into_iter())
            .chain(into_coordinates(&acc).into_iter())
            .collect_vec();
        
        let input_len = L/4;
        // for _ in 0..input_len {
        //     messages_vec.extend_from_slice(&message_vec);
        // }

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
            inlineHash::<_, PoseidonSpecFp, ConstantLength<L>, 5, 4>::init().hash(message);

        let circuit = CyclefoldTestChip { inputs: vec![inputs; input_len] };
        MockProver::run(k, &circuit, vec![vec![hash]]).unwrap().assert_satisfied();

        halo2_base::halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }

}

