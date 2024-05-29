use halo2_base::{halo2_proofs::
    {circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector, Expression, Assigned, Fixed},
    poly::Rotation, 
    halo2curves::{bn256::{G1Affine, G2Affine, G1}, grumpkin::{self, Fr as Fq}},
}, 
gates::flex_gate::{FlexGateConfig, FlexGateConfigParams},
utils::{CurveAffineExt, ScalarField, BigPrimeField},
};
use halo2_base::{
    gates::GateInstructions,
    utils::bit_length,
    AssignedValue, Context,
};
use halo2_base::halo2_proofs::halo2curves::{group::Group, grumpkin::Fr, Coordinates, CurveAffine};
use itertools::Itertools;
use std::{
    iter,
    marker::PhantomData,
    sync::{RwLock, RwLockReadGuard},
};

use crate::util::arithmetic::{TwoChainCurve, PrimeFieldBits, Field};

pub const NUM_ADVICE_SM: usize = 6;
pub const NUM_FIXED: usize = 1;
pub const NUM_SELECTOR: usize = 2;

#[derive(Clone, Debug)]
pub struct ScalarMulChipConfig<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    witness: [Column<Advice>; NUM_ADVICE_SM],
    selector: Selector,
    _marker: PhantomData<C>,
}

impl<C> ScalarMulChipConfig<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub fn configure(meta: &mut ConstraintSystem<C::Scalar>, advices: [Column<Advice>; NUM_ADVICE_SM]) -> Self {

        // | row | r_bits_0  |   point   |   acc.x   |   acc.y   |  lambda   | 
        // | 0   |    0      |     x     |    y      |    y      |    1      | 
        // | 1   |    1      |     y     |    2y     |    2y     |    0      |
        // | 2   |    1      |     x     |    4y     |    4y     |    1      | 
        // | 3   |    1      |     y     |    16y    |    16y    |    0      |

        let [col_rbits, col_ptx, col_pty, col_acc_x, col_acc_y, col_lambda] = 
            advices;
    
        let q_ec_double_add = meta.selector();

            meta.create_gate("q_ec_double_add", |meta| {

                let q_ec_double_add = meta.query_selector(q_ec_double_add);
                let r = meta.query_advice(col_rbits, Rotation(1));
                let x = meta.query_advice(col_ptx, Rotation(0));
                let y = meta.query_advice(col_pty, Rotation(0));
                let acc_x = meta.query_advice(col_acc_x, Rotation(0));
                let acc_y = meta.query_advice(col_acc_y, Rotation(0));

                let acc_next_x = meta.query_advice(col_acc_x, Rotation(1));
                let acc_next_y = meta.query_advice(col_acc_y, Rotation(1));
                let lambda = meta.query_advice(col_lambda, Rotation(1));
                let acc_x_sq = acc_x.clone() * acc_x.clone();
                let acc_y_sq = acc_y.clone() * acc_y.clone();

                let zero = Expression::Constant(C::Scalar::ZERO);
                let one = Expression::Constant(C::Scalar::ONE);
                let two = Expression::Constant(C::Scalar::from(2));
                let three = Expression::Constant(C::Scalar::from(3));
                let nine = Expression::Constant(C::Scalar::from(9));
                let eight = Expression::Constant(C::Scalar::from(8));
                let twenty_four = Expression::Constant(C::Scalar::from(24));
                let twenty_seven = Expression::Constant(C::Scalar::from(27)); // nine * b
                let seventy_two = Expression::Constant(C::Scalar::from(72)); // twenty_four * b
                
                // pt double, b = 3 for bn254
                //  x' = 2xy(y^2 - 9bz^2)
                //  y' = (y^2 - 9bz^2)(y^2 + 3bz^2) + 24*b*y^2*z^2 
                //  z' = 8y^3*z

                // simplified for b = 3, 
                let acc_double_x = two * acc_x.clone() * acc_y.clone() * (acc_y_sq.clone() - twenty_seven.clone());
                let acc_double_y = (acc_y_sq.clone() - twenty_seven.clone()) 
                                 * (acc_y_sq.clone() + nine.clone()) + seventy_two.clone() * acc_y_sq.clone();
                let acc_double_z = eight.clone() * acc_y_sq.clone() * acc_y.clone();

                // choice poly in projective coordinates, identity is (0,1,0)
                let sel_x = r.clone() * x.clone(); 
                let sel_y = (one.clone() - r.clone()) + r.clone() * y.clone(); 
                let sel_z = r.clone(); 

                // X_1 = acc_next_x, Y_2 = sel_y
                // X_3 &= (X_1(-Y_2) + X_2Y_1)(Y_1(-Y_2) - 3bZ_1Z_2) \\ x1y1
                //  - (Y_1Z_2 - Y_2Z_1)(3b(X_1Z_2 + X_2Z_1)), \\
                // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) \\ y1^2
                //  + (Y_1(-Y_2) + 3bZ_1Z_2)(Y_1(-Y_2) - 3bZ_1Z_2), \\
                // Z_3 &= (Y_1Z_2 - Y_2Z_1)(Y_1(-Y_2) + 3bZ_1Z_2) \\ z1y1
                //  + (X_1(-Y_2) + X_2Y_1)(3X_1X_2).

                // simplified for b = 3, 
                let acc_sub_x = (acc_next_x.clone() * ( - sel_y.clone()) + sel_x.clone() * acc_next_y.clone())
                    * ( acc_next_y.clone() * (- sel_y.clone()) - nine.clone() * sel_z.clone())
                    - ( acc_next_y.clone() * sel_z.clone() - sel_y.clone())
                    * ( nine.clone() * (acc_next_x.clone() * sel_z.clone() + sel_x.clone()));
                
                let acc_sub_y = (three.clone() * acc_next_x.clone() * sel_x.clone()) 
                    * ( nine.clone() * ( acc_next_x.clone() * sel_z.clone() + sel_x.clone()))
                    + ( acc_next_y.clone() * (- sel_y.clone()) + nine.clone() * sel_z.clone()) 
                    * ( - sel_y.clone() * acc_next_y.clone() - nine.clone() * sel_z.clone());

                let acc_sub_z = (acc_next_y.clone() * sel_z.clone() - sel_y.clone())
                    * ( acc_next_y.clone() * (- sel_y.clone()) + nine.clone() * sel_z.clone())
                    + ( - acc_next_x.clone() * sel_y.clone() + sel_x.clone() * acc_next_y.clone())
                    * ( three.clone() * acc_next_x.clone() * sel_x.clone());

                vec![q_ec_double_add.clone() * (acc_sub_x - acc_double_x.clone() * lambda.clone()),
                     q_ec_double_add.clone() * (acc_sub_y - acc_double_y.clone() * lambda.clone()),
                     q_ec_double_add.clone() * (acc_sub_z - acc_double_z.clone() * lambda.clone())]

            });


        Self { 
            witness: [col_rbits, col_ptx, col_pty, col_acc_x, col_acc_y, col_lambda], 
            selector: q_ec_double_add,
            _marker: PhantomData 
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        inputs: ScalarMulConfigInputs<C>,
    ) -> Result<(), Error> {

        layouter.assign_region(
            || "ScalarMulChipConfig assign",
            |mut region| {

        // | row |  r_bits   |   point   |   acc.x   |   acc.y   |  lambda   | 
        // | 1   |    0      |     x     |    x      |    y      |    1      | 
        // | 2   |    1      |     y     |    2y     |    2y     |    0      |
        // | 3   |    1      |     x     |    4y     |    4y     |    1      | 
        // | 4   |    1      |     y     |    16y    |    16y    |    0      |

            let rbits_vec_len = inputs.rbits_vec.len();
                for row in 0..rbits_vec_len {
                    region.assign_advice(|| "r_vec",self.witness[0], row, || inputs.rbits_vec[row])?;
                    region.assign_advice(|| "ptx_vec",self.witness[1], row, || inputs.ptx_vec[row])?;
                    region.assign_advice(|| "pty_vec",self.witness[2], row, || inputs.pty_vec[row])?;
                    region.assign_advice(|| "acc_x_vec",self.witness[3], row, || inputs.acc_x_vec[row])?;
                    region.assign_advice(|| "acc_y_vec",self.witness[4], row, || inputs.acc_y_vec[row])?;
                    region.assign_advice(|| "acc_z_vec",self.witness[5], row, || inputs.lambda_vec[row])?;

                    if row != rbits_vec_len - 1 {
                        self.selector.enable(&mut region, row)?;
                    }
                }         
                                
                Ok(())
            },
        )
    }
}

#[derive(Debug)]
pub struct ScalarMulChipInputs<F, C> 
{   
    pub r_le_bits: Vec<F>,
    pub r: F,
    pub nark_comm: C,
    pub acc_comm: C,
    pub acc_prime_comm: C,
}

#[derive(Clone, Default)]
pub struct ScalarMulConfigInputs<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub rbits_vec: Vec<Value<C::Scalar>>,
    pub ptx_vec: Vec<Value<C::Scalar>>,
    pub pty_vec: Vec<Value<C::Scalar>>,
    pub acc_x_vec: Vec<Value<C::Scalar>>,
    pub acc_y_vec: Vec<Value<C::Scalar>>,
    pub lambda_vec: Vec<Value<C::Scalar>>,
    // pub r: Value<C::Scalar>,
}

#[derive(Clone, Default)]
pub struct ScalarMulChip<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{ 
    pub inputs: Vec<ScalarMulConfigInputs<C>> 
}

impl<C> Circuit<C::Scalar> for ScalarMulChip<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    type Params = ();
    type Config = ScalarMulChipConfig<C>; 
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        let advices = [0; NUM_ADVICE_SM].map(|_| meta.advice_column());
        ScalarMulChipConfig::configure(meta, advices)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {

        for inputs in self.inputs.iter() {
            config.assign(layouter.namespace(|| "ScalarMulChip"), inputs.clone())?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use bitvec::vec;
    use itertools::Itertools;
    use std::{marker::PhantomData, time::Instant};
    use halo2_base::halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fq, Fr, G1Affine, G1}, grumpkin}, plonk::Assigned};
    use halo2_proofs::{arithmetic::Field, halo2curves::{ff::BatchInvert, group::{cofactor::CofactorCurveAffine, Curve, Group}, Coordinates, CurveAffine}};
    use crate::util::{arithmetic::{add_proj_comp, double_proj_comp, fe_from_bits_le, fe_to_fe, is_identity_proj, is_scaled_identity_proj, sub_aff_proj, sub_proj_comp, ProjectivePoint}, izip_eq};
    use super::{ScalarMulChip, ScalarMulConfigInputs};
    use rand::{rngs::OsRng, Rng};
        
    #[test]
    fn ec_vec() {

        use plotters::prelude::*;
        let root = BitMapBackend::new("ECChip_deg6.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("ECChip_deg6", ("sans-serif", 60)).unwrap();

        let k = 7; 
        let mut rng = OsRng;
        let vec_len: usize = 4;

        let mut rbits = Vec::new();
        rbits.extend([true, false, true, true]);
        //rbits.extend((0..vec_len).map(|_| rng.gen_bool(1.0 / 3.0)));
        let mut rbits_vec = rbits.iter().map(|bit| 
            Value::known(if *bit {Fq::ONE} else {Fq::ZERO}))
            .rev()
            .collect_vec();
        
        // rbits_vec.insert(0, Value::known(Fq::ZERO)); // push first element as 0/1 doesnt matter

        // 3.26 algo for double add, Guide to ECC
        // let mut p = G1Affine::random(&mut rng); 
        // let acc_prev = G1Affine::identity().to_affine();
        // for i in 0..vec_len {
        //     acc_prev = if rbits[i] { (acc_prev + p).to_affine() } else { acc_prev };
        //     p = G1::double(&p.into()).to_affine(); 
        //     acc_x_vec.push(Value::known(acc_prev.x));
        //     acc_y_vec.push(Value::known(acc_prev.y)); 
        // }

        // 3.27 algo for double add, Guide to ECC
        // let p = G1Affine::random(&mut rng); 
        // let mut acc_prev = G1Affine::identity().to_affine();
        // for i in (0..vec_len) {
        //     acc_prev = G1::double(&acc_prev.into()).to_affine();
        //     acc_prev = if rbits_rev[i] { (acc_prev + p).to_affine() } else { acc_prev }; 
        //     acc_x_vec.push(Value::known(acc_prev.x));
        //     acc_y_vec.push(Value::known(acc_prev.y)); 
        // }
        
        let witness_gen_time = Instant::now();
        let zero = ProjectivePoint::identity();
        let mut p = G1Affine::identity();
        while p == G1Affine::identity() {
            p = G1Affine::random(&mut rng);
        }

        let p_single = p; 
        let mut acc_prev = ProjectivePoint::identity();
        let mut ptx_vec = Vec::new();
        let mut pty_vec = Vec::new();
        let mut acc_prev_xvec = Vec::new();
        let mut acc_prev_yvec = Vec::new();
        let mut acc_prev_zvec = Vec::new();

        let mut lhs_double_xvec = Vec::new();
        let mut lhs_double_yvec = Vec::new();
        let mut lhs_double_zvec = Vec::new();
        let mut lhs_zvec = Vec::new();
        let mut rhs_zvec = Vec::new();

        // acc_x_vec.push(Value::known(acc_prev.x));
        // acc_y_vec.push(Value::known(acc_prev.y)); 
        // acc_z_vec.push(Value::known(acc_prev.z));
        // let rbits_rev = rbits.iter().skip(1).rev().cloned().collect_vec();
        let rbits_rev = rbits.iter().rev().cloned().collect_vec();

        for i in 0..vec_len {
            let choice_proj = if rbits_rev[i] { 
                ProjectivePoint::new(p_single.x, p_single.y, Fq::one())
            } else {zero};
            acc_prev = double_proj_comp(acc_prev);

            let lhs = acc_prev;
            acc_prev = add_proj_comp(acc_prev, choice_proj);
            acc_prev_xvec.push(acc_prev.x);
            acc_prev_yvec.push(acc_prev.y);
            acc_prev_zvec.push(acc_prev.z);

            lhs_double_xvec.push(lhs.x);
            lhs_double_yvec.push(lhs.y);
            lhs_double_zvec.push(lhs.z);
        }

        let batch_invert_time = std::time::Instant::now();
        acc_prev_zvec.batch_invert();
        println!("batch_invert_time1: {:?}", batch_invert_time.elapsed());

        let acc_xvec = acc_prev_zvec.iter().zip(acc_prev_xvec.clone()).map(|(lhs, rhs)| lhs*rhs).collect_vec();
        let acc_yvec = acc_prev_zvec.iter().zip(acc_prev_yvec.clone()).map(|(lhs, rhs)| lhs*rhs).collect_vec();

        for i in 0..vec_len {
            let acc_prev_proj = ProjectivePoint::new(acc_xvec[i], acc_yvec[i], Fq::one());
            let lhs_double_proj = ProjectivePoint::new(lhs_double_xvec[i], lhs_double_yvec[i], lhs_double_zvec[i]);
            let p_single_proj = if rbits_rev[i] { 
                ProjectivePoint::new(p_single.x, p_single.y, Fq::one())
            } else {zero};

            let rhs = sub_proj_comp(acc_prev_proj, p_single_proj);
            if is_identity_proj(rhs) && is_identity_proj(lhs_double_proj) {
                lhs_zvec.push(Fq::one());
                rhs_zvec.push(Fq::one());
            } else if is_identity_proj(rhs) && is_scaled_identity_proj(lhs_double_proj) {
                lhs_zvec.push(lhs_double_proj.y);
                rhs_zvec.push(Fq::one());
            } else if is_identity_proj(lhs_double_proj) && is_scaled_identity_proj(rhs) {
                lhs_zvec.push(Fq::one());
                rhs_zvec.push(rhs.y);
            } else {
                lhs_zvec.push(lhs_double_zvec[i]);
                rhs_zvec.push(rhs.z);
            }
        }

        let batch_invert_time = std::time::Instant::now();
        lhs_zvec.batch_invert();
        println!("batch_invert_time2: {:?}", batch_invert_time.elapsed());
        
        let acc_x_vec = acc_xvec.iter().map(|fe| Value::known(*fe)).collect_vec();
        let acc_y_vec = acc_yvec.iter().map(|fe| Value::known(*fe)).collect_vec();
        let lambda_vec = lhs_zvec.iter().zip(rhs_zvec).map(|(lhs, rhs)| Value::known(lhs*rhs)).collect_vec();

        for i in 0..vec_len {
            ptx_vec.push(Value::known(p.x));
            pty_vec.push(Value::known(p.y));
        }

        println!("witness_gen_time: {:?}", witness_gen_time.elapsed());

        // | row |  r_bits   |   point   |   acc.x   |   acc.y   |  lambda   | 
        // | 1   |    1      |     x     |    x      |    y      |    1      | 
        // | 2   |    0      |     y     |    2y     |    2y     |    0      |
        // | 3   |    1      |     x     |    4y     |    4y     |    1      | 
        // | 4   |    1      |     y     |    16y    |    16y    |    0      |

        let rbits_native = rbits.iter().map(|bit| 
            if *bit {Fr::ONE} else {Fr::ZERO})
            .collect_vec();

        let r = fe_from_bits_le(rbits_native);
        // let r_non_native: Fq = fe_to_fe(r);
        // rbits_vec.push(Value::known(r_non_native)); // push last element as r
        let scalar_mul_given = p * r;
        let scalar_mul_proj = (acc_prev_xvec.last().unwrap(), acc_prev_yvec.last().unwrap(), acc_prev_zvec.last().unwrap());
        assert_eq!(scalar_mul_given.x, scalar_mul_proj.0 * scalar_mul_given.z * scalar_mul_proj.2);
        assert_eq!(scalar_mul_given.y, scalar_mul_proj.1 * scalar_mul_given.z * scalar_mul_proj.2);
        
        let scalar_mul_affine = G1Affine::from_xy(*acc_xvec.last().unwrap(), *acc_yvec.last().unwrap()).unwrap();
        assert_eq!(scalar_mul_affine, scalar_mul_given.to_affine());

        let inputs =
            ScalarMulConfigInputs::<grumpkin::G1Affine> { 
                rbits_vec, 
                ptx_vec, 
                pty_vec,
                acc_x_vec, 
                acc_y_vec, 
                lambda_vec, 
            };   

        let circuit = ScalarMulChip::<grumpkin::G1Affine> { inputs: vec![inputs] };
        MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();

        halo2_base::halo2_proofs::dev::CircuitLayout::default()
        .render(k, &circuit, &root)
        .unwrap();
    }

}