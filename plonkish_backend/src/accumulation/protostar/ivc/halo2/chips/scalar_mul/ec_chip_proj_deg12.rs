use halo2_base::{gates::flex_gate::{FlexGateConfig, FlexGateConfigParams}, halo2_proofs::
    {circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value}, halo2curves::{bn256::{G1Affine, G2Affine, G1}, grumpkin::{self, Fr as Fq}}, plonk::{Advice, Assigned, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Fixed, Selector}, poly::Rotation
}, utils::{BigPrimeField, CurveAffineExt, ScalarField}
};
use halo2_base::{
    gates::GateInstructions,
    utils::bit_length,
    AssignedValue, Context,
};
use halo2_proofs::halo2curves::{group::Group, grumpkin::Fr, Coordinates, CurveAffine};
use itertools::Itertools;
use std::{
    iter,
    marker::PhantomData,
    sync::{RwLock, RwLockReadGuard},
};

use crate::util::arithmetic::{TwoChainCurve, PrimeFieldBits, Field, BatchInvert};

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
    selector: [Selector; NUM_SELECTOR],
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
        // | 0   |    0      |     x     |    x      |    y      |    1      | 
        // | 1   |    1      |     y     |    2y     |    2y     |    0      |
        // | 2   |    1      |     x     |    4y     |    4y     |    1      | 
        // | 3   |    1      |     y     |    16y    |    16y    |    0      |

        let [col_rbits, col_ptx, col_pty, col_acc_x, col_acc_y, col_acc_z] = 
            advices;
    
        let [q_first_row, q_ec_double_add] = [(); NUM_SELECTOR].map(|_| meta.selector());

            // meta.create_gate("q_first_row", |meta| {

            //     let q_first_row = meta.query_selector(q_first_row);
            //     let one = Expression::Constant(C::Scalar::ONE);
            //     let zero = Expression::Constant(C::Scalar::ZERO);
            //     let r = meta.query_advice(col_rbits, Rotation(0));
            //     let x = meta.query_advice(col_ptx, Rotation(0));
            //     let y = meta.query_advice(col_pty, Rotation(0));
            //     let acc_x = meta.query_advice(col_acc_x, Rotation(0));
            //     let acc_y = meta.query_advice(col_acc_y, Rotation(0));
            //     let acc_z = meta.query_advice(col_acc_z, Rotation(0));

            //     vec![q_first_row.clone() * (acc_x.clone() - x.clone() * r.clone()), 
            //          q_first_row.clone() * (acc_y.clone() - y.clone() * r.clone()), 
            //          q_first_row.clone() * (acc_z.clone() - one.clone())]
            // });

            meta.create_gate("q_ec_double_add", |meta| {

                let q_ec_double_add = meta.query_selector(q_ec_double_add);
                let r = meta.query_advice(col_rbits, Rotation(1));
                let x = meta.query_advice(col_ptx, Rotation(0));
                let y = meta.query_advice(col_pty, Rotation(0));
                let acc_x = meta.query_advice(col_acc_x, Rotation(0));
                let acc_y = meta.query_advice(col_acc_y, Rotation(0));
                let acc_z = meta.query_advice(col_acc_z, Rotation(0));

                let acc_next_x = meta.query_advice(col_acc_x, Rotation(1));
                let acc_next_y = meta.query_advice(col_acc_y, Rotation(1));
                let acc_next_z = meta.query_advice(col_acc_z, Rotation(1));

                let zero = Expression::Constant(C::Scalar::ZERO);
                let one = Expression::Constant(C::Scalar::ONE);
                let two = Expression::Constant(C::Scalar::from(2));
                let three = Expression::Constant(C::Scalar::from(3));

                let b = three.clone();
                let nine = Expression::Constant(C::Scalar::from(9));
                let eight = Expression::Constant(C::Scalar::from(8));
                let twenty_four = Expression::Constant(C::Scalar::from(24));
                let twenty_seven = Expression::Constant(C::Scalar::from(27)); // nine * b
                let seventy_two = Expression::Constant(C::Scalar::from(72)); // twenty_four * b
                let acc_x_sq = acc_x.clone() * acc_x.clone();
                let acc_y_sq = acc_y.clone() * acc_y.clone();
                let acc_z_sq = acc_z.clone() * acc_z.clone();

                
                // pt double, b = 3 for bn254
                //  x' = 2xy(y^2 - 9bz^2)
                //  y' = (y^2 - 9bz^2)(y^2 + 3bz^2) + 24*b*y^2*z^2
                //  z' = 8y^3*z

                // simplified for b = 3, 
                let acc_double_x = two * acc_x.clone() * acc_y.clone() * (acc_y_sq.clone() - twenty_seven.clone() * acc_z_sq.clone());
                let acc_double_y = (acc_y_sq.clone() - twenty_seven.clone() * acc_z_sq.clone()) * (acc_y_sq.clone() 
                                    + nine.clone() * acc_z_sq.clone()) + seventy_two.clone() * acc_y_sq.clone() * acc_z_sq.clone();
                let acc_double_z = eight.clone() * acc_y_sq.clone() * acc_y.clone() * acc_z.clone();

                // X_1 = acc_double_x, Y_2 = y
                // X_3 &= (X_1(Y_2) + X_2Y_1)(Y_1(Y_2)) - 3bZ_1Z_2) \\
                //  - (Y_1Z_2 + Y_2Z_1)(3b(X_1Z_2 + X_2Z_1)), \\
                // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) \\
                //  + (Y_1(Y_2) + 3bZ_1Z_2)(Y_1(Y_2) - 3bZ_1Z_2), \\
                // Z_3 &= (Y_1Z_2 + Y_2Z_1)(Y_1(Y_2) + 3bZ_1Z_2) \\
                //  + (X_1(Y_2) + X_2Y_1)(3X_1X_2).

                // simplified for b = 3, 
                let acc_add_x = ( acc_double_x.clone() * y.clone() + x.clone() * acc_double_y.clone())
                    * ( y.clone() * acc_double_y.clone() - nine.clone() * acc_double_z.clone())
                    - ( acc_double_y.clone() + y.clone() * acc_double_z.clone())
                    * ( nine.clone() * (acc_double_x.clone()  + x.clone() * acc_double_z.clone()));
                
                let acc_add_y = ( three.clone() * acc_double_x.clone() * x.clone()) 
                    * ( nine.clone() * ( acc_double_x.clone() + x.clone() * acc_double_z.clone()))
                    + ( acc_double_y.clone() * y.clone() + nine.clone() * acc_double_z.clone()) 
                    * ( y.clone() * acc_double_y.clone() - nine.clone() * acc_double_z.clone());

                let acc_add_z = (acc_double_y.clone() + y.clone() * acc_double_z.clone())
                    * ( y.clone() * acc_double_y.clone() + nine.clone() * acc_double_z.clone())
                    + ( acc_double_x.clone() * y.clone() + x.clone() * acc_double_y.clone())
                    * ( three.clone() * acc_double_x.clone() * x.clone());
                
                let rhs_x = (one.clone() - r.clone()) * acc_double_x.clone() - r.clone() * acc_add_x.clone();
                let rhs_y = (one.clone() - r.clone()) * acc_double_y.clone() - r.clone() * acc_add_y.clone();
                let rhs_z = (one.clone() - r.clone()) * acc_double_z.clone() - r.clone() * acc_add_z.clone();

                vec![q_ec_double_add.clone() * (rhs_z.clone() * acc_next_x - rhs_x.clone() * acc_next_z.clone()),
                     q_ec_double_add.clone() * (rhs_z.clone() * acc_next_y - rhs_y.clone() * acc_next_z.clone())]
            
            });

        Self { 
            witness: [col_rbits, col_ptx, col_pty, col_acc_x, col_acc_y, col_acc_z], 
            selector: [q_first_row, q_ec_double_add],
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
            // self.selector[0].enable(&mut region, 0)?;

                for row in 0..rbits_vec_len {
                    region.assign_advice(|| "r_vec",self.witness[0], row, || inputs.rbits_vec[row])?;
                    region.assign_advice(|| "ptx_vec",self.witness[1], row, || inputs.ptx_vec[row])?;
                    region.assign_advice(|| "pty_vec",self.witness[2], row, || inputs.pty_vec[row])?;
                    region.assign_advice(|| "acc_x_vec",self.witness[3], row, || inputs.acc_x_vec[row])?;
                    region.assign_advice(|| "acc_y_vec",self.witness[4], row, || inputs.acc_y_vec[row])?;
                    region.assign_advice(|| "acc_z_vec",self.witness[5], row, || inputs.acc_z_vec[row])?;

                    if row != rbits_vec_len - 1 {
                        self.selector[1].enable(&mut region, row)?;
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
    pub acc_z_vec: Vec<Value<C::Scalar>>,
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
    use halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fq, Fr, G1Affine, G1}, grumpkin}, plonk::Assigned};
    use halo2_proofs::{arithmetic::Field, halo2curves::{ff::BatchInvert, group::{cofactor::CofactorCurveAffine, Curve, Group}, Coordinates, CurveAffine}};
    use crate::util::{arithmetic::{fe_from_bits_le, fe_to_fe}, izip_eq};
    use super::{ScalarMulChip, ScalarMulConfigInputs};
    use rand::{rngs::OsRng, Rng};
        
    #[test]
    fn ec_vec() {

        use plotters::prelude::*;
        let root = BitMapBackend::new("ECChip_deg6.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("ECChip_deg6", ("sans-serif", 60)).unwrap();

        let k = 8; 
        let mut rng = OsRng;
        let vec_len: usize = 129;

        let mut rbits = Vec::new();
        rbits.extend((0..vec_len).map(|_| rng.gen_bool(1.0 / 3.0)));

        let mut rbits_vec = rbits.iter().skip(1).map(|bit| 
            Value::known(if *bit {Fq::ONE} else {Fq::ZERO}))
            .rev()
            .collect_vec();
        rbits_vec.insert(0, Value::known(Fq::ZERO)); // push first element as 0/1 doesnt matter

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
        // 3.27 algo for double add, Guide to ECC
        let mut p = G1Affine::identity();
        while p == G1Affine::identity() {
            p = G1Affine::random(&mut rng);
        }
        println!("p: {:?}", p);

        let p_single = p; 
        let mut acc_prev = G1::identity();
        let mut ptx_vec = Vec::new();
        let mut pty_vec = Vec::new();
        let mut acc_x_vec = Vec::new();
        let mut acc_y_vec = Vec::new();
        let mut acc_z_vec = Vec::new();

        acc_x_vec.push(Value::known(acc_prev.x));
        acc_y_vec.push(Value::known(acc_prev.y)); 
        acc_z_vec.push(Value::known(acc_prev.z));
        let rbits_rev = rbits.iter().skip(1).rev().cloned().collect_vec();
        // let rbits_rev = rbits.iter().rev().cloned().collect_vec();

        for i in 0..vec_len - 1 {
            acc_prev = G1::double(&acc_prev);
            acc_prev = if rbits_rev[i] { acc_prev + p } else { acc_prev };
            acc_x_vec.push(Value::known(acc_prev.x));
            acc_y_vec.push(Value::known(acc_prev.y)); 
            acc_z_vec.push(Value::known(acc_prev.z));
        }

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

        // let zero = G1::identity(); 
        // println!("zero: {:?}", zero);
        // //println!("zero: {:?}", zero.to_affine().);
        // let p = G1::random(&mut rng); 
        // //let p_affine = p.to_affine();
        // let mut acc_prev = G1::identity();

        // let mut acc_prev_xvec = Vec::new();
        // let mut acc_prev_yvec = Vec::new();
        // let mut acc_prev_zvec = Vec::new();

        // let mut lhs_yvec =  Vec::new();
        // let mut lhs_double_xvec = Vec::new();
        // let mut lhs_double_yvec = Vec::new();
        // let mut lhs_double_zvec = Vec::new();
        // let mut rhs_yvec = Vec::new();

        // let mut pt_vec = Vec::new();
        // let rbits_rev = rbits.iter().rev().cloned().collect_vec();

        // for i in (0..vec_len) {
        //     acc_prev = G1::double(&acc_prev);
        //     let lhs = acc_prev;
        //     println!("rbit: {}", rbits_rev[i]);
        //     acc_prev = if rbits_rev[i] { acc_prev + p 
        //                     } else { 
        //                         acc_prev
        //                     };
    
        //     acc_prev_xvec.push(acc_prev.x);
        //     acc_prev_yvec.push(acc_prev.y);
        //     acc_prev_zvec.push(acc_prev.z);

        //     lhs_double_xvec.push(lhs.x);
        //     lhs_double_yvec.push(lhs.y);
        //     lhs_double_zvec.push(lhs.z);
        // }

        // let acc_prev_yv = acc_prev_yvec.clone();
        // let batch_invert_time = std::time::Instant::now();
        // lhs_double_yvec.batch_invert();
        // acc_prev_yvec.batch_invert();
        // println!("batch_invert_time1: {:?}", batch_invert_time.elapsed());

        // let acc_x_vec = acc_prev_yvec.iter().zip(acc_prev_xvec).map(|(lhs, rhs)| Value::known(lhs*rhs)).collect_vec();
        // let acc_z_vec = acc_prev_yvec.iter().zip(acc_prev_zvec).map(|(lhs, rhs)| Value::known(lhs*rhs)).collect_vec();
        
        // let acc_affine = acc_x_vec.iter().zip(acc_z_vec.iter()).map(|(x, y)| G1Affine::from_xy(x.assign().unwrap(), y.assign().unwrap()).unwrap()).collect_vec();
        // let lhs_double_affine = lhs_double_zvec.iter().zip(lhs_double_xvec.iter().zip(lhs_double_yvec)).map(|(zinv, (x, y))| G1Affine::from_xy(x*zinv, y*zinv).unwrap()).collect_vec();
        // let p_yinv = p.y.invert().unwrap();
        // let p_affine = G1Affine::from_xy(p.x*p_yinv, p.z*p_yinv).unwrap();

        // for i in 0..vec_len {
        //     let rhs_y = if rbits_rev[i] { 
        //                         // need to impl sub for g1
        //                         // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) \\
        //                         //  + (Y_1(-Y_2) + 3bZ_1Z_2)(Y_1(-Y_2) - 3bZ_1Z_2), \\
        //                         Fq::from(3)*acc_x_vec[i].assign().unwrap()*p.x*(Fq::from(9)*acc_x_vec[i].assign().unwrap()*p.z + acc_z_vec[i].assign().unwrap()*p.x)
        //                         + ((-p.y) + Fq::from(9)*acc_z_vec[i].assign().unwrap()*p.z)
        //                         * ((-p.y) - Fq::from(9)*acc_z_vec[i].assign().unwrap()*p.z)
        //                     } else { Fq::ONE
        //                 };
        //     lhs_yvec.push(lhs_double_yvec[i]);
        //     rhs_yvec.push(rhs_y);
        // }

        // let batch_invert_time = std::time::Instant::now();
        // lhs_yvec.batch_invert();
        // println!("batch_invert_time2: {:?}", batch_invert_time.elapsed());
        // let lambda_vec = lhs_yvec.iter().zip(rhs_yvec).map(|(lhs, rhs)| Value::known(lhs*rhs)).collect_vec();
        // println!("lambda_vec: {:?}", lambda_vec);

        // for i in (0..vec_len) {
        //     acc_prev = G1::double(&acc_prev);
        //     let lhs = acc_prev;
        //     println!("rbit: {}", rbits_rev[i]);
        //     acc_prev = if rbits_rev[i] { acc_prev + p 
        //                     } else { 
        //                         acc_prev
        //                     };
    
        //     acc_prev_xvec.push(acc_prev.x);
        //     acc_prev_yvec.push(acc_prev.y);
        //     acc_prev_zvec.push(acc_prev.z);

        //     lhs_double_xvec.push(lhs.x);
        //     lhs_double_yvec.push(lhs.y);
        //     lhs_double_zvec.push(lhs.z);
        // }

        // let batch_invert_time = std::time::Instant::now();
        // lhs_double_zvec.batch_invert();
        // acc_prev_zvec.batch_invert();
        // println!("batch_invert_time1: {:?}", batch_invert_time.elapsed());

        // let acc_x_vec = acc_prev_zvec.iter().zip(acc_prev_xvec).map(|(lhs, rhs)| Value::known(lhs*rhs)).collect_vec();
        // let acc_y_vec = acc_prev_zvec.iter().zip(acc_prev_yvec).map(|(lhs, rhs)| Value::known(lhs*rhs)).collect_vec();
        
        // let acc_affine = acc_x_vec.iter().zip(acc_y_vec.iter()).map(|(x, y)| G1Affine::from_xy(x.assign().unwrap(), y.assign().unwrap()).unwrap()).collect_vec();
        // // let lhs_double_affine = lhs_double_zvec.iter().zip(lhs_double_xvec.iter().zip(lhs_double_yvec)).map(|(zinv, (x, y))| G1Affine::from_xy(x*zinv, y*zinv).unwrap()).collect_vec();

        // for i in 0..vec_len{
        //     let rhs = if rbits_rev[i] { acc_affine[i] - p_affine 
        //                     } else { acc_affine[i].into()
        //                 };
        //     lhs_zvec.push(lhs_double_zvec[i]);
        //     rhs_zvec.push(rhs.z);
        // }

        // let batch_invert_time = std::time::Instant::now();
        // lhs_zvec.batch_invert();
        // println!("batch_invert_time2: {:?}", batch_invert_time.elapsed());
        // let lambda_vec = lhs_zvec.iter().zip(rhs_zvec).map(|(lhs, rhs)| Value::known(lhs*rhs)).collect_vec();
        // println!("lambda_vec: {:?}", lambda_vec);

        // let rbits_native = rbits.iter().map(|bit| 
        //     if *bit {Fr::ONE} else {Fr::ZERO})
        //     .collect_vec();

        let rbits_native = rbits.iter().skip(1).map(|bit| 
            if *bit {Fr::ONE} else {Fr::ZERO})
            .collect_vec();

        let r = fe_from_bits_le(rbits_native);
        // let r_non_native: Fq = fe_to_fe(r);
        // rbits_vec.push(Value::known(r_non_native)); // push last element as r
        let scalar_mul_given = p * r;
        let scalar_mul_calc = (acc_x_vec.last().map(|val| val.assign().unwrap()).unwrap(), acc_y_vec.last().map(|val| val.assign().unwrap()).unwrap(), acc_z_vec.last().map(|val| val.assign().unwrap()).unwrap());
        assert_eq!(scalar_mul_given.x * scalar_mul_calc.2, scalar_mul_calc.0 * scalar_mul_given.z);
        assert_eq!(scalar_mul_given.y * scalar_mul_calc.2, scalar_mul_calc.1 * scalar_mul_given.z);

        let inputs =
            ScalarMulConfigInputs::<grumpkin::G1Affine> { 
                rbits_vec, 
                ptx_vec, 
                pty_vec,
                acc_x_vec, 
                acc_y_vec, 
                acc_z_vec, 
            };   

        let circuit = ScalarMulChip::<grumpkin::G1Affine> { inputs: vec![inputs] };
        MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();

        halo2_base::halo2_proofs::dev::CircuitLayout::default()
        .render(k, &circuit, &root)
        .unwrap();
    }
}



    // pub fn sm_config_inputs_proj_deg11(
    //     &self,
    //     sm_inputs: &Vec<ScalarMulChipInputs<C::Scalar, C::Secondary>>
    // ) -> Result<Vec<ScalarMulConfigInputs<C>>, Error> {

    //     let vec_len: usize = 128;
    //     let mut sm_config_inputs = Vec::new();
    //     for inputs in sm_inputs{

    //         let r = inputs.r;
    //         let rbits_fe = &inputs.r_le_bits;
    //         let rbits_rev_fe = rbits_fe.iter().rev().cloned().collect_vec();
    //         let rbits_rev = rbits_rev_fe.iter().map( |fe|
    //             { if *fe == C::Scalar::ONE {true} else {false} })
    //             .collect_vec();

    //         let mut rbits_vec = rbits_rev_fe.iter().map(|fe| Value::known(*fe)).collect_vec();
    //         // rbits_vec.insert(0, Value::known(C::Scalar::ZERO));

    //         let p = inputs.nark_comm; 
    //         let p_coord = into_coordinate_proj(&p);
    //         let p_single_x = into_coordinates(&p)[0];
    //         let p_single_y = into_coordinates(&p)[1];

    //         // 3.27 algo for double add, Guide to ECC
    //         let mut acc_prev = ProjectivePoint::identity();
    //         let mut ptx_vec = Vec::new();
    //         let mut pty_vec = Vec::new();
    //         let mut acc_x_vec = Vec::new();
    //         let mut acc_y_vec = Vec::new();
    //         let mut acc_z_vec = Vec::new();

    //         acc_x_vec.push(Value::known(acc_prev.x));
    //         acc_y_vec.push(Value::known(acc_prev.y)); 
    //         acc_z_vec.push(Value::known(acc_prev.z));
    //         // let rbits_rev = rbits.iter().skip(1).rev().cloned().collect_vec();

    //         for i in 0..vec_len - 1 {
    //             acc_prev = double_proj(acc_prev);
    //             acc_prev = if rbits_rev[i] { add_proj(p_coord, acc_prev) } else { acc_prev };
    //             acc_x_vec.push(Value::known(acc_prev.x));
    //             acc_y_vec.push(Value::known(acc_prev.y)); 
    //             acc_z_vec.push(Value::known(acc_prev.z));
    //         }

    //         for i in 0..vec_len {
    //             ptx_vec.push(Value::known(p_single_x));
    //             pty_vec.push(Value::known(p_single_y));
    //         }
            
    //         // let r_native = fe_from_bits_le(rbits_fe.clone());
    //         // let r_non_native: C::Base = fe_to_fe(r_native);
    //         // let scalar_mul_given = p * r_non_native;
    //         // let scalar_mul_calc = (acc_x_vec.last().map(|val| val.assign().unwrap()).unwrap(), acc_y_vec.last().map(|val| val.assign().unwrap()).unwrap(), acc_z_vec.last().map(|val| val.assign().unwrap()).unwrap());
    //         // assert_eq!(scalar_mul_given.x * scalar_mul_calc.2, scalar_mul_calc.0 * scalar_mul_given.z);
    //         // assert_eq!(scalar_mul_given.y * scalar_mul_calc.2, scalar_mul_calc.1 * scalar_mul_given.z);
    
    //         let inputs =
    //             ScalarMulConfigInputs::<C> { 
    //                 rbits_vec, 
    //                 ptx_vec, 
    //                 pty_vec,
    //                 acc_x_vec, 
    //                 acc_y_vec, 
    //                 acc_z_vec, 
    //             }; 

    //         sm_config_inputs.push(inputs);
    //     }

    //     Ok(sm_config_inputs)
    // }