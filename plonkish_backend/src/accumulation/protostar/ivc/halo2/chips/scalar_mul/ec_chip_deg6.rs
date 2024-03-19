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

use crate::{accumulation::protostar::ivc::cyclefold::CycleFoldInputs, util::arithmetic::{TwoChainCurve, PrimeFieldBits, Field}};

pub const NUM_ADVICE: usize = 5;
pub const NUM_FIXED: usize = 1;
pub const NUM_SELECTOR: usize = 2;

#[derive(Clone, Debug)]
pub struct ScalarMulChipConfig<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    witness: [Column<Advice>; NUM_ADVICE],
    selector: [Selector; NUM_SELECTOR],
    _marker: PhantomData<C>,
}

impl<C> ScalarMulChipConfig<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub fn configure(meta: &mut ConstraintSystem<C::Scalar>, advices: [Column<Advice>; NUM_ADVICE]) -> Self {

        // | row | r_bits_0  |   point   |   acc.x   |   acc.y   |  lambda   | 
        // | 0   |    0      |     x     |    y      |    y      |    1      | 
        // | 1   |    1      |     y     |    2y     |    2y     |    0      |
        // | 2   |    1      |     x     |    4y     |    4y     |    1      | 
        // | 3   |    1      |     y     |    16y    |    16y    |    0      |

        let [col_rbits, col_pt, col_acc_x, col_acc_y, col_lambda] = 
            advices;
    
        let [q_ec_double_add_odd, q_ec_double_add_even] = [(); NUM_SELECTOR].map(|_| meta.selector());;
        
            meta.create_gate("q_ec_double_add_odd", |meta| {

                let q_ec_double_add_odd = meta.query_selector(q_ec_double_add_odd);
                let r = meta.query_advice(col_rbits, Rotation(1));
                let x = meta.query_advice(col_pt, Rotation(1));
                let y = meta.query_advice(col_pt, Rotation(0));
                let acc_x = meta.query_advice(col_acc_x, Rotation(0));
                let acc_y = meta.query_advice(col_acc_y, Rotation(0));
                // let acc_z = Expression::Constant(C::Scalar::ONE);

                let acc_next_x = meta.query_advice(col_acc_x, Rotation(1));
                let acc_next_y = meta.query_advice(col_acc_y, Rotation(1));
                // let acc_next_z = Expression::Constant(C::Scalar::ONE);
                let lambda = meta.query_advice(col_lambda, Rotation(1));

                let zero = Expression::Constant(C::Scalar::ZERO);
                let one = Expression::Constant(C::Scalar::ONE);
                let two = Expression::Constant(C::Scalar::from(2));
                let three = Expression::Constant(C::Scalar::from(3));

                let b = three.clone(); // todo change for other curve
                let nine = Expression::Constant(C::Scalar::from(9));
                let eight = Expression::Constant(C::Scalar::from(8));
                let twenty_four = Expression::Constant(C::Scalar::from(24));
                let twenty_seven = Expression::Constant(C::Scalar::from(27)); // nine * b
                let sixty_three = Expression::Constant(C::Scalar::from(72)); // twenty_four * b
                let acc_x_sq = acc_x.clone() * acc_x.clone();
                let acc_y_sq = acc_y.clone() * acc_y.clone();
                //let acc_z_sq = one.clone();

                
                // pt double, b = 3 for bn254
                //  x' = 2xy(y^2 - 9bz^2) --> x'*l^2 = 2xy(y^2*l^2 - 9b)
                //  y' = (y^2 - 9bz^2)(y^2 + 3bz^2) + 24*b*y^2*z^2 --> y'*l^3 = (y^2*l^2 - 9b)(y^2*l^2 + 3b) + 24*b*y^2*z^2
                //  z' = 8y^3*z

                // let acc_double_x = two * acc_x.clone() * acc_y.clone() * (acc_y_sq.clone() - nine.clone() * b.clone() * acc_z_sq.clone());
                // let acc_double_y = (acc_y_sq.clone() - nine.clone() * b.clone() * acc_z_sq.clone()) * (acc_y_sq.clone() 
                //                     + three.clone() * b.clone() * acc_z_sq.clone()) + twenty_four.clone() * b.clone() * acc_y_sq.clone() * acc_z_sq.clone();
                // let acc_double_z = eight.clone() * acc_y_sq.clone() * acc_y.clone() * acc_z.clone();

                // simplified for b = 3, 
                let acc_double_x = two * acc_x.clone() * acc_y.clone() * (acc_y_sq.clone() - twenty_seven.clone());
                let acc_double_y = (acc_y_sq.clone() - twenty_seven.clone()) * (acc_y_sq.clone() 
                                    + nine.clone()) + sixty_three.clone() * acc_y_sq.clone();
                let acc_double_z = eight.clone() * acc_y_sq.clone() * acc_y.clone();

                // choice poly in projective coordinates, identity is (0,1,0)
                let sel_x = r.clone() * x.clone(); 
                let sel_y = (one.clone() - r.clone()) + r.clone() * y.clone(); 
                let sel_z = r.clone(); 
 

                // X_3 &= (X_1(-Y_2) + X_2Y_1)(Y_1(-Y_2)) - 3bZ_1Z_2 \\
                //  - (Y_1Z_2 - Y_2Z_1)(3b(X_1Z_2 + X_2Z_1)), \\
                // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) \\
                //  + (Y_1(-Y_2) + 3bZ_1Z_2)(Y_1(-Y_2) - 3bZ_1Z_2), \\
                // Z_3 &= (Y_1Z_2 - Y_2Z_1)(Y_1(-Y_2) + 3bZ_1Z_2) \\
                //  + (X_1(-Y_2) + X_2Y_1)(3X_1X_2).

            // simplified for b = 3, 
            let acc_sub_x = ( - sel_x.clone() * acc_next_y.clone() + acc_next_x.clone() * sel_y.clone())
                * ( - sel_y.clone() * acc_next_y.clone()) - nine.clone() * sel_z.clone()
                - ( sel_y.clone()  - acc_next_y.clone() * sel_z.clone())
                * (nine.clone() * (sel_x.clone()  + acc_next_x.clone() * sel_z.clone()));
            
            let acc_sub_y = (three.clone() * sel_x.clone() * acc_next_x.clone()) 
                * (nine.clone() * (sel_x.clone()  + acc_next_x.clone() * sel_z.clone()))
                + ( - sel_y.clone() * acc_next_y.clone() + nine.clone() * sel_z.clone() ) 
                * ( - sel_y.clone() * acc_next_y.clone() - nine.clone() * sel_z.clone() );

            let acc_sub_z = (sel_y.clone()  - acc_next_y.clone() * sel_z.clone())
                * ( - sel_y.clone() * acc_next_y.clone() + nine.clone() * sel_z.clone() )
                + ( - sel_x.clone() * acc_next_y.clone() + acc_next_x.clone() * sel_y.clone())
                * (three.clone() * sel_x.clone() * acc_next_x.clone());

                vec![q_ec_double_add_odd.clone() * (acc_sub_x - acc_double_x.clone() * lambda.clone()),
                     q_ec_double_add_odd.clone() * (acc_sub_y - acc_double_y.clone() * lambda.clone()),
                     q_ec_double_add_odd * (acc_sub_z - acc_double_z.clone() * lambda.clone())]
            
            });

            meta.create_gate("q_ec_double_add_even", |meta| {

                let q_ec_double_add_even = meta.query_selector(q_ec_double_add_even);
                let r = meta.query_advice(col_rbits, Rotation(1));
                let x = meta.query_advice(col_pt, Rotation(0));
                let y = meta.query_advice(col_pt, Rotation(1));
                let acc_x = meta.query_advice(col_acc_x, Rotation(0));
                let acc_y = meta.query_advice(col_acc_y, Rotation(0));
                // let acc_z = Expression::Constant(C::Scalar::ONE);

                let acc_next_x = meta.query_advice(col_acc_x, Rotation(1));
                let acc_next_y = meta.query_advice(col_acc_y, Rotation(1));
                // let acc_next_z = Expression::Constant(C::Scalar::ONE);
                let lambda = meta.query_advice(col_lambda, Rotation(0));

                let zero = Expression::Constant(C::Scalar::ZERO);
                let one = Expression::Constant(C::Scalar::ONE);
                let two = Expression::Constant(C::Scalar::from(2));
                let three = Expression::Constant(C::Scalar::from(3));

                let b = three.clone(); // todo change for other curve
                let nine = Expression::Constant(C::Scalar::from(9));
                let eight = Expression::Constant(C::Scalar::from(8));
                let twenty_four = Expression::Constant(C::Scalar::from(24));
                let twenty_seven = Expression::Constant(C::Scalar::from(27)); // nine * b
                let sixty_three = Expression::Constant(C::Scalar::from(72)); // twenty_four * b
                let acc_x_sq = acc_x.clone() * acc_x.clone();
                let acc_y_sq = acc_y.clone() * acc_y.clone();
                //let acc_z_sq = one.clone();

                
                // pt double, b = 3 for bn254
                //  x' = 2xy(y^2 - 9bz^2) --> x'*l^2 = 2xy(y^2*l^2 - 9b)
                //  y' = (y^2 - 9bz^2)(y^2 + 3bz^2) + 24*b*y^2*z^2 --> y'*l^3 = (y^2*l^2 - 9b)(y^2*l^2 + 3b) + 24*b*y^2*z^2
                //  z' = 8y^3*z

                // let acc_double_x = two * acc_x.clone() * acc_y.clone() * (acc_y_sq.clone() - nine.clone() * b.clone() * acc_z_sq.clone());
                // let acc_double_y = (acc_y_sq.clone() - nine.clone() * b.clone() * acc_z_sq.clone()) * (acc_y_sq.clone() 
                //                     + three.clone() * b.clone() * acc_z_sq.clone()) + twenty_four.clone() * b.clone() * acc_y_sq.clone() * acc_z_sq.clone();
                // let acc_double_z = eight.clone() * acc_y_sq.clone() * acc_y.clone() * acc_z.clone();

                // simplified for b = 3, 
                let acc_double_x = two * acc_x.clone() * acc_y.clone() * (acc_y_sq.clone() - twenty_seven.clone());
                let acc_double_y = (acc_y_sq.clone() - twenty_seven.clone()) * (acc_y_sq.clone() 
                                    + nine.clone()) + sixty_three.clone() * acc_y_sq.clone();
                let acc_double_z = eight.clone() * acc_y_sq.clone() * acc_y.clone();

                // choice poly in projective coordinates, identity is (0,1,0)
                let sel_x = r.clone() * x.clone(); 
                let sel_y = (one.clone() - r.clone()) + r.clone() * y.clone(); 
                let sel_z = r.clone(); 
 

                // X_3 &= (X_1(-Y_2) + X_2Y_1)(Y_1(-Y_2)) - 3bZ_1Z_2 \\
                //  - (Y_1Z_2 - Y_2Z_1)(3b(X_1Z_2 + X_2Z_1)), \\
                // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) \\
                //  + (Y_1(-Y_2) + 3bZ_1Z_2)(Y_1(-Y_2) - 3bZ_1Z_2), \\
                // Z_3 &= (Y_1Z_2 - Y_2Z_1)(Y_1(-Y_2) + 3bZ_1Z_2) \\
                //  + (X_1(-Y_2) + X_2Y_1)(3X_1X_2).

            // simplified for b = 3, 
            let acc_sub_x = ( - sel_x.clone() * acc_next_y.clone() + acc_next_x.clone() * sel_y.clone())
                * ( - sel_y.clone() * acc_next_y.clone()) - nine.clone() * sel_z.clone()
                - ( sel_y.clone()  - acc_next_y.clone() * sel_z.clone())
                * (nine.clone() * (sel_x.clone()  + acc_next_x.clone() * sel_z.clone()));
            
            let acc_sub_y = (three.clone() * sel_x.clone() * acc_next_x.clone()) 
                * (nine.clone() * (sel_x.clone()  + acc_next_x.clone() * sel_z.clone()))
                + ( - sel_y.clone() * acc_next_y.clone() + nine.clone() * sel_z.clone() ) 
                * ( - sel_y.clone() * acc_next_y.clone() - nine.clone() * sel_z.clone() );

            let acc_sub_z = (sel_y.clone()  - acc_next_y.clone() * sel_z.clone())
                * ( - sel_y.clone() * acc_next_y.clone() + nine.clone() * sel_z.clone() )
                + ( - sel_x.clone() * acc_next_y.clone() + acc_next_x.clone() * sel_y.clone())
                * (three.clone() * sel_x.clone() * acc_next_x.clone());

                vec![q_ec_double_add_even.clone() * (acc_sub_x - acc_double_x.clone() * lambda.clone()),
                     q_ec_double_add_even.clone() * (acc_sub_y - acc_double_y.clone() * lambda.clone()),
                     q_ec_double_add_even * (acc_sub_z - acc_double_z.clone() * lambda.clone())]
            
            });


        Self { 
            witness: [col_rbits, col_pt, col_acc_x, col_acc_y, col_lambda], 
            selector: [q_ec_double_add_odd, q_ec_double_add_even],
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
        // | 1   |    0      |     x     |    y      |    y      |    1      | 
        // | 2   |    1      |     y     |    2y     |    2y     |    0      |
        // | 3   |    1      |     x     |    4y     |    4y     |    1      | 
        // | 4   |    1      |     y     |    16y    |    16y    |    0      |

            let rbits_vec_len = inputs.rbits_vec.len();

                for row in 0..rbits_vec_len {
                    region.assign_advice(|| "r_vec",self.witness[0], row, || inputs.rbits_vec[row])?;
                    region.assign_advice(|| "pt_vec",self.witness[1], row, || inputs.pt_vec[row])?;
                    region.assign_advice(|| "acc_x_vec",self.witness[2], row, || inputs.acc_x_vec[row])?;
                    region.assign_advice(|| "acc_y_vec",self.witness[3], row, || inputs.acc_y_vec[row])?;
                    region.assign_advice(|| "lambda_vec",self.witness[4], row, || inputs.lambda_vec[row])?;

                    // if row % 2 != 0 {
                    //     self.selector[0].enable(&mut region, row)?;
                    // } else {
                    //     self.selector[1].enable(&mut region, row)?;
                    // }
                }

                self.selector[1].enable(&mut region, 0)?;

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
    pub pt_vec: Vec<Value<C::Scalar>>,
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
        let advices = [0; NUM_ADVICE].map(|_| meta.advice_column());
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
    use std::marker::PhantomData;

    use bitvec::vec;
    use halo2_base::halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fr, Fq, G1Affine, G1}, grumpkin}};
    use halo2_proofs::{halo2curves::{Coordinates, group::{Group, Curve, cofactor::CofactorCurveAffine}, CurveAffine}, arithmetic::Field};
    use itertools::Itertools;
    use crate::util::arithmetic::{fe_to_fe, fe_from_bits_le};
    use super::{ScalarMulChip, ScalarMulConfigInputs};
    use rand::{rngs::OsRng, Rng};
    use subtle::ConstantTimeEq;


        
    #[test]
    fn ec_vec() {

        use plotters::prelude::*;
        let root = BitMapBackend::new("ECChip_deg6.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("ECChip_deg6", ("sans-serif", 60)).unwrap();

        let k = 7; 
        let mut rng = OsRng;
        // let vec_len: usize = 1 << k;
        let vec_len: usize = 4;
        let mut pt_vec = Vec::new();
        let mut acc_x_vec = Vec::new();
        let mut acc_y_vec = Vec::new();
        let mut lambda_vec = Vec::new();

        // first bit is assumed to be 1 for now, will remove this at the end of calculation later, 
        // since this cost 1 additional row which tips this over the next power of 2
        let mut rbits = Vec::new();
        // rbits.extend((0..vec_len).map(|_| false));
        rbits.extend( [true, false, true, false]);
        // rbits.extend((0..vec_len).map(|_| rng.gen_bool(1.0 / 3.0)));

        let rbits_vec = rbits.iter().map(|bit| 
            Value::known(if *bit {Fq::ONE} else {Fq::ZERO}))
            .collect_vec();

        // 3.26 algo for double add, Guide to ECC
        // let mut p = G1::random(&mut rng).to_affine(); 
        // let p_single_affine = p;//.to_affine();
        // let mut acc_prev = G1::identity().to_affine();
        // for i in 0..vec_len {
        //     acc_prev = if rbits[i] { (acc_prev + p).to_affine() } else { acc_prev };
        //     p = G1::double(&p.into()).to_affine(); 
        //     acc_x_vec.push(Value::known(acc_prev.x));
        //     acc_y_vec.push(Value::known(acc_prev.y)); 
        // }

        // for i in 0..vec_len {
        //     if i % 2 == 0 {
        //         pt_vec.push(Value::known(p_single_affine.x));
        //         pt_vec.push(Value::known(p_single_affine.y));
        //     }
        // }


        // | row |  r_bits   |   point   |   acc.x   |   acc.y   |  lambda   | 
        // | 1   |    0      |     x     |    y      |    y      |    1      | 
        // | 2   |    1      |     y     |    2y     |    2y     |    0      |
        // | 3   |    1      |     x     |    4y     |    4y     |    1      | 
        // | 4   |    1      |     y     |    16y    |    16y    |    0      |

        // acc_x_vec.push(Value::known(p_single_affine.x));
        // acc_y_vec.push(Value::known(p_single_affine.y)); 

        // 3.26 algo for double add, Guide to ECC
        let mut p = G1Affine::random(&mut rng); 
        let p_single = p; 
        let mut acc_prev = G1Affine::identity();
        let mut acc_next = G1Affine::identity();
        let mut p_double = G1::identity();
        let mut lhs = G1::identity();

        for i in 0..vec_len {
            let acc_prev_single = acc_prev;
            acc_prev = if rbits[i] { (acc_prev + p).to_affine() } else { acc_prev };

            acc_x_vec.push(Value::known(acc_prev.x));
            acc_y_vec.push(Value::known(acc_prev.y)); 

            let rhs = acc_prev - acc_prev_single;
            let lhs = if rbits[i] { p_double } else { G1::identity()};

            let ct_equal = rhs.ct_eq(&lhs);
            println!("ct_equal: {:?}", ct_equal);
            
            // let lambda = if i != 0 { 
            //     let ct_equal = rhs.ct_eq(&lhs);
            //     println!("ct_equal: {:?}", ct_equal);
            //     Fq::ONE 
            //     // lhs.z * rhs.z.invert().unwrap() 
            // } else {
            //     Fq::ONE 
            // };

            p_double = G1::double(&p.into());
            p = p_double.to_affine();

        }

        for i in 0..vec_len {
            if i % 2 == 0 {
                pt_vec.push(Value::known(p_single.x));
                pt_vec.push(Value::known(p_single.y));
            }
        }

        // let zero = G1::identity();
        // let zero_affine = zero.to_affine();

        // let mut p = G1::random(&mut rng).to_affine(); 
        // let p_single = p;
        // let p_single_affine = p.to_affine();
        // // let mut lambda = p_single.z.invert().unwrap();
        // let mut acc_prev = zero.to_affine();

        // for i in 0..vec_len {
            // println!("i: {:?}", i);
            // println!("rbits[i]: {:?}", rbits[i]);
            // println!("acc_prev: {:?}", acc_prev);
            // let doubling = G1::double(&p_single); 
            // let doubling_affine = doubling.to_affine();
            // let acc_sel = if rbits[i] { p_single } else { zero };
            // let acc_sel_affine = acc_sel.to_affine();

            // acc_prev = if rbits[i] { (acc_prev + p).to_affine() } else { acc_prev };
            // p = G1::double(&p.into()).to_affine(); 

            // let acc_next_affine: G1Affine = (doubling_affine + acc_sel_affine).into();
            // let rhs = if rbits[i] {acc_next - acc_sel
            // } else { acc_next };
            // let rhs_z = rhs.z;

            // println!("doubling: {:?}", doubling);
            // println!("acc_sel: {:?}", acc_sel);
            // println!("acc_next: {:?}", acc_next);

            // let lhs_z = doubling.z.invert().unwrap();
            // lambda = rhs_z * lhs_z;
            // let lambda_fe: Fr = fe_to_fe(lambda);
            // println!("lambda: {:?}", lambda);
            // let acc_next_scaled = (acc_next * lambda_fe);
            // let acc_next_affine = acc_next_scaled.to_affine();
            
            // let acc_next_affine = acc_next.to_affine();
            // println!("acc_next_affine: {:?}", acc_next_affine);

            // acc_x_vec.push(Value::known(acc_prev.x));
            // acc_y_vec.push(Value::known(acc_prev.y)); 

            // acc_x_vec.push(Value::known(acc_next_affine.x));
            // acc_y_vec.push(Value::known(acc_next_affine.y)); 
            // lambda_vec.push(Value::known(lambda));

            // let acc_double_x = Fq::from(2) * acc_x.clone() * acc_y.clone() * (acc_y_sq.clone() - twenty_seven.clone());
            // let acc_double_y = (acc_y_sq.clone() - twenty_seven.clone()) * (acc_y_sq.clone() 
            //                     + nine.clone()) + sixty_three.clone() * acc_y_sq.clone();
            // let acc_double_z = eight.clone() * acc_y_sq.clone() * acc_y.clone();

            // choice poly in projective coordinates, identity is (0,1,0)
            // let sel_x = r.clone() * x.clone(); 
            // let sel_y = (one.clone() - r.clone()) + r.clone() * y.clone(); 
            // let sel_z = r.clone(); 

            // acc_prev = acc_next;
            // acc_prev = acc_next_affine;

        //}

        let rbits_native = rbits.iter().map(|bit| 
            if *bit {Fr::ONE} else {Fr::ZERO})
            .collect_vec();
        //println!("rbits_native: {:?}", rbits_native);

        let r = fe_from_bits_le(rbits_native);
        // let r_non_native: Fq = fe_to_fe(r);
        // rbits_vec.push(Value::known(r_non_native)); // push last element as r
        let scalar_mul_given = (p_single * r).to_affine();
        let scalar_mul_calc = G1Affine::from_xy(acc_x_vec.last().map(|val| val.assign().unwrap()).unwrap(), acc_y_vec.last().map(|val| val.assign().unwrap()).unwrap()).unwrap();
        assert_eq!(scalar_mul_given, scalar_mul_calc);

        let inputs =
            ScalarMulConfigInputs::<grumpkin::G1Affine> { 
                rbits_vec, 
                pt_vec, 
                acc_x_vec, 
                acc_y_vec, 
                lambda_vec, 
            };   

        let circuit = ScalarMulChip::<grumpkin::G1Affine> { inputs: vec![inputs] };
        // MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();

        halo2_base::halo2_proofs::dev::CircuitLayout::default()
        .render(k, &circuit, &root)
        .unwrap();
    }

}
