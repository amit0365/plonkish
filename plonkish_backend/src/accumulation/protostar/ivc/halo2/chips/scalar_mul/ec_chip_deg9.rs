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
use halo2_proofs::halo2curves::{group::Group, grumpkin::Fr, Coordinates, CurveAffine};
use itertools::Itertools;
use std::{
    iter,
    marker::PhantomData,
    sync::{RwLock, RwLockReadGuard},
};

use crate::util::arithmetic::{TwoChainCurve, PrimeFieldBits, Field};

pub const NUM_ADVICE: usize = 5;
pub const NUM_FIXED: usize = 1;
pub const NUM_SELECTOR: usize = 4;

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
        // | 1   |    0      |     x     |    y      |    y      |    1      | 
        // | 2   |    1      |     y     |    2y     |    2y     |    0      |
        // | 3   |    1      |    2x     |    4y     |    4y     |    1      | 
        // | 4   |    0      |    2y     |    16y    |    16y    |    0      |

        let [col_rbits, col_pt, col_acc_x, col_acc_y, col_lambda] = 
            advices;
    
        let [q_ec_double_add0, q_ec_double_add1, q_ec_double_add2, q_ec_double_add3] = [(); NUM_SELECTOR].map(|_| meta.selector());;
        
            meta.create_gate("q_ec_double_add0", |meta| {

                let q_ec_double_add0 = meta.query_selector(q_ec_double_add0);
                let r = meta.query_advice(col_rbits, Rotation(0));
                let x = meta.query_advice(col_pt, Rotation(0));
                let y = meta.query_advice(col_pt, Rotation(1));
                let x2 = meta.query_advice(col_pt, Rotation(2));
                let y2 = meta.query_advice(col_pt, Rotation(3));
                // let z2 = Expression::Constant(C::Scalar::ONE);
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
                // let acc_z_sq = one.clone();

                
                // pt double, b = 3 for bn254
                //  x' = 2xy(y^2 - 9bz^2)
                //  y' = (y^2 - 9bz^2)(y^2 + 3bz^2) + 24*b*y^2*z^2 
                //  z' = 8y^3*z

                let acc_double_x = two.clone() * acc_x.clone() * acc_y.clone() * (acc_y_sq.clone() - twenty_seven.clone());
                let acc_double_y = (acc_y_sq.clone() - twenty_seven.clone()) * (acc_y_sq.clone() 
                                    + nine.clone()) + sixty_three.clone() * acc_y_sq.clone();
                let acc_double_z = eight.clone() * acc_y_sq.clone() * acc_y.clone();


                // X_3 &= (X_1Y_2 + X_2Y_1)(Y_1Y_2) - 3bZ_1Z_2 - (Y_1Z_2 + Y_2Z_1)(3b(X_1Z_2 + X_2Z_1)), \\
                // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) + (Y_1Y_2 + 3bZ_1Z_2)(Y_1Y_2 - 3bZ_1Z_2), \\
                // Z_3 &= (Y_1Z_2 + Y_2Z_1)(Y_1Y_2 + 3bZ_1Z_2) + (X_1Y_2 + X_2Y_1)(3X_1X_2).

                let acc_triple_x = (acc_x.clone() * acc_double_y.clone() + acc_double_x.clone() * acc_y.clone())
                    * acc_y.clone() * acc_double_y.clone() - nine.clone() * acc_double_z.clone()
                    - (acc_y.clone() * acc_double_z.clone() + acc_double_y.clone())
                    * (nine.clone() * (acc_x.clone() * acc_double_z.clone() + acc_double_x.clone()));

                let acc_triple_y = (three.clone() * acc_x.clone() * acc_double_x.clone()) 
                    * (nine.clone() * (acc_x.clone() * acc_double_z.clone() + acc_double_x.clone()))
                    + (acc_y.clone() * acc_double_y.clone() + nine.clone() * acc_double_z.clone()) 
                    * (acc_y.clone() * acc_double_y.clone() - nine.clone() * acc_double_z.clone());

                let acc_triple_z = (acc_y.clone() * acc_double_z.clone() + acc_double_y.clone())
                    * (acc_y.clone() * acc_double_y.clone() + nine.clone() * acc_double_z.clone())
                    + (acc_x.clone() * acc_double_y.clone() + acc_double_x.clone() * acc_y.clone())
                    * (three.clone() * acc_x.clone() * acc_double_x.clone());

                // choice poly in projective coordinates, identity is (0,1,0)
                // fix the factor of two coming from the last term
                // check if z2 is one
                let sel_x = (two.clone() - r.clone()) * r.clone() * x.clone() + (r.clone() - one.clone()) * r.clone() * x2.clone(); 
                let sel_y = (two.clone() - r.clone()) * (one.clone() - r.clone()) + (two.clone() - r.clone()) * r.clone() * y.clone() 
                            + (r.clone() - one.clone()) * r.clone() * y2.clone(); 
                // let sel_z = (two.clone() - r.clone()) * r.clone() + (r.clone() - one.clone()) * r.clone(); 
                let sel_z = r.clone(); 


                // X_3 &= (X_1(-Y_2) + X_2Y_1)(Y_1(-Y_2)) - 3bZ_1Z_2 - (Y_1Z_2 - Y_2Z_1)(3b(X_1Z_2 + X_2Z_1)), \\
                // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) + (Y_1(-Y_2) + 3bZ_1Z_2)(Y_1(-Y_2) - 3bZ_1Z_2), \\
                // Z_3 &= (Y_1Z_2 - Y_2Z_1)(Y_1(-Y_2) + 3bZ_1Z_2) + (X_1(-Y_2) + X_2Y_1)(3X_1X_2).

            // simplified for b = 3, 
            let acc_sub_x = ( - sel_x.clone() * acc_next_y.clone() + acc_next_x.clone() * sel_y.clone())
                * ( - sel_y.clone() * acc_next_y.clone()) - nine.clone() * sel_z.clone()
                - ( sel_y.clone()  - acc_next_y.clone() * sel_z.clone())
                * (nine.clone() * (sel_x.clone()  + acc_next_x.clone() * sel_z.clone()));
            
            let acc_sub_y = (three.clone() * sel_x.clone() * acc_next_x.clone()) 
                * (nine.clone() * (sel_x.clone()  + acc_next_x.clone() * sel_z.clone()))
                + ( - sel_y.clone() * acc_next_y.clone() + nine.clone() * sel_z.clone()) 
                * ( - sel_y.clone() * acc_next_y.clone() - nine.clone() * sel_z.clone());

            let acc_sub_z = (sel_y.clone()  - acc_next_y.clone() * sel_z.clone())
                * ( - sel_y.clone() * acc_next_y.clone() + nine.clone() * sel_z.clone() )
                + ( - sel_x.clone() * acc_next_y.clone() + acc_next_x.clone() * sel_y.clone())
                * (three.clone() * sel_x.clone() * acc_next_x.clone());

                vec![q_ec_double_add0.clone() * (lambda.clone() * acc_sub_x - acc_triple_x.clone()),
                     q_ec_double_add0.clone() * (lambda.clone() * acc_sub_y - acc_triple_y.clone()),
                     q_ec_double_add0 * (lambda.clone() * acc_sub_z - acc_triple_z.clone())]

            });


        Self { 
            witness: [col_rbits, col_pt, col_acc_x, col_acc_y, col_lambda], 
            selector: [q_ec_double_add0, q_ec_double_add1, q_ec_double_add2, q_ec_double_add3],
            _marker: PhantomData 
        }
    }

    // pub fn assign(
    //     &self,
    //     mut layouter: impl Layouter<C::Scalar>,
    //     inputs: ScalarMulConfigInputs<C>,
    // ) -> Result<[AssignedCell<C::Scalar, C::Scalar>; 5], Error> {

    //     layouter.assign_region(
    //         || "ScalarMulChipConfig assign",
    //         |mut region| {

    //     // | row |  r_bits   |   point   |   acc.x   |   acc.y   |  lambda   | 
    //     // | 1   |    0      |     x     |    y      |    y      |    1      | 
    //     // | 2   |    1      |     y     |    2y     |    2y     |    0      |
    //     // | 3   |    1      |     x     |    4y     |    4y     |    1      | 
    //     // | 4   |    1      |     y     |    16y    |    16y    |    0      |

    //         let rbits_vec_len = inputs.rbits_vec.len();

    //             for row in 0..rbits_vec_len {
    //                 self.selector[0].enable(&mut region, row)?;
    //                 region.assign_advice(|| "r_vec",self.witness[0], row, || inputs.rbits_vec[row])?;
    //                 region.assign_advice(|| "pt_vec",self.witness[1], row, || inputs.pt_vec[row])?;
    //                 region.assign_advice(|| "acc_x_vec",self.witness[2], row, || inputs.acc_x_vec[row])?;
    //                 region.assign_advice(|| "acc_y_vec",self.witness[3], row, || inputs.acc_y_vec[row])?;
    //                 region.assign_advice(|| "lambda_vec",self.witness[4], row, || inputs.lambda_vec[row])?;
    //             }

    //             Ok([r, nark_x, nark_y, acc_x, acc_y])
    //         },
    //     )
    // }
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
    pub r: Value<C::Scalar>,
}

#[derive(Clone, Default)]
pub struct ScalarMulChip<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{ 
    _marker: PhantomData<C>,
    // pub inputs: Vec<ScalarMulConfigInputs<C>> 
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

        // for inputs in self.inputs.iter() {
            // config.assign(layouter.namespace(|| "ScalarMulChip"), inputs.clone())?;
        // }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::marker::PhantomData;

    use halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fr, Fq, G1Affine, G1}, grumpkin}};
    use halo2_proofs::{halo2curves::{Coordinates, group::{Group, Curve, cofactor::CofactorCurveAffine}, CurveAffine}, arithmetic::Field};
    use itertools::Itertools;
    use crate::{accumulation::protostar::ivc::halo2::chips::scalar_mul::ec_chip_strawman::ScalarMulConfigInputs, util::arithmetic::{fe_to_fe, fe_from_bits_le}};
    use super::ScalarMulChip;
    use rand::{rngs::OsRng, Rng};

        
    #[test]
    fn ec_vec() {

        use plotters::prelude::*;
        let root = BitMapBackend::new("ECChip.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("ECChip", ("sans-serif", 60)).unwrap();

        let k = 7; 
//         let mut rng = OsRng;
//         let vec_len: usize = 129;
//         let mut pt_vec = Vec::new();
//         let mut acc_x_vec = Vec::new();
//         let mut acc_y_vec = Vec::new();
//         let rbits = (0..vec_len-1).map(|_| rng.gen_bool(1.0 / 3.0)).collect_vec();
//         // let r_window_bits = rbits[1..].chunks(2).collect_vec();
//         let r_le_bits = rbits.iter().map(|bit| 
//             Value::known(if *bit {Fq::ONE} else {Fq::ZERO}))
//             .collect_vec();

//         let mut rbits_vec = Vec::new();
//         rbits_vec = r_le_bits.clone();

//         let zero = G1::identity();
//         println!("zero {:?}", zero);
//         let mut p = G1::random(&mut rng); 
//         let acc = G1::random(&mut rng);
//         let p_single = p;
        
//         pt_vec.push(Value::known(p_single.x));
//         pt_vec.push(Value::known(p_single.y));
//         acc_x_vec.push(Value::known(p_single.x));
//         acc_y_vec.push(Value::known(p_single.y)); 


//         // | row |  r_bits   |   point   |   acc.x   |   acc.y   |  lambda   | 
//         // | 1   |    0      |     x     |    y      |    y      |    1      | 
//         // | 2   |    1      |     y     |    2y     |    2y     |    0      |
//         // | 3   |    1      |     x     |    4y     |    4y     |    1      | 
//         // | 4   |    1      |     y     |    16y    |    16y    |    0      |


//         for idx in (1..vec_len-2).step_by(2) {
//             p = G1::double(&p); 
//             nark_x_vec.push(Value::known(p.x));
//             nark_y_vec.push(Value::known(p.y));
//             let p_single = p;

//             p = G1::double(&p);
//             nark_x_vec.push(Value::known(p.x));
//             nark_y_vec.push(Value::known(p.y)); 

//             let p_triple = (p + p_single);
//             rnark_x_vec.push(Value::known(p_triple.x));
//             rnark_y_vec.push(Value::known(p_triple.y)); 

//             let acc_sel = if rbits[idx] { zero } else { p_single };

//             let acc_prev = G1Affine::from_xy(rnark_x_vec[idx-1].assign().unwrap(), rnark_y_vec[idx-1].assign().unwrap()).unwrap();
//             let acc_next = (acc_prev + acc_sel).to_affine();

//             rnark_x_vec.push(Value::known(acc_next.x));
//             rnark_y_vec.push(Value::known(acc_next.y));
//         }

//         // push last rbit 
//         p = <G1Affine as CurveAffine>::CurveExt::double(&p.into()).into(); 
//         nark_x_vec.push(Value::known(p.x));
//         nark_y_vec.push(Value::known(p.y));

//         if rbits[vec_len-2] {
//             let acc_prev = G1Affine::from_xy(rnark_x_vec[vec_len-3].assign().unwrap(), rnark_y_vec[vec_len-3].assign().unwrap()).unwrap();
//             let acc_next = (acc_prev + p).to_affine();
//             rnark_x_vec.push(Value::known(acc_next.x));
//             rnark_y_vec.push(Value::known(acc_next.y));
//         } else {
//             rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-3].assign().unwrap()));
//             rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-3].assign().unwrap()));
//         }

//         // push last element as the first rbit
//         nark_x_vec.push(Value::known(p_single.x));
//         nark_y_vec.push(Value::known(p_single.y));

//         // correct initial assumption
//         if rbits[0] {
//             rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-2].assign().unwrap()));
//             rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-2].assign().unwrap()));
//         } else {
//             let acc_prev = G1Affine::from_xy(rnark_x_vec[vec_len-2].assign().unwrap(), rnark_y_vec[vec_len-2].assign().unwrap()).unwrap();
//             let acc_next = (acc_prev - p_single).to_affine();
//             rnark_x_vec.push(Value::known(acc_next.x));
//             rnark_y_vec.push(Value::known(acc_next.y));
//         }

//         let r_lebits = rbits.iter().map(|bit| 
//             if *bit {Fr::ONE} else {Fr::ZERO})
//             .collect_vec();

//         let r = fe_from_bits_le(r_lebits);
//         let r_non_native: Fq = fe_to_fe(r);
//         rbits_vec.push(Value::known(r_non_native)); // push last element as r
//         let scalar_mul_given = (p_single * r).to_affine();
//         let scalar_mul_calc = G1Affine::from_xy(rnark_x_vec[vec_len-1].assign().unwrap(), rnark_y_vec[vec_len-1].assign().unwrap()).unwrap();
//         let acc_prime_calc  = (scalar_mul_calc + acc).to_affine();
//         let acc_prime_given = (scalar_mul_given + acc).to_affine(); // todo this should be from cyclefold struct
//         assert_eq!(scalar_mul_given, scalar_mul_calc);
//         assert_eq!(acc_prime_calc, acc_prime_given);

        // let inputs =
        //     ScalarMulConfigInputs::<grumpkin::G1Affine> { 
        //         nark_x_vec: nark_x_vec.clone(), nark_y_vec: nark_y_vec.clone(), r: Value::known(r_non_native),
        //         rbits_vec: rbits_vec.clone(), rnark_x_vec: rnark_x_vec.clone(), rnark_y_vec: rnark_y_vec.clone(), 
        //         acc_x: Value::known(acc.x), acc_y: Value::known(acc.y), 
        //         acc_prime_calc_x: Value::known(acc_prime_calc.x), 
        //         acc_prime_calc_y: Value::known(acc_prime_calc.y), 
        //         acc_prime_given_x: Value::known(acc_prime_given.x), 
        //         acc_prime_given_y: Value::known(acc_prime_given.y) 
        //     };   

        let circuit = ScalarMulChip::<grumpkin::G1Affine> { _marker: PhantomData };
        MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();

        halo2_base::halo2_proofs::dev::CircuitLayout::default()
        .render(k, &circuit, &root)
        .unwrap();
    }

}
