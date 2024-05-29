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

pub const NUM_ADVICE_SM: usize = 5;
pub const NUM_FIXED: usize = 1;

#[derive(Clone, Debug)]
pub struct ScalarMulChipConfig<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    witness: [Column<Advice>; NUM_ADVICE_SM],
    selector: [Selector; NUM_ADVICE_SM],
    _marker: PhantomData<C>,
}

impl<C> ScalarMulChipConfig<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub fn configure(meta: &mut ConstraintSystem<C::Scalar>, advices: [Column<Advice>; NUM_ADVICE_SM]) -> Self {

        // | row | r_bits_le | witness.x | witness.y | witness.x  |  witness.y |
        // | 0   |   1       |     x     |   y       |    x       |    y       |
        // | 1   |   0       |    2x     |  2y       |    6x      |   6y       |
        // | 2   |   1       |    4x     |  4y       |    5x      |   5y       |
        // | 3   |   1       |    8x     |  8y       |    24x     |   24y      |
        // | 4   |   1       |    16x    |  16y      |    29x     |   29y      |


        let [col_rbits, col_px, col_py, col_acc_x, col_acc_y] = 
            advices;
    
        let [q_ec_double, q_ec_add_unequal, q_ec_acc_add_unequal, q_ec_add_unequal_last, q_ec_sub_unequal_last] = 
            [(); 5].map(|_| meta.selector());
        
            meta.create_gate("ec_double", |meta| {

                let q_ec_double = meta.query_selector(q_ec_double);
                let x = meta.query_advice(col_px, Rotation(0));
                let y = meta.query_advice(col_py, Rotation(0));
                let x2 = meta.query_advice(col_px, Rotation(1));
                let y2 = meta.query_advice(col_py, Rotation(1));

                let two = Expression::Constant(C::Scalar::from(2));
                let three = Expression::Constant(C::Scalar::from(3));
                let four = Expression::Constant(C::Scalar::from(4));
                let nine = Expression::Constant(C::Scalar::from(9));

                let x_sq = x.clone() * x.clone();
                let x_pow3 = x_sq.clone() * x.clone();
                let x_pow4 = x_sq.clone() * x_sq.clone();
                let y_sq = y.clone() * y.clone();


                //  4y^2 xout = 9x^4 -  4y^2 * 2x
                //  2y*yout = -3x^2x’ +  3x^3  -  2y * y

                vec![q_ec_double.clone() * (four.clone() * y_sq.clone() * x2.clone() - nine * x_pow4.clone() + four * y_sq.clone()* two.clone() * x.clone()),
                     q_ec_double * (two.clone() * y.clone() * y2.clone() + three.clone() * x_sq.clone() * x2.clone() - three * x_pow3.clone() + two * y.clone() * y.clone())]
            
            });


            meta.create_gate("ec_add_unequal", |meta| {

                let q_ec_add_unequal = meta.query_selector(q_ec_add_unequal);
                let x = meta.query_advice(col_px, Rotation(0));
                let y = meta.query_advice(col_py, Rotation(0));
                let x2 = meta.query_advice(col_px, Rotation(1));
                let y2 = meta.query_advice(col_py, Rotation(1));
                let x3 = meta.query_advice(col_acc_x, Rotation(0));
                let y3 = meta.query_advice(col_acc_y, Rotation(0));

                let dx = x2.clone() - x.clone();
                let dy = y2.clone() - y.clone();
                let dx_sq = dx.clone() * dx.clone();
                let dy_sq = dy.clone() * dy.clone();


                //  x_3 * dx_sq = dy_sq - x_1 * dx_sq - x_2 * dx_sq
                //  y_3 * dx = dy * (x_1 - x_3) - y_1 * dx

                vec![q_ec_add_unequal.clone() * (x3.clone() * dx_sq.clone() - dy_sq.clone() + x.clone() * dx_sq.clone() + x2.clone() * dx_sq.clone()),
                     q_ec_add_unequal * (y3.clone() * dx.clone() - dy.clone() * (x.clone() - x3.clone()) + y.clone() * dx.clone())]

            });


        // | row | r_bits_le | witness.x | witness.y | witness.x  |  witness.y |
        // | 0   |   1       |     x     |   y       |    x       |    y       |
        // | 1   |   0       |    2x     |  2y       |    6x      |   6y       |
        // | 2   |   1       |    4x     |  4y       |    5x      |   5y       |
        // | 3   |   1       |    8x     |  8y       |    24x     |   24y      |
        // | 4   |   1       |    16x    |  16y      |    29x     |   29y      |


            meta.create_gate("ec_acc_add_unequal", |meta| {

                let q_ec_acc_add_unequal = meta.query_selector(q_ec_acc_add_unequal);
                let x = meta.query_advice(col_px, Rotation(0));
                let y = meta.query_advice(col_py, Rotation(0));
                let x2 = meta.query_advice(col_px, Rotation(1));
                let y2 = meta.query_advice(col_py, Rotation(1));
                let x3 = meta.query_advice(col_acc_x, Rotation(0));
                let y3 = meta.query_advice(col_acc_y, Rotation(0));
                let acc_prev_x = meta.query_advice(col_acc_x, Rotation(-1));
                let acc_prev_y = meta.query_advice(col_acc_y, Rotation(-1));
                let acc_next_x = meta.query_advice(col_acc_x, Rotation(1));
                let acc_next_y = meta.query_advice(col_acc_y, Rotation(1));

                let r0 = meta.query_advice(col_rbits, Rotation(0));
                let r1 = meta.query_advice(col_rbits, Rotation(1));
                let one = Expression::Constant(C::Scalar::ONE);
                let zero = Expression::Constant(C::Scalar::ZERO);

                // (1-q0)(1-q1)*zero + q0(1-q1)*x + (1-q0)q1*2x + q0q1*3x 
                let sel_x = r0.clone() * r1.clone() * x3.clone() + 
                            r0.clone() * (one.clone() - r1.clone()) * x.clone() + 
                            (one.clone() - r0.clone()) * r1.clone() * x2.clone() +
                            zero.clone(); //(one.clone() - r0.clone())*(one.clone() - r1.clone()); 

                let sel_y = r0.clone() * r1.clone() * y3.clone() + 
                            r0.clone() * (one.clone() - r1.clone()) * y.clone() + 
                            (one.clone() - r0.clone()) * r1.clone() * y2.clone() +
                            zero.clone(); 

                let dx = sel_x.clone() - acc_prev_x.clone();
                let dy = sel_y.clone() - acc_prev_y.clone();
                let dx_sq = dx.clone() * dx.clone();
                let dy_sq = dy.clone() * dy.clone();


                // if r0 != 0 && r1 != 0 otherwise acc_prev = acc_next
                // x_3 * dx_sq = dy_sq - x_1 * dx_sq - x_2 * dx_sq
                // y_3 * dx = dy * (x_1 - x_3) - y_1 * dx

                vec![q_ec_acc_add_unequal.clone() * ((r0.clone() * r1.clone() + r0.clone() * (one.clone() - r1.clone()) + (one.clone() - r0.clone()) * r1.clone()) *
                    (acc_next_x.clone() * dx_sq.clone() - dy_sq.clone() + acc_prev_x.clone() * dx_sq.clone() + sel_x.clone() * dx_sq.clone()) + (one.clone() - r0.clone())*(one.clone() - r1.clone())*(acc_next_x.clone() - acc_prev_x.clone())),
                     q_ec_acc_add_unequal * ((r0.clone() * r1.clone() + r0.clone() * (one.clone() - r1.clone()) + (one.clone() - r0.clone()) * r1.clone()) * 
                    (acc_next_y.clone() * dx.clone() - dy.clone() * (acc_prev_x.clone() - acc_next_x.clone()) + acc_prev_y.clone() * dx.clone()) + (one.clone() - r0.clone())*(one.clone() - r1.clone())*(acc_next_y.clone() - acc_prev_y.clone()))]
            });


            meta.create_gate("ec_add_unequal_r0_last", |meta| {

                let q_ec_add_unequal_last = meta.query_selector(q_ec_add_unequal_last);
                let acc_prev_x = meta.query_advice(col_acc_x, Rotation(-1));
                let acc_prev_y = meta.query_advice(col_acc_y, Rotation(-1));
                let x2 = meta.query_advice(col_px, Rotation(0));
                let y2 = meta.query_advice(col_py, Rotation(0));
                let x3 = meta.query_advice(col_acc_x, Rotation(0));
                let y3 = meta.query_advice(col_acc_y, Rotation(0));
                let r0 = meta.query_advice(col_rbits, Rotation(0));

                let dx = x2.clone() - acc_prev_x.clone();
                let dy = y2.clone() - acc_prev_y.clone();
                let dx_sq = dx.clone() * dx.clone();
                let dy_sq = dy.clone() * dy.clone();
                let one = Expression::Constant(C::Scalar::ONE);

                //  x_3 * dx_sq = dy_sq - x_1 * dx_sq - x_2 * dx_sq
                //  y_3 * dx = dy * (x_1 - x_3) - y_1 * dx

                vec![q_ec_add_unequal_last.clone() * (r0.clone() * (x3.clone() * dx_sq.clone() - dy_sq.clone() + acc_prev_x.clone() * dx_sq.clone() + x2.clone() * dx_sq.clone()) +
                    ((one.clone() - r0.clone()) * (x3.clone() - acc_prev_x.clone()))),
                     q_ec_add_unequal_last * (r0.clone() * (y3.clone() * dx.clone() - dy.clone() * (acc_prev_x.clone() - x3.clone()) + acc_prev_y.clone() * dx.clone()) + 
                    ((one.clone() - r0.clone()) * (y3.clone() - acc_prev_y.clone())))]
            });
            

            meta.create_gate("ec_sub_unequal_last", |meta| {
    
                let q_ec_sub_unequal_last = meta.query_selector(q_ec_sub_unequal_last);
                let x1 = meta.query_advice(col_acc_x, Rotation(-1));
                let y1 = meta.query_advice(col_acc_y, Rotation(-1));
                let x2 = meta.query_advice(col_px, Rotation(0));
                let y2 = meta.query_advice(col_py, Rotation(0));
                let x_out = meta.query_advice(col_acc_x, Rotation(0));
                let y_out = meta.query_advice(col_acc_y, Rotation(0));
                let r0 = meta.query_advice(col_rbits, Rotation(0));
    
                let dx = x2.clone() - x1.clone();
                let sy = y2.clone() + y1.clone();
                let dx_sq = dx.clone() * dx.clone();
                let sy_sq = sy.clone() * sy.clone();
                let one = Expression::Constant(C::Scalar::ONE);


                //  x_3 * dx_sq = sy_sq - x_1 * dx_sq - x_2 * dx_sq
                //  y_3 * dx = -sy * (x_1 - x_3) +  y_1 * dx
    
                vec![q_ec_sub_unequal_last.clone() * ((one.clone() - r0.clone()) * (x_out.clone() * dx_sq.clone() - sy_sq.clone() + x1.clone() * dx_sq.clone() + x2.clone() * dx_sq.clone()) + 
                    (r0.clone() * (x_out.clone() - x1.clone()))),
                     q_ec_sub_unequal_last * ((one.clone() - r0.clone()) * (y_out.clone() * dx.clone() + sy.clone() * (x1.clone() - x_out.clone()) + y1.clone() * dx.clone()) +
                    (r0.clone() * (y_out.clone() - y1.clone())))]
    
            });

        Self { 
            witness: [col_rbits, col_px, col_py, col_acc_x, col_acc_y], 
            selector: [q_ec_double, q_ec_add_unequal, q_ec_acc_add_unequal, q_ec_add_unequal_last, q_ec_sub_unequal_last],
            _marker: PhantomData 
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        inputs: ScalarMulConfigInputs<C>,
    ) -> Result<[AssignedCell<C::Scalar, C::Scalar>; NUM_ADVICE_SM], Error> {

        layouter.assign_region(
            || "ScalarMulChipConfig assign",
            |mut region| {

        // | row | r_bits_le | witness.x | witness.y | witness.x  |  witness.y |
        // | 0   |   1       |     x     |   y       |    x       |    y       |
        // | 1   |   0       |    2x     |  2y       |    6x      |   6y       |
        // | 2   |   1       |    4x     |  4y       |    5x      |   5y       |
        // | 3   |   1       |    8x     |  8y       |    24x     |   24y      |
        // | 4   |   1       |    16x    |  16y      |    29x     |   29y      |


            let nark_vec_len = inputs.nark_x_vec.len();
            assert_eq!(inputs.nark_x_vec.len(), inputs.nark_y_vec.len());
            assert_eq!(inputs.rnark_y_vec.len(), inputs.rnark_x_vec.len());

                for row in 0..nark_vec_len {
                    region.assign_advice(|| "r_vec",self.witness[0], row, || inputs.rbits_vec[row])?;
                    region.assign_advice(|| "nark_x_vec",self.witness[1], row, || inputs.nark_x_vec[row])?;
                    region.assign_advice(|| "nark_y_vec",self.witness[2], row, || inputs.nark_y_vec[row])?;
                    region.assign_advice(|| "rnark_x_vec",self.witness[3], row, || inputs.rnark_x_vec[row])?;
                    region.assign_advice(|| "rnark_y_vec",self.witness[4], row, || inputs.rnark_y_vec[row])?;

                    if row != 0 {
                        if row != nark_vec_len - 1 {
                            self.selector[0].enable(&mut region, row - 1)?;
                        }

                        if row % 2 != 0 && row < nark_vec_len - 3 {
                            self.selector[1].enable(&mut region, row)?;
                            self.selector[2].enable(&mut region, row)?;
                        }

                        if row == nark_vec_len - 2 {
                            self.selector[3].enable(&mut region, row)?;
                        }

                        if row == nark_vec_len - 1 {
                            self.selector[4].enable(&mut region, row)?;
                        }
                    }
                }

                // todo uncomment
                let third_last_row = nark_vec_len;
                let second_last_row = third_last_row + 1;
                self.selector[3].enable(&mut region, third_last_row)?;

                region.assign_advice(|| "r0_is_one_always_add", self.witness[0], third_last_row, || Value::known(C::Scalar::ONE))?;
                let nark_x = region.assign_advice(|| "nark_x", self.witness[3], second_last_row, || inputs.nark_x_vec[0])?;
                let nark_y = region.assign_advice(|| "nark_y", self.witness[4], second_last_row, || inputs.nark_y_vec[0])?;
                let acc_x = region.assign_advice(|| "acc_x", self.witness[1], third_last_row, || inputs.acc_x)?;
                let acc_y = region.assign_advice(|| "acc_y", self.witness[2], third_last_row, || inputs.acc_y)?;
                let r = region.assign_advice(|| "r", self.witness[0], second_last_row, || inputs.r)?;

                let acc_prime_calc_x = region.assign_advice(|| "acc_prime_calc_x", self.witness[3], third_last_row, || inputs.acc_prime_calc_x)?;
                let acc_prime_calc_y = region.assign_advice(|| "acc_prime_calc_y", self.witness[4], third_last_row, || inputs.acc_prime_calc_y)?;
                let acc_prime_given_x = region.assign_advice(|| "acc_prime_given_x", self.witness[1], second_last_row, || inputs.acc_prime_given_x)?;
                let acc_prime_given_y = region.assign_advice(|| "acc_prime_given_y", self.witness[2], second_last_row, || inputs.acc_prime_given_y)?;
                region.constrain_equal(acc_prime_calc_x.cell(), acc_prime_given_x.cell());
                region.constrain_equal(acc_prime_calc_y.cell(), acc_prime_given_y.cell());

                Ok([r, nark_x, nark_y, acc_x, acc_y])
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
    pub nark_x_vec: Vec<Value<C::Scalar>>,
    pub nark_y_vec: Vec<Value<C::Scalar>>,
    pub rnark_x_vec: Vec<Value<C::Scalar>>,
    pub rnark_y_vec: Vec<Value<C::Scalar>>,
    pub r: Value<C::Scalar>,
    pub acc_x: Value<C::Scalar>,
    pub acc_y: Value<C::Scalar>,
    pub acc_prime_calc_x: Value<C::Scalar>,
    pub acc_prime_calc_y: Value<C::Scalar>,
    pub acc_prime_given_x: Value<C::Scalar>,
    pub acc_prime_given_y: Value<C::Scalar>,
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
    use halo2_base::halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fr, Fq, G1Affine, G1}, grumpkin}};
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

        let k = 10; 
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

        // push last element as the first rbit
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
            ScalarMulConfigInputs::<grumpkin::G1Affine> { 
                nark_x_vec: nark_x_vec.clone(), nark_y_vec: nark_y_vec.clone(), r: Value::known(r_non_native),
                rbits_vec: rbits_vec.clone(), rnark_x_vec: rnark_x_vec.clone(), rnark_y_vec: rnark_y_vec.clone(), 
                acc_x: Value::known(acc.x), acc_y: Value::known(acc.y), 
                acc_prime_calc_x: Value::known(acc_prime_calc.x), 
                acc_prime_calc_y: Value::known(acc_prime_calc.y), 
                acc_prime_given_x: Value::known(acc_prime_given.x), 
                acc_prime_given_y: Value::known(acc_prime_given.y) 
            };   

        let circuit = ScalarMulChip::<grumpkin::G1Affine> { inputs: vec![inputs; 6] };
        MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();

        halo2_base::halo2_proofs::dev::CircuitLayout::default()
        .render(k, &circuit, &root)
        .unwrap();
    }

}


    // pub fn sm_config_inputs(
    //     &self,
    //     sm_inputs: &Vec<ScalarMulChipInputs<C::Scalar, C::Secondary>>
    // ) -> Result<Vec<ScalarMulConfigInputs<C>>, Error> {

    //     let vec_len: usize = 129;
    //     let mut sm_config_inputs = Vec::new();
    //     for inputs in sm_inputs{
    //         let mut nark_x_vec = Vec::new();
    //         let mut nark_y_vec = Vec::new();
    //         let mut rnark_x_vec = Vec::new();
    //         let mut rnark_y_vec = Vec::new();

    //         let one = C::Scalar::ONE;
    //         let zero = C::Scalar::ZERO;
    //         let r_le_bits = &inputs.r_le_bits;
    //         let r_le_bits_value = r_le_bits.iter().map(|fe| Value::known(*fe)).collect_vec();
    //         let r_window_bits = r_le_bits[1..].chunks(2).collect_vec();

    //         // push last element as the first rbit
    //         let mut rbits_vec = Vec::new();
    //         rbits_vec = r_le_bits_value.clone();
    //         rbits_vec.push(r_le_bits_value[0]);

    //         let p_zero = C::Secondary::identity();
    //         let mut p = inputs.nark_comm; 
    //         let acc = inputs.acc_comm;
    //         let r = inputs.r;
    //         let p_single = p;
            
    //         // initial assumption: rbits[0] = 1
    //         let p_single_x = into_coordinates(&p_single)[0];
    //         let p_single_y = into_coordinates(&p_single)[1];
    //         nark_x_vec.push(Value::known(p_single_x));
    //         nark_y_vec.push(Value::known(p_single_y));
    //         rnark_x_vec.push(Value::known(p_single_x));
    //         rnark_y_vec.push(Value::known(p_single_y)); 

    //         for idx in (1..vec_len-2).step_by(2) {
    //             p = <C::Secondary as CurveAffine>::CurveExt::double(&p.into()).into(); 
    //             nark_x_vec.push(Value::known(into_coordinates(&p)[0]));
    //             nark_y_vec.push(Value::known(into_coordinates(&p)[1]));
    //             let p_single = p;

    //             p = <C::Secondary as CurveAffine>::CurveExt::double(&p.into()).into();
    //             nark_x_vec.push(Value::known(into_coordinates(&p)[0]));
    //             nark_y_vec.push(Value::known(into_coordinates(&p)[1])); 

    //             let p_triple = (p + p_single).to_affine();
    //             rnark_x_vec.push(Value::known(into_coordinates(&p_triple)[0]));
    //             rnark_y_vec.push(Value::known(into_coordinates(&p_triple)[0])); 

    //             let acc_sel = match r_window_bits[idx/2] {
    //                 [z, o] if *z == zero && *o == zero => p_zero,    // 00
    //                 [z, o] if *z == one && *o == zero => p_single,   // 10
    //                 [z, o] if *z == zero && *o == one => p,          // 01
    //                 [z, o] if *z == one && *o == one => p_triple,    // 11
    //                 _ => panic!("Invalid window"),
    //             };

    //             let acc_prev = C::Secondary::from_xy(rnark_x_vec[idx-1].assign().unwrap(), rnark_y_vec[idx-1].assign().unwrap()).unwrap();
    //             let acc_next = (acc_prev + acc_sel).to_affine();

    //             rnark_x_vec.push(Value::known(into_coordinates(&acc_next)[0]));
    //             rnark_y_vec.push(Value::known(into_coordinates(&acc_next)[1]));

    //         }

    //         // push last rbit 
    //         p = <C::Secondary as CurveAffine>::CurveExt::double(&p.into()).into(); 
    //         nark_x_vec.push(Value::known(into_coordinates(&p)[0]));
    //         nark_y_vec.push(Value::known(into_coordinates(&p)[1]));

    //         if r_le_bits[vec_len-2] == one {
    //             let acc_prev = C::Secondary::from_xy(rnark_x_vec[vec_len-3].assign().unwrap(), rnark_y_vec[vec_len-3].assign().unwrap()).unwrap();
    //             let acc_next = (acc_prev + p).to_affine();
    //             rnark_x_vec.push(Value::known(into_coordinates(&acc_next)[0]));
    //             rnark_y_vec.push(Value::known(into_coordinates(&acc_next)[1]));
    //         } else {
    //             rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-3].assign().unwrap()));
    //             rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-3].assign().unwrap()));
    //         }

    //         // push last element as the first rbit
    //         nark_x_vec.push(Value::known(into_coordinates(&p_single)[0]));
    //         nark_y_vec.push(Value::known(into_coordinates(&p_single)[1]));

    //         // correct initial assumption
    //         if r_le_bits[0] == one {
    //             rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-2].assign().unwrap()));
    //             rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-2].assign().unwrap()));
    //         } else {
    //             let acc_prev = C::Secondary::from_xy(rnark_x_vec[vec_len-2].assign().unwrap(), rnark_y_vec[vec_len-2].assign().unwrap()).unwrap();
    //             let acc_next = (acc_prev - p_single).to_affine();
    //             rnark_x_vec.push(Value::known(into_coordinates(&acc_next)[0]));
    //             rnark_y_vec.push(Value::known(into_coordinates(&acc_next)[1]));
    //         }
    //         let r_non_native: C::Base = fe_to_fe(r);
    //         let add_and_convert_affine_time = Instant::now();
    //         let result = (p_single + p_single).to_affine();
    //         println!("add_and_convert_affine_time: {:?}", add_and_convert_affine_time.elapsed());
            
    //         let add_time = Instant::now();
    //         let result = (p_single + p_single);
    //         println!("add_time: {:?}", add_time.elapsed());

    //         let scalar_mul_given = (p_single * r_non_native).to_affine();
    //         let scalar_mul_calc = C::Secondary::from_xy(rnark_x_vec[vec_len-1].assign().unwrap(), rnark_y_vec[vec_len-1].assign().unwrap()).unwrap();
    //         let acc_prime_calc  = (scalar_mul_calc + acc).to_affine();
    //         let acc_prime_given = inputs.acc_prime_comm; 
    //         assert_eq!(acc_prime_calc, acc_prime_given);
    //         assert_eq!(scalar_mul_given, scalar_mul_calc);

    //         let inputs =
    //             ScalarMulConfigInputs::<C> { 
    //                 rbits_vec, r: Value::known(r), nark_x_vec, nark_y_vec, rnark_x_vec, rnark_y_vec, 
    //                 acc_x: Value::known(into_coordinates(&acc)[0]), 
    //                 acc_y: Value::known(into_coordinates(&acc)[1]), 
    //                 acc_prime_calc_x: Value::known(into_coordinates(&acc_prime_calc)[0]), 
    //                 acc_prime_calc_y: Value::known(into_coordinates(&acc_prime_calc)[1]), 
    //                 acc_prime_given_x: Value::known(into_coordinates(&acc_prime_given)[0]), 
    //                 acc_prime_given_y: Value::known(into_coordinates(&acc_prime_given)[1])
    //             };

    //         sm_config_inputs.push(inputs);
    //     }

    //     Ok(sm_config_inputs)
    // }