use halo2_base::{halo2_proofs::
    {circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector, Expression, Assigned, Fixed},
    poly::Rotation, 
    halo2curves::{bn256::{G1Affine, G1}, grumpkin},
}, 
gates::flex_gate::{FlexGateConfig, FlexGateConfigParams},
utils::{CurveAffineExt, ScalarField, BigPrimeField},
};
use halo2_base::{
    gates::GateInstructions,
    utils::bit_length,
    AssignedValue, Context,
};
use halo2_proofs::halo2curves::{Coordinates, group::Group, CurveAffine};
use itertools::Itertools;
use std::{
    iter,
    marker::PhantomData,
    sync::{RwLock, RwLockReadGuard},
};

use crate::util::arithmetic::{TwoChainCurve, PrimeFieldBits};

pub const NUM_ADVICE: usize = 1;
pub const NUM_FIXED: usize = 1;

#[derive(Clone, Debug)]
pub struct ScalarMulChipConfig<F: ScalarField> {
    witness: [Column<Advice>; 5],
    selector: [Selector; 5],
    _marker: PhantomData<F>,
}

impl<F: ScalarField> ScalarMulChipConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {

        // | row | r_bits_le | witness.x | witness.y | witness.x  |  witness.y |
        // | 0   |   1       |     x     |   y       |    x       |    y       |
        // | 1   |   0       |    2x     |  2y       |    6x      |   6y       |
        // | 2   |   1       |    4x     |  4y       |    5x      |   5y       |
        // | 3   |   1       |    8x     |  8y       |    24x     |   24y      |
        // | 4   |   1       |    16x    |  16y      |    29x     |   29y      |


        let [col_rbits, col_px, col_py, col_acc_x, col_acc_y] = 
            [(); 5].map(|_| meta.advice_column());

        let [q_ec_double, q_ec_add_unequal, q_ec_acc_add_unequal, q_ec_add_unequal_last, q_ec_sub_unequal_last] = 
            [(); 5].map(|_| meta.selector());
        
            meta.create_gate("ec_double", |meta| {

                let q_ec_double = meta.query_selector(q_ec_double);
                let x = meta.query_advice(col_px, Rotation(0));
                let y = meta.query_advice(col_py, Rotation(0));
                let x2 = meta.query_advice(col_px, Rotation(1));
                let y2 = meta.query_advice(col_py, Rotation(1));

                let two = Expression::Constant(F::from(2));
                let three = Expression::Constant(F::from(3));
                let four = Expression::Constant(F::from(4));
                let nine = Expression::Constant(F::from(9));

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


            meta.create_gate("ec_add_unequal_last", |meta| {

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
                let one = Expression::Constant(F::ONE);

                //  x_3 * dx_sq = dy_sq - x_1 * dx_sq - x_2 * dx_sq
                //  y_3 * dx = dy * (x_1 - x_3) - y_1 * dx

                vec![q_ec_add_unequal_last.clone() * (r0.clone() * (x3.clone() * dx_sq.clone() - dy_sq.clone() + acc_prev_x.clone() * dx_sq.clone() + x2.clone() * dx_sq.clone()) +
                    ((one.clone() - r0.clone()) * (x3.clone() - acc_prev_x.clone()))),
                     q_ec_add_unequal_last * (r0.clone() * (y3.clone() * dx.clone() - dy.clone() * (acc_prev_x.clone() - x3.clone()) + acc_prev_y.clone() * dx.clone()) + 
                    ((one.clone() - r0.clone()) * (y3.clone() - acc_prev_y.clone())))]
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
                let one = Expression::Constant(F::ONE);
                let zero = Expression::Constant(F::ZERO);

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
                let one = Expression::Constant(F::ONE);


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
}


#[derive(Clone, Default)]
pub struct ScalarMulChip<F: ScalarField> 
{
    pub x_vec: Vec<Value<F>>,
    pub y_vec: Vec<Value<F>>,
    pub r_vec: Vec<Value<F>>,
    pub acc_x_vec: Vec<Value<F>>,
    pub acc_y_vec: Vec<Value<F>>,
}

impl<F: ScalarField> Circuit<F> for ScalarMulChip<F> 
{
    type Params = FlexGateConfigParams;
    type Config = ScalarMulChipConfig<F>; 
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        ScalarMulChipConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "ScalarMulChip",
            |mut region| {


        // | row | r_bits_le | witness.x | witness.y | witness.x  |  witness.y |
        // | 0   |   1       |     x     |   y       |    x       |    y       |
        // | 1   |   0       |    2x     |  2y       |    6x      |   6y       |
        // | 2   |   1       |    4x     |  4y       |    5x      |   5y       |
        // | 3   |   1       |    8x     |  8y       |    24x     |   24y      |
        // | 4   |   1       |    16x    |  16y      |    29x     |   29y      |


            let nrows = self.x_vec.len();
            assert_eq!(self.x_vec.len(), self.y_vec.len());

                for row in 0..nrows {

                    region.assign_advice(|| "x",config.witness[1], row, || self.x_vec[row])?;
                    region.assign_advice(|| "y",config.witness[2], row, || self.y_vec[row])?;
                    region.assign_advice(|| "acc_x",config.witness[3], row, || self.acc_x_vec[row])?;
                    region.assign_advice(|| "acc_y",config.witness[4], row, || self.acc_y_vec[row])?;
                    region.assign_advice(|| "r_vec",config.witness[0], row, || self.r_vec[row])?;


                    if row != 0 {

                        if row != nrows - 1 {
                            config.selector[0].enable(&mut region, row - 1)?;
                        }

                        if row % 2 != 0 && row < nrows - 3 {
                            config.selector[1].enable(&mut region, row)?;
                            config.selector[2].enable(&mut region, row)?;
                        }

                        if row == nrows - 2 {
                            config.selector[3].enable(&mut region, row)?;
                        }

                        if row == nrows - 1 {
                            config.selector[4].enable(&mut region, row)?;
                        }

                    }
                    
                }

                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod test {
    use halo2_base::halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::{bn256::{Fr, Fq, G1Affine, G1}, grumpkin}};
    use halo2_proofs::{halo2curves::{Coordinates, group::{Group, Curve, cofactor::CofactorCurveAffine}, CurveAffine}, arithmetic::Field};
    use itertools::Itertools;
    use crate::util::arithmetic::{fe_to_fe, fe_from_bits_le};
    use super::ScalarMulChip;
    use rand::{rngs::OsRng, Rng};

        
    #[test]
    fn test_ec_vec() {
        let k = 8; 
        let mut rng = OsRng;
        let vec_len: usize = 129;
        let mut x_vec = Vec::new();
        let mut y_vec = Vec::new();
        let mut acc_x_vec = Vec::new();
        let mut acc_y_vec = Vec::new();
        let rbits = (0..vec_len-1).map(|_| rng.gen_bool(1.0 / 3.0)).collect_vec();
        let r_window_bits = rbits[1..].chunks(2).collect_vec();
        let r_le_bits = rbits.iter().map(|bit| 
            Value::known(if *bit {Fq::ONE} else {Fq::ZERO}))
            .collect_vec();

        // push last element as the first rbit
        let mut r_vec = Vec::new();
        r_vec = r_le_bits.clone();
        r_vec.push(r_le_bits[0]);

        let zero = G1Affine::identity();
        let mut p = G1Affine::random(&mut rng); 
        let p_single = p;
        
        // initial assumption: rbits[0] = 1
        x_vec.push(Value::known(p_single.x));
        y_vec.push(Value::known(p_single.y));
        acc_x_vec.push(Value::known(p_single.x));
        acc_y_vec.push(Value::known(p_single.y)); 


        // | row | r_bits_le | witness.x | witness.y | witness.x  |  witness.y |
        // | 0   |   0       |     x     |   y       |    x       |    y       |
        // | 1   |   0       |    2x     |  2y       |    6x      |   6y       |
        // | 2   |   1       |    4x     |  4y       |    5x      |   5y       |
        // | 3   |   1       |    8x     |  8y       |    24x     |   24y      |
        // | 4   |   1       |    16x    |  16y      |    29x     |   29y      |
        // | 5   |   1       |    32x    |  32y      |    61x     |   61y      |
        // |last | rbits[0]  |    x      |   y       |    60x     |   60y      |

        for idx in (1..vec_len-2).step_by(2) {
            p = <G1Affine as CurveAffine>::CurveExt::double(&p.into()).into(); 
            x_vec.push(Value::known(p.x));
            y_vec.push(Value::known(p.y));
            let p_single = p;

            p = <G1Affine as CurveAffine>::CurveExt::double(&p.into()).into();
            x_vec.push(Value::known(p.x));
            y_vec.push(Value::known(p.y)); 

            let p_triple = (p + p_single).to_affine();
            acc_x_vec.push(Value::known(p_triple.x));
            acc_y_vec.push(Value::known(p_triple.y)); 

            let acc_sel = match r_window_bits[idx/2] {
                [false, false] => zero,                             // 00
                [true, false] => p_single,                          // 10
                [false, true] => p,                                 // 01
                [true, true] =>  p_triple,                          // 11
                _ => panic!("Invalid window"),
            };

            let acc_prev = G1Affine::from_xy(acc_x_vec[idx-1].assign().unwrap(), acc_y_vec[idx-1].assign().unwrap()).unwrap();
            let acc_next = (acc_prev + acc_sel).to_affine();

            acc_x_vec.push(Value::known(acc_next.x));
            acc_y_vec.push(Value::known(acc_next.y));

        }

        // push last rbit 
        p = <G1Affine as CurveAffine>::CurveExt::double(&p.into()).into(); 
        x_vec.push(Value::known(p.x));
        y_vec.push(Value::known(p.y));

        if rbits[vec_len-2] {
            let acc_prev = G1Affine::from_xy(acc_x_vec[vec_len-3].assign().unwrap(), acc_y_vec[vec_len-3].assign().unwrap()).unwrap();
            let acc_next = (acc_prev + p).to_affine();
            acc_x_vec.push(Value::known(acc_next.x));
            acc_y_vec.push(Value::known(acc_next.y));
        } else {
            acc_x_vec.push(Value::known(acc_x_vec[vec_len-3].assign().unwrap()));
            acc_y_vec.push(Value::known(acc_y_vec[vec_len-3].assign().unwrap()));
        }

        // push last element as the first rbit
        x_vec.push(Value::known(p_single.x));
        y_vec.push(Value::known(p_single.y));

        // correct initial assumption
        if rbits[0] {
            acc_x_vec.push(Value::known(acc_x_vec[vec_len-2].assign().unwrap()));
            acc_y_vec.push(Value::known(acc_y_vec[vec_len-2].assign().unwrap()));
        } else {
            let acc_prev = G1Affine::from_xy(acc_x_vec[vec_len-2].assign().unwrap(), acc_y_vec[vec_len-2].assign().unwrap()).unwrap();
            let acc_next = (acc_prev - p_single).to_affine();
            acc_x_vec.push(Value::known(acc_next.x));
            acc_y_vec.push(Value::known(acc_next.y));
        }

        let r_lebits = rbits.iter().map(|bit| 
            if *bit {Fr::ONE} else {Fr::ZERO})
            .collect_vec();
        let r_lebits_num = fe_from_bits_le(r_lebits);
        let result = (p_single * r_lebits_num).to_affine();
        let circuit_result = G1Affine::from_xy(acc_x_vec[vec_len-1].assign().unwrap(), acc_y_vec[vec_len-1].assign().unwrap()).unwrap();
        assert_eq!(result, circuit_result);

        let circuit = ScalarMulChip::<Fq> { x_vec, y_vec, r_vec, acc_x_vec, acc_y_vec };
        MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();
    
    }

}
