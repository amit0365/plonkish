use halo2_proofs::
    {circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector, Expression, Assigned, Fixed},
    poly::Rotation, 
    halo2curves::{bn256::{G1Affine, G2Affine, G1}, grumpkin::{self, Fr as Fq}},
};
use halo2_base::utils::{CurveAffineExt, ScalarField, BigPrimeField};
use halo2_proofs::halo2curves::{group::Group, grumpkin::Fr, Coordinates, CurveAffine};
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
                let acc_z = meta.query_advice(col_lambda, Rotation(0));
                // let acc_z = Expression::Constant(C::Scalar::ONE);

                let acc_next_x = meta.query_advice(col_acc_x, Rotation(1));
                let acc_next_y = meta.query_advice(col_acc_y, Rotation(1));
                let acc_next_z = meta.query_advice(col_lambda, Rotation(1));
                // let acc_next_z = Expression::Constant(C::Scalar::ONE);
                // let lambda = meta.query_advice(col_lambda, Rotation(0));

                let zero = Expression::Constant(C::Scalar::ZERO);
                let one = Expression::Constant(C::Scalar::ONE);
                let two = Expression::Constant(C::Scalar::from(2));
                let three = Expression::Constant(C::Scalar::from(3));

                let b = three.clone(); // todo change for other curve
                let nine = Expression::Constant(C::Scalar::from(9));
                let eight = Expression::Constant(C::Scalar::from(8));
                let twenty_four = Expression::Constant(C::Scalar::from(24));
                let twenty_seven = Expression::Constant(C::Scalar::from(27)); // nine * b
                let seventy_two = Expression::Constant(C::Scalar::from(72)); // twenty_four * b
                let acc_x_sq = acc_x.clone() * acc_x.clone();
                let acc_y_sq = acc_y.clone() * acc_y.clone();
                let acc_z_sq = acc_z.clone() * acc_z.clone();
                //let acc_z_sq = one.clone();

                
                // pt double, b = 3 for bn254
                //  x' = 2xy(y^2 - 9bz^2)
                //  y' = (y^2 - 9bz^2)(y^2 + 3bz^2) + 24*b*y^2*z^2 
                //  z' = 8y^3*z

                // simplified for b = 3, 
                let acc_double_x = two * acc_x.clone() * acc_y.clone() * (acc_y_sq.clone() - twenty_seven.clone() * acc_z_sq.clone());
                let acc_double_y = (acc_y_sq.clone() - twenty_seven.clone() * acc_z_sq.clone()) 
                                 * (acc_y_sq.clone() + nine.clone() * acc_z_sq.clone()) + seventy_two.clone() * acc_y_sq.clone() * acc_z_sq.clone();
                let acc_double_z = eight.clone() * acc_y_sq.clone() * acc_y.clone() * acc_z.clone();

                // choice poly in projective coordinates, identity is (0,1,0)
                let sel_x = r.clone() * x.clone(); 
                let sel_y = (one.clone() - r.clone()) + r.clone() * y.clone(); 
                let sel_z = r.clone(); 

                // X_1 = acc_next_x, Y_2 = sel_y
                // X_3 &= (X_1(-Y_2) + X_2Y_1)(Y_1(-Y_2)) - 3bZ_1Z_2) \\
                //  - (Y_1Z_2 - Y_2Z_1)(3b(X_1Z_2 + X_2Z_1)), \\
                // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) \\ 
                //  + (Y_1(-Y_2) + 3bZ_1Z_2)(Y_1(-Y_2) - 3bZ_1Z_2), \\
                // Z_3 &= (Y_1Z_2 - Y_2Z_1)(Y_1(-Y_2) + 3bZ_1Z_2) \\ 
                //  + (X_1(-Y_2) + X_2Y_1)(3X_1X_2).

            // simplified for b = 3, 
            let acc_sub_x = (acc_next_x.clone() * ( - sel_y.clone()) + sel_x.clone() * acc_next_y.clone())
                * ( acc_next_y.clone() * (- sel_y.clone()) - nine.clone() * acc_next_z.clone() * sel_z.clone())
                - ( acc_next_y.clone() * sel_z.clone() - sel_y.clone() * acc_next_z.clone())
                * ( nine.clone() * (acc_next_x.clone() * sel_z.clone()  + acc_next_z.clone() * sel_x.clone()));
            
            let acc_sub_y = (three.clone() * acc_next_x.clone() * sel_x.clone()) 
                * ( nine.clone() * ( acc_next_x.clone() * sel_z.clone() + sel_x.clone() * acc_next_z.clone()))
                + ( acc_next_y.clone() * (- sel_y.clone()) + nine.clone() * sel_z.clone() * acc_next_z.clone()) 
                * ( - sel_y.clone() * acc_next_y.clone() - nine.clone() * sel_z.clone() * acc_next_z.clone());

            let acc_sub_z = (acc_next_y.clone() * sel_z.clone() - sel_y.clone() * acc_next_z.clone())
                * (acc_next_y.clone() * (- sel_y.clone()) + nine.clone() * sel_z.clone() * acc_next_z.clone())
                + ( - acc_next_x.clone() * sel_y.clone() + sel_x.clone() * acc_next_y.clone())
                * (three.clone() * acc_next_x.clone() * sel_x.clone());

                vec![q_ec_double_add.clone() * (acc_double_z.clone() * acc_sub_x - acc_double_x.clone() * acc_sub_z.clone()),
                     q_ec_double_add.clone() * (acc_double_z.clone() * acc_sub_y - acc_double_y.clone() * acc_sub_z.clone())]

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
            println!("rbits_vec_len: {:?}", rbits_vec_len);
                for row in 0..rbits_vec_len {
                    region.assign_advice(|| "r_vec",self.witness[0], row, || inputs.rbits_vec[row])?;
                    region.assign_advice(|| "ptx_vec",self.witness[1], row, || inputs.ptx_vec[row])?;
                    region.assign_advice(|| "pty_vec",self.witness[2], row, || inputs.pty_vec[row])?;
                    region.assign_advice(|| "acc_x_vec",self.witness[3], row, || inputs.acc_x_vec[row])?;
                    region.assign_advice(|| "acc_y_vec",self.witness[4], row, || inputs.acc_y_vec[row])?;
                    region.assign_advice(|| "acc_z_vec",self.witness[5], row, || inputs.acc_z_vec[row])?;

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
        // let mut rbits_vec = rbits.iter().map(|bit| 
        //     Value::known(if *bit {Fq::ONE} else {Fq::ZERO}))
        //     .rev()
        //     .collect_vec();

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

        halo2_proofs::dev::CircuitLayout::default()
        .render(k, &circuit, &root)
        .unwrap();
    }

}