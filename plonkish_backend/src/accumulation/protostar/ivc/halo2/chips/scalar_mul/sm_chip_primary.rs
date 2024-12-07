use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{
        AccU, Advice, Column, ConstraintSystem, Constraints, Error, Expression, Selector
    },
    poly::Rotation,
};
use halo2_base::utils::BigPrimeField;
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::halo2curves::ff::BatchInvert;
use crate::{accumulation::protostar::{hyperplonk::NUM_CHALLENGE_BITS, ivc::halo2::chips::main_chip::{EcPointNative, Number}}, util::{arithmetic::{add_aff_unequal, add_proj_comp, double_proj_comp, fe_from_bits_le, fe_to_fe, into_coordinate_proj, into_coordinates, into_proj_coordinates, is_identity_proj, is_scaled_identity_proj, powers, sub_proj_comp, OverridenCurveAffine, ProjectivePoint}, end_timer, expression::pow_expr, start_timer}};
use itertools::Itertools;
use std::marker::PhantomData;

use crate::util::arithmetic::{Field, PrimeFieldBits, TwoChainCurve};

pub const NUM_ADVICE_SM: usize = 7;
pub const NUM_FIXED: usize = 1;
pub const NUM_SELECTOR: usize = 3;

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

        // | row |  r_bits   |    ptx    |   pty     |   acc.x   |   acc.y   |   acc.z   |  lambda   | 
        // | 0   |    -      |     -     |    -      |    0      |    0      |    -      |    -      |
        // | 1   |    0      |     x     |    y      |    x      |    y      |    z      |    1      | 
        // | 2   |    1      |     x     |    y      |    2x     |    2y     |    2z     |    0      |
        // | 3   |    1      |     x     |    y      |    4x     |    4y     |    4z     |    1      | 
        // | 4   |    1      |     x     |    y      |    16x    |    16y    |    16z    |    0      |
        // ...
        // | 128 |    0      |     x     |    y      |    sm.x   |    sm.y   |    sm.z   |    1      | 
        // | 129 | comm.is_0 |  comm.X   |  comm.Y   |     x3    |     y3    |     X3    |    Y3     |

        let [col_rbits, col_ptx, col_pty, col_acc_x, col_acc_y, col_acc_z, col_lambda] = 
            advices;
    
        let [q_ec_double_add, q_ec_add_unequal_last, q_ec_convert_affine] = [(); NUM_SELECTOR].map(|_| meta.selector());

            meta.create_gate("q_ec_double_add", |meta| {

                let q_ec_double_add = meta.query_selector(q_ec_double_add);
                let acc_prev_x = meta.query_advice(col_acc_x, Rotation(0));
                let acc_prev_y = meta.query_advice(col_acc_y, Rotation(0));
                let acc_prev_z = meta.query_advice(col_acc_z, Rotation(0));

                let x = meta.query_advice(col_ptx, Rotation(1));
                let y = meta.query_advice(col_pty, Rotation(1));
                let r = meta.query_advice(col_rbits, Rotation(1));
                let lambda = meta.query_advice(col_lambda, Rotation(1));

                let acc_next_x = meta.query_advice(col_acc_x, Rotation(1));
                let acc_next_y = meta.query_advice(col_acc_y, Rotation(1));
                let acc_next_z = meta.query_advice(col_acc_z, Rotation(1));
                let acc_prev_x_sq = acc_prev_x.clone() * acc_prev_x.clone();
                let acc_prev_y_sq = acc_prev_y.clone() * acc_prev_y.clone();
                let acc_prev_z_sq = acc_prev_z.clone() * acc_prev_z.clone();

                let zero = Expression::Constant(C::Scalar::ZERO);
                let one = Expression::Constant(C::Scalar::ONE);
                let two = Expression::Constant(C::Scalar::from(2));
                let three = Expression::Constant(C::Scalar::from(3));
                let nine = Expression::Constant(C::Scalar::from(9));
                let eight = Expression::Constant(C::Scalar::from(8));
                let twenty_four = Expression::Constant(C::Scalar::from(24));
                let twenty_seven = Expression::Constant(C::Scalar::from(27)); // nine * b
                let seventy_two = Expression::Constant(C::Scalar::from(72)); // twenty_four * b
                let u = Expression::AccU(AccU{index: 0});

                // pt double, b = 3 for bn254, degree 4
                //  x' = 2xy(y^2 - 9bz^2)
                //  y' = (y^2 - 9bz^2)(y^2 + 3bz^2) + 24*b*y^2*z^2 
                //  z' = 8y^3*z

                // simplified for b = 3, 
                let acc_double_x = two * acc_prev_x.clone() * acc_prev_y.clone() * (acc_prev_y_sq.clone() - twenty_seven.clone() * acc_prev_z_sq.clone());
                let acc_double_y = (acc_prev_y_sq.clone() - twenty_seven.clone() * acc_prev_z_sq.clone()) 
                                 * (acc_prev_y_sq.clone() + nine.clone() * acc_prev_z_sq.clone()) + seventy_two.clone() * acc_prev_y_sq.clone() * acc_prev_z_sq.clone();
                let acc_double_z = eight.clone() * acc_prev_y_sq.clone() * acc_prev_y.clone() * acc_prev_z.clone();

                // choice poly in projective coordinates, identity is (0,1,0), two choices so degree 2
                let sel_x = r.clone() * x.clone(); 
                let sel_y = (one.clone() * u.clone() - r.clone()) * u.clone() + r.clone() * y.clone(); 
                let sel_z = r.clone() * u.clone(); 

                // X_1 = acc_next_x, Y_2 = sel_y
                // X_3 &= (X_1(-Y_2) + X_2Y_1)(Y_1(-Y_2)) - 3bZ_1Z_2) \\ x1y1
                //  - (Y_1Z_2 - Y_2Z_1)(3b(X_1Z_2 + X_2Z_1)), \\
                // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) \\ y1^2
                //  + (Y_1(-Y_2) + 3bZ_1Z_2)(Y_1(-Y_2) - 3bZ_1Z_2), \\
                // Z_3 &= (Y_1Z_2 - Y_2Z_1)(Y_1(-Y_2) + 3bZ_1Z_2) \\ z1y1
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

                vec![q_ec_double_add.clone() * (acc_sub_x - lambda.clone() * acc_double_x.clone() * u.clone()),
                     q_ec_double_add.clone() * (acc_sub_y - lambda.clone() * acc_double_y.clone() * u.clone()),
                     q_ec_double_add.clone() * (acc_sub_z - lambda.clone() * acc_double_z.clone() * u.clone())]

            });

            meta.create_gate("ec_add_unequal_last", |meta| {

                let q_ec_add_unequal_last = meta.query_selector(q_ec_add_unequal_last);
                let one = Expression::Constant(C::Scalar::ONE);
                let comm_x = meta.query_advice(col_ptx, Rotation(0));
                let comm_y = meta.query_advice(col_pty, Rotation(0));
                let comm_sel_bit = meta.query_advice(col_rbits, Rotation(0));
                let sm_x = meta.query_advice(col_acc_x, Rotation(0));
                let sm_y = meta.query_advice(col_acc_y, Rotation(0));
                let x3 = meta.query_advice(col_acc_z, Rotation(0));
                let y3 = meta.query_advice(col_lambda, Rotation(0));
                let u = Expression::AccU(AccU{index: 0});

                // dx = x2 - x1
                let dx = sm_x.clone() - comm_x.clone();
                let dy = sm_y.clone() - comm_y.clone();
                let dx_sq = dx.clone() * dx.clone();
                let dy_sq = dy.clone() * dy.clone();

                //  x_3 * dx_sq = dy_sq - x_1 * dx_sq - x_2 * dx_sq, degree 3
                //  y_3 * dx = dy * (x_1 - x_3) - y_1 * dx, degree 2

            vec![q_ec_add_unequal_last.clone() * (((x3.clone() * dx_sq.clone() - dy_sq.clone() * u.clone() + comm_x.clone() * dx_sq.clone() + sm_x.clone() * dx_sq.clone()) * comm_sel_bit.clone()) * pow_expr(u.clone(), 2) + ((one.clone() * u.clone() - comm_sel_bit.clone()) * (x3.clone() - sm_x.clone()))*pow_expr(u.clone(), 4)),
                 q_ec_add_unequal_last * (((y3.clone() * dx.clone() - dy.clone() * (comm_x.clone() - x3.clone()) + comm_y.clone() * dx.clone()) * comm_sel_bit.clone()) * pow_expr(u.clone(), 3) + ((one.clone() * u.clone() - comm_sel_bit.clone()) * (y3.clone() - sm_y.clone()))*pow_expr(u.clone(), 4))]
            });

            meta.create_gate("ec_convert_affine", |meta| {

                let q_ec_convert_affine = meta.query_selector(q_ec_convert_affine);
                let sm_x = meta.query_advice(col_acc_x, Rotation(-1));
                let sm_y = meta.query_advice(col_acc_y, Rotation(-1));
                let sm_z = meta.query_advice(col_acc_z, Rotation(-1));

                let u = Expression::AccU(AccU{index: 0});
                let x3_aff = meta.query_advice(col_acc_x, Rotation(0));
                let y3_aff = meta.query_advice(col_acc_y, Rotation(0));

                Constraints::with_selector(
                    q_ec_convert_affine,
                    [
                        (
                            "Constrain affine_x conversion",
                            (sm_z.clone() * x3_aff - sm_x.clone() * u.clone()) * pow_expr(u.clone(), 4),
                        ),
                        (
                            "Constrain affine_y conversion",
                            (sm_z.clone() * y3_aff - sm_y.clone() * u.clone()) * pow_expr(u.clone(), 4),
                        )
                    ],
                )
            });

        Self { 
            witness: [col_rbits, col_ptx, col_pty, col_acc_x, col_acc_y, col_acc_z, col_lambda], 
            selector: [q_ec_double_add, q_ec_add_unequal_last, q_ec_convert_affine],
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

            // | row |  r_bits   |    ptx    |   pty     |   acc.x   |   acc.y   |   acc.z   |  lambda   | 
            // | 0   |    -      |     -     |    -      |    0      |    1      |    0      |    1      |
            // | 1   |    0      |     x     |    y      |    x      |    y      |    z      |    1      | 
            // | 2   |    1      |     x     |    y      |    2x     |    2y     |    2z     |    0      |
            // | 3   |    1      |     x     |    y      |    4x     |    4y     |    4z     |    1      | 
            // | 4   |    1      |     x     |    y      |    16x    |    16y    |    16z    |    0      |
            // ...
            // | 128 |    1      |     x     |    y      |   sm.x    |   sm.y    |    sm.z   |   z3_inv  | 
            // | 129 |    z3     |   acc.x   |   acc.y   |    x3     |    y3     |    X3     |    Y3     |

                for row in 0..NUM_CHALLENGE_BITS + 2 { 
                    if row != NUM_CHALLENGE_BITS + 1 {
                        if row != 0 {
                            region.assign_advice(|| "r_vec",self.witness[0], row, || inputs.rbits_vec[row - 1])?;
                            region.assign_advice(|| "ptx_vec",self.witness[1], row, || inputs.ptx_vec[row - 1])?;
                            region.assign_advice(|| "pty_vec",self.witness[2], row, || inputs.pty_vec[row - 1])?;
                            region.assign_advice(|| "lambda_vec",self.witness[6], row, || inputs.lambda_vec[row - 1])?;

                        }

                        region.assign_advice(|| "acc_x_vec",self.witness[3], row, || inputs.acc_x_vec[row])?;
                        region.assign_advice(|| "acc_y_vec",self.witness[4], row, || inputs.acc_y_vec[row])?;
                        region.assign_advice(|| "acc_z_vec",self.witness[5], row, || inputs.acc_z_vec[row])?;
                    }

                    if row < NUM_CHALLENGE_BITS {
                        self.selector[0].enable(&mut region, row)?;
                    } 

                    if row == NUM_CHALLENGE_BITS + 1 {
                        self.selector[1].enable(&mut region, row)?;
                        self.selector[2].enable(&mut region, row)?;
                            region.assign_advice(|| "comm_is_zero",self.witness[0], row, || inputs.comm_is_zero)?;
                            region.assign_advice(|| "comm_X",self.witness[1], row, || inputs.comm_X)?;
                            region.assign_advice(|| "comm_Y",self.witness[2], row, || inputs.comm_Y)?;
                            region.assign_advice(|| "sm_X",self.witness[3], row, || inputs.sm_X)?;
                            region.assign_advice(|| "sm_Y",self.witness[4], row, || inputs.sm_Y)?;
                            region.assign_advice(|| "X3",self.witness[5], row, || inputs.X3)?;
                            region.assign_advice(|| "Y3",self.witness[6], row, || inputs.Y3)?;

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
    pub lambda_vec: Vec<Value<C::Scalar>>,
    pub comm_is_zero: Value<C::Scalar>,
    pub comm_X: Value<C::Scalar>,
    pub comm_Y: Value<C::Scalar>,
    pub sm_X: Value<C::Scalar>,
    pub sm_Y: Value<C::Scalar>,
    pub X3: Value<C::Scalar>,
    pub Y3: Value<C::Scalar>,
}

#[derive(Clone)]
pub struct ScalarMulChip<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{ 
    pub config: ScalarMulChipConfig<C>,
    // pub is_primary: Value<C::Scalar>,
    // pub inputs: Vec<ScalarMulConfigInputs<C>> 
}

impl<C> ScalarMulChip<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub fn new(config: ScalarMulChipConfig<C>) -> Self {
        Self { config }
    }

    pub fn get_outputs_raw(
        r_le_bits: Vec<C::Scalar>,
        nark_comm: &[C::Scalar; 2],
        acc_comm: &[C::Scalar; 2],
    ) -> Result<ScalarMulConfigInputs<C>, Error> {

        let scalar_bits = NUM_CHALLENGE_BITS;

            let rbits_rev_fe = r_le_bits.iter().rev().cloned().collect_vec();
            let rbits_rev = rbits_rev_fe.iter().map( |fe| *fe == C::Scalar::ONE ).collect_vec();

            let rbits_vec = rbits_rev_fe.iter().map(|fe| Value::known(*fe)).collect_vec();
            let zero = ProjectivePoint {
                x: C::Scalar::ZERO,
                y: C::Scalar::ONE,
                z: C::Scalar::ZERO,
            };
            
            let p_single_x = nark_comm[0];
            let p_single_y = nark_comm[1];

            let p = C::Secondary::from_xy(p_single_x, p_single_y).unwrap();
            let mut ptx_vec = Vec::new();
            let mut pty_vec = Vec::new();
            for i in 0..scalar_bits {
                ptx_vec.push(Value::known(p_single_x));
                pty_vec.push(Value::known(p_single_y));
            }

            let acc_comm_x = acc_comm[0];
            let acc_comm_y = acc_comm[1];
            let comm_is_zero_bool = acc_comm_x == C::Scalar::ZERO && acc_comm_y == C::Scalar::ZERO;
            let comm_is_zero = if comm_is_zero_bool { C::Scalar::ONE } else { C::Scalar::ZERO };

            let mut acc_prev = ProjectivePoint::identity();
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
                    ProjectivePoint::new(p_single_x, p_single_y, C::Scalar::ONE)
                } else { zero };
                
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

            for i in 0..scalar_bits {
                let acc_prev_proj = ProjectivePoint::new(acc_prev_xvec[i+1], acc_prev_yvec[i+1], acc_prev_zvec[i+1]);
                let lhs_double_proj = ProjectivePoint::new(lhs_double_xvec[i], lhs_double_yvec[i], lhs_double_zvec[i]);
                let p_single_proj = if rbits_rev[i] { 
                    ProjectivePoint::new(p_single_x, p_single_y, C::Scalar::ONE)
                } else { zero };
    
                let rhs = sub_proj_comp(acc_prev_proj, p_single_proj);
                if is_identity_proj(rhs) && is_identity_proj(lhs_double_proj) {
                    lhs_zvec.push(C::Scalar::ONE);
                    rhs_zvec.push(C::Scalar::ONE);
                } else if is_identity_proj(rhs) && is_scaled_identity_proj(lhs_double_proj) {
                    lhs_zvec.push(lhs_double_proj.y);
                    rhs_zvec.push(C::Scalar::ONE);
                } else if is_identity_proj(lhs_double_proj) && is_scaled_identity_proj(rhs) {
                    lhs_zvec.push(C::Scalar::ONE);
                    rhs_zvec.push(rhs.y);
                } else {
                    lhs_zvec.push(lhs_double_zvec[i]);
                    rhs_zvec.push(rhs.z);
                }
            }

            lhs_zvec.batch_invert();            
            let lambda_vec = lhs_zvec.iter().zip(rhs_zvec).map(|(lhs, rhs)| Value::known(*lhs*rhs)).collect();        
            let scalar_mul_calc = ProjectivePoint::<C::Scalar>::new(*acc_prev_xvec.last().unwrap(), *acc_prev_yvec.last().unwrap(), *acc_prev_zvec.last().unwrap());
            let scalar_mul_calc_affine = scalar_mul_calc.to_affine();

            let acc_prime  = if comm_is_zero_bool {
                scalar_mul_calc_affine
            } else {
                add_aff_unequal(scalar_mul_calc_affine, (acc_comm_x, acc_comm_y))
            };
            
            let acc_x_vec = acc_prev_xvec.iter().map(|fe| Value::known(*fe)).collect();
            let acc_y_vec = acc_prev_yvec.iter().map(|fe| Value::known(*fe)).collect();
            let acc_z_vec = acc_prev_zvec.iter().map(|fe| Value::known(*fe)).collect();

            let inputs =
                ScalarMulConfigInputs::<C> { 
                    rbits_vec, 
                    ptx_vec,
                    pty_vec,
                    acc_x_vec, 
                    acc_y_vec, 
                    acc_z_vec,
                    lambda_vec, 
                    comm_is_zero: Value::known(comm_is_zero),
                    comm_X: Value::known(acc_comm_x),
                    comm_Y: Value::known(acc_comm_y),
                    sm_X: Value::known(scalar_mul_calc_affine.0),
                    sm_Y: Value::known(scalar_mul_calc_affine.1),
                    X3: Value::known(acc_prime.0),
                    Y3: Value::known(acc_prime.1),
                };  
        Ok(inputs)
    }

    pub fn preprocess_inputs(
        &self,
        r_le_bits: Vec<Number<C::Scalar>>,
        nark_comm: &EcPointNative<C>,
        acc_comm: &EcPointNative<C>,
    ) -> Result<ScalarMulConfigInputs<C>, Error> {

        let mut rbits_fe = Vec::new();
        r_le_bits.iter().for_each(|fe| {
            rbits_fe.push(fe.value());
        });

        let scalar_bits = NUM_CHALLENGE_BITS;

            let rbits_rev_fe = rbits_fe.iter().rev().cloned().collect_vec();
            let rbits_rev = rbits_rev_fe.iter().map( |fe| *fe == C::Scalar::ONE ).collect_vec();

            let rbits_vec = rbits_rev_fe.iter().map(|fe| Value::known(*fe)).collect_vec();
            let zero = ProjectivePoint {
                x: C::Scalar::ZERO,
                y: C::Scalar::ONE,
                z: C::Scalar::ZERO,
            };
            
            let p_single_x = nark_comm.x.value();
            let p_single_y = nark_comm.y.value();

            let p = C::Secondary::from_xy(p_single_x, p_single_y).unwrap();
            let mut ptx_vec = Vec::new();
            let mut pty_vec = Vec::new();
            for i in 0..scalar_bits {
                ptx_vec.push(Value::known(p_single_x));
                pty_vec.push(Value::known(p_single_y));
            }

            let acc_comm_x = acc_comm.x.value();
            let acc_comm_y = acc_comm.y.value();
            let comm_is_zero_bool = acc_comm_x == C::Scalar::ZERO && acc_comm_y == C::Scalar::ZERO;
            let comm_is_zero = if comm_is_zero_bool { C::Scalar::ONE } else { C::Scalar::ZERO };

            let mut acc_prev = ProjectivePoint::identity();
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
                    ProjectivePoint::new(p_single_x, p_single_y, C::Scalar::ONE)
                } else { zero };
                
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

            for i in 0..scalar_bits {
                let acc_prev_proj = ProjectivePoint::new(acc_prev_xvec[i+1], acc_prev_yvec[i+1], acc_prev_zvec[i+1]);
                let lhs_double_proj = ProjectivePoint::new(lhs_double_xvec[i], lhs_double_yvec[i], lhs_double_zvec[i]);
                let p_single_proj = if rbits_rev[i] { 
                    ProjectivePoint::new(p_single_x, p_single_y, C::Scalar::ONE)
                } else { zero };
    
                let rhs = sub_proj_comp(acc_prev_proj, p_single_proj);
                if is_identity_proj(rhs) && is_identity_proj(lhs_double_proj) {
                    lhs_zvec.push(C::Scalar::ONE);
                    rhs_zvec.push(C::Scalar::ONE);
                } else if is_identity_proj(rhs) && is_scaled_identity_proj(lhs_double_proj) {
                    lhs_zvec.push(lhs_double_proj.y);
                    rhs_zvec.push(C::Scalar::ONE);
                } else if is_identity_proj(lhs_double_proj) && is_scaled_identity_proj(rhs) {
                    lhs_zvec.push(C::Scalar::ONE);
                    rhs_zvec.push(rhs.y);
                } else {
                    lhs_zvec.push(lhs_double_zvec[i]);
                    rhs_zvec.push(rhs.z);
                }
            }

            lhs_zvec.batch_invert();            
            let lambda_vec = lhs_zvec.iter().zip(rhs_zvec).map(|(lhs, rhs)| Value::known(*lhs*rhs)).collect();        
            let scalar_mul_calc = ProjectivePoint::<C::Scalar>::new(*acc_prev_xvec.last().unwrap(), *acc_prev_yvec.last().unwrap(), *acc_prev_zvec.last().unwrap());
            let scalar_mul_calc_affine = scalar_mul_calc.to_affine();

            let acc_prime  = if comm_is_zero_bool {
                scalar_mul_calc_affine
            } else {
                add_aff_unequal(scalar_mul_calc_affine, (acc_comm_x, acc_comm_y))
            };
            
            let acc_x_vec = acc_prev_xvec.iter().map(|fe| Value::known(*fe)).collect();
            let acc_y_vec = acc_prev_yvec.iter().map(|fe| Value::known(*fe)).collect();
            let acc_z_vec = acc_prev_zvec.iter().map(|fe| Value::known(*fe)).collect();

            let inputs =
                ScalarMulConfigInputs::<C> { 
                    rbits_vec, 
                    ptx_vec,
                    pty_vec,
                    acc_x_vec, 
                    acc_y_vec, 
                    acc_z_vec,
                    lambda_vec, 
                    comm_is_zero: Value::known(comm_is_zero),
                    comm_X: Value::known(acc_comm_x),
                    comm_Y: Value::known(acc_comm_y),
                    sm_X: Value::known(scalar_mul_calc_affine.0),
                    sm_Y: Value::known(scalar_mul_calc_affine.1),
                    X3: Value::known(acc_prime.0),
                    Y3: Value::known(acc_prime.1),
                };  
        Ok(inputs)
    }

    pub fn preprocess_inputs_raw(
        &self,
        r_le_bits: Vec<C::Scalar>,
        nark_comm: &[C::Scalar; 2],
        acc_comm: &[C::Scalar; 2],
    ) -> Result<ScalarMulConfigInputs<C>, Error> {

        let scalar_bits = NUM_CHALLENGE_BITS;

            let rbits_rev_fe = r_le_bits.iter().rev().cloned().collect_vec();
            let rbits_rev = rbits_rev_fe.iter().map( |fe| *fe == C::Scalar::ONE ).collect_vec();

            let rbits_vec = rbits_rev_fe.iter().map(|fe| Value::known(*fe)).collect_vec();
            let zero = ProjectivePoint {
                x: C::Scalar::ZERO,
                y: C::Scalar::ONE,
                z: C::Scalar::ZERO,
            };
            
            let p_single_x = nark_comm[0];
            let p_single_y = nark_comm[1];

            let p = C::Secondary::from_xy(p_single_x, p_single_y).unwrap();
            let mut ptx_vec = Vec::new();
            let mut pty_vec = Vec::new();
            for i in 0..scalar_bits {
                ptx_vec.push(Value::known(p_single_x));
                pty_vec.push(Value::known(p_single_y));
            }

            let acc_comm_x = acc_comm[0];
            let acc_comm_y = acc_comm[1];
            let comm_is_zero_bool = acc_comm_x == C::Scalar::ZERO && acc_comm_y == C::Scalar::ZERO;
            let comm_is_zero = if comm_is_zero_bool { C::Scalar::ONE } else { C::Scalar::ZERO };

            let mut acc_prev = ProjectivePoint::identity();
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
                    ProjectivePoint::new(p_single_x, p_single_y, C::Scalar::ONE)
                } else { zero };
                
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

            for i in 0..scalar_bits {
                let acc_prev_proj = ProjectivePoint::new(acc_prev_xvec[i+1], acc_prev_yvec[i+1], acc_prev_zvec[i+1]);
                let lhs_double_proj = ProjectivePoint::new(lhs_double_xvec[i], lhs_double_yvec[i], lhs_double_zvec[i]);
                let p_single_proj = if rbits_rev[i] { 
                    ProjectivePoint::new(p_single_x, p_single_y, C::Scalar::ONE)
                } else { zero };
    
                let rhs = sub_proj_comp(acc_prev_proj, p_single_proj);
                if is_identity_proj(rhs) && is_identity_proj(lhs_double_proj) {
                    lhs_zvec.push(C::Scalar::ONE);
                    rhs_zvec.push(C::Scalar::ONE);
                } else if is_identity_proj(rhs) && is_scaled_identity_proj(lhs_double_proj) {
                    lhs_zvec.push(lhs_double_proj.y);
                    rhs_zvec.push(C::Scalar::ONE);
                } else if is_identity_proj(lhs_double_proj) && is_scaled_identity_proj(rhs) {
                    lhs_zvec.push(C::Scalar::ONE);
                    rhs_zvec.push(rhs.y);
                } else {
                    lhs_zvec.push(lhs_double_zvec[i]);
                    rhs_zvec.push(rhs.z);
                }
            }

            lhs_zvec.batch_invert();            
            let lambda_vec = lhs_zvec.iter().zip(rhs_zvec).map(|(lhs, rhs)| Value::known(*lhs*rhs)).collect();        
            let scalar_mul_calc = ProjectivePoint::<C::Scalar>::new(*acc_prev_xvec.last().unwrap(), *acc_prev_yvec.last().unwrap(), *acc_prev_zvec.last().unwrap());
            let scalar_mul_calc_affine = scalar_mul_calc.to_affine();

            let acc_prime  = if comm_is_zero_bool {
                scalar_mul_calc_affine
            } else {
                add_aff_unequal(scalar_mul_calc_affine, (acc_comm_x, acc_comm_y))
            };
            
            let acc_x_vec = acc_prev_xvec.iter().map(|fe| Value::known(*fe)).collect();
            let acc_y_vec = acc_prev_yvec.iter().map(|fe| Value::known(*fe)).collect();
            let acc_z_vec = acc_prev_zvec.iter().map(|fe| Value::known(*fe)).collect();

            let inputs =
                ScalarMulConfigInputs::<C> { 
                    rbits_vec, 
                    ptx_vec,
                    pty_vec,
                    acc_x_vec, 
                    acc_y_vec, 
                    acc_z_vec,
                    lambda_vec, 
                    comm_is_zero: Value::known(comm_is_zero),
                    comm_X: Value::known(acc_comm_x),
                    comm_Y: Value::known(acc_comm_y),
                    sm_X: Value::known(scalar_mul_calc_affine.0),
                    sm_Y: Value::known(scalar_mul_calc_affine.1),
                    X3: Value::known(acc_prime.0),
                    Y3: Value::known(acc_prime.1),
                };  
        Ok(inputs)
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        rbits_fe: Vec<Number<C::Scalar>>,
        nark_comm: &EcPointNative<C>,
        acc_comm: &EcPointNative<C>,
    ) -> Result<EcPointNative<C>, Error> {

        let inputs = self.preprocess_inputs(rbits_fe, nark_comm, acc_comm)?;

        let mut acc_prime_x = Vec::new();
        let mut acc_prime_y = Vec::new();

        layouter.assign_region(
            || "ScalarMulChipConfig assign",
            |mut region| {

            // | row |  r_bits   |    ptx    |   pty     |   acc.x   |   acc.y   |   acc.z   |  lambda   | 
            // | 0   |    -      |     -     |    -      |    0      |    1      |    0      |    -      |
            // | 1   |    0      |     x     |    y      |    x      |    y      |    z      |    1      | 
            // | 2   |    1      |     x     |    y      |    2x     |    2y     |    2z     |    0      |
            // | 3   |    1      |     x     |    y      |    4x     |    4y     |    4z     |    1      | 
            // | 4   |    1      |     x     |    y      |    16x    |    16y    |    16z    |    0      |
            // ...
            // | 128 |    1      |     x     |    y      |   sm.x    |   sm.y    |    sm.z   |    1      | 
            // | 129 |    -      |   acc.x   |   acc.y   |   r.x/z   |   r.y/z   |    -      |    -      |

            let ptx = region.assign_advice(|| "ptx_vec",self.config.witness[1], 1, || inputs.ptx_vec[0])?;
            let pty = region.assign_advice(|| "pty_vec",self.config.witness[2], 1, || inputs.pty_vec[0])?;

                for row in 0..NUM_CHALLENGE_BITS + 2 { 
                    if row != NUM_CHALLENGE_BITS + 1 {
                        if row != 0 {
                            region.assign_advice(|| "r_vec",self.config.witness[0], row, || inputs.rbits_vec[row - 1])?;
                            region.assign_advice(|| "lambda_vec",self.config.witness[6], row, || inputs.lambda_vec[row - 1])?;

                            if row != 1 {
                                ptx.copy_advice(|| "ptx_vec", &mut region, self.config.witness[1], row)?;
                                pty.copy_advice(|| "pty_vec", &mut region, self.config.witness[2], row)?;
                            }
                        }
                        
                        region.assign_advice(|| "acc_x_vec",self.config.witness[3], row, || inputs.acc_x_vec[row])?;
                        region.assign_advice(|| "acc_y_vec",self.config.witness[4], row, || inputs.acc_y_vec[row])?;
                        region.assign_advice(|| "acc_z_vec",self.config.witness[5], row, || inputs.acc_z_vec[row])?;
                    }

                    if row < NUM_CHALLENGE_BITS {
                        self.config.selector[0].enable(&mut region, row)?;
                    } 

                    if row == NUM_CHALLENGE_BITS + 1 {
                        self.config.selector[1].enable(&mut region, row)?;
                        self.config.selector[2].enable(&mut region, row)?;
                            region.assign_advice(|| "comm_is_zero",self.config.witness[0], row, || inputs.comm_is_zero)?;
                            region.assign_advice(|| "comm_X",self.config.witness[1], row, || inputs.comm_X)?;
                            region.assign_advice(|| "comm_Y",self.config.witness[2], row, || inputs.comm_Y)?;
                            region.assign_advice(|| "sm_X",self.config.witness[3], row, || inputs.sm_X)?;
                            region.assign_advice(|| "sm_Y",self.config.witness[4], row, || inputs.sm_Y)?;
                            acc_prime_x.push(region.assign_advice(|| "X3",self.config.witness[5], row, || inputs.X3)?);
                            acc_prime_y.push(region.assign_advice(|| "Y3",self.config.witness[6], row, || inputs.Y3)?);

                    }
                }         
                // todo check this, giving none            
                Ok(EcPointNative::new(Number(acc_prime_x.last().unwrap().clone()), Number(acc_prime_y.last().unwrap().clone())))
            },
        )
    }

    pub fn assign_raw(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        rbits_fe: Vec<C::Scalar>,
        nark_comm: &[C::Scalar; 2],
        acc_comm: &[C::Scalar; 2],
    ) -> Result<(Number<C::Scalar>, Number<C::Scalar>), Error> {

        let inputs = self.preprocess_inputs_raw(rbits_fe, nark_comm, acc_comm)?;

        let mut acc_prime_x = Vec::new();
        let mut acc_prime_y = Vec::new();

        layouter.assign_region(
            || "ScalarMulChipConfig assign",
            |mut region| {

            // | row |  r_bits   |    ptx    |   pty     |   acc.x   |   acc.y   |   acc.z   |  lambda   | 
            // | 0   |    -      |     -     |    -      |    0      |    1      |    0      |    -      |
            // | 1   |    0      |     x     |    y      |    x      |    y      |    z      |    1      | 
            // | 2   |    1      |     x     |    y      |    2x     |    2y     |    2z     |    0      |
            // | 3   |    1      |     x     |    y      |    4x     |    4y     |    4z     |    1      | 
            // | 4   |    1      |     x     |    y      |    16x    |    16y    |    16z    |    0      |
            // ...
            // | 128 |    1      |     x     |    y      |   sm.x    |   sm.y    |    sm.z   |    1      | 
            // | 129 |    -      |   acc.x   |   acc.y   |   r.x/z   |   r.y/z   |    -      |    -      |

            let ptx = region.assign_advice(|| "ptx_vec",self.config.witness[1], 1, || inputs.ptx_vec[0])?;
            let pty = region.assign_advice(|| "pty_vec",self.config.witness[2], 1, || inputs.pty_vec[0])?;

                for row in 0..NUM_CHALLENGE_BITS + 2 { 
                    if row != NUM_CHALLENGE_BITS + 1 {
                        if row != 0 {
                            region.assign_advice(|| "r_vec",self.config.witness[0], row, || inputs.rbits_vec[row - 1])?;
                            region.assign_advice(|| "lambda_vec",self.config.witness[6], row, || inputs.lambda_vec[row - 1])?;

                            if row != 1 {
                                ptx.copy_advice(|| "ptx_vec", &mut region, self.config.witness[1], row)?;
                                pty.copy_advice(|| "pty_vec", &mut region, self.config.witness[2], row)?;
                            }
                        }
                        
                        region.assign_advice(|| "acc_x_vec",self.config.witness[3], row, || inputs.acc_x_vec[row])?;
                        region.assign_advice(|| "acc_y_vec",self.config.witness[4], row, || inputs.acc_y_vec[row])?;
                        region.assign_advice(|| "acc_z_vec",self.config.witness[5], row, || inputs.acc_z_vec[row])?;
                    }

                    if row < NUM_CHALLENGE_BITS {
                        self.config.selector[0].enable(&mut region, row)?;
                    } 

                    if row == NUM_CHALLENGE_BITS + 1 {
                        self.config.selector[1].enable(&mut region, row)?;
                        self.config.selector[2].enable(&mut region, row)?;
                            region.assign_advice(|| "comm_is_zero",self.config.witness[0], row, || inputs.comm_is_zero)?;
                            region.assign_advice(|| "comm_X",self.config.witness[1], row, || inputs.comm_X)?;
                            region.assign_advice(|| "comm_Y",self.config.witness[2], row, || inputs.comm_Y)?;
                            region.assign_advice(|| "sm_X",self.config.witness[3], row, || inputs.sm_X)?;
                            region.assign_advice(|| "sm_Y",self.config.witness[4], row, || inputs.sm_Y)?;
                            acc_prime_x.push(region.assign_advice(|| "X3",self.config.witness[5], row, || inputs.X3)?);
                            acc_prime_y.push(region.assign_advice(|| "Y3",self.config.witness[6], row, || inputs.Y3)?);

                    }
                }         
                // todo check this, giving none            
                Ok((Number(acc_prime_x.last().unwrap().clone()), Number(acc_prime_y.last().unwrap().clone())))
            },
        )
    }
}
