use crate::accumulation::protostar::{
    hyperplonk::NUM_CHALLENGE_BITS, ivc::halo2::ivc_circuits::primary::T,
};

use halo2_proofs::{
        circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
        halo2curves::{
            bn256::{G1Affine, G2Affine, G1},
            grumpkin::{self, Fr as Fq},
        },
        plonk::{
            AccU, Advice, Assigned, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Fixed, Instance, Selector
        },
        poly::Rotation,
};
use halo2_base::utils::{BigPrimeField, CurveAffineExt, ScalarField};
use halo2_proofs::halo2curves::{group::Group, grumpkin::Fr, Coordinates, CurveAffine};
use itertools::Itertools;
use poseidon2::circuit::hash_chip::NUM_PARTIAL_SBOX;
use std::{
    iter,
    marker::PhantomData,
    sync::{RwLock, RwLockReadGuard},
};

use crate::util::arithmetic::{Field, PrimeFieldBits, TwoChainCurve};
pub const NUM_IO: usize = 5;
pub const NUM_ADVICE_SM: usize = 8;
pub const NUM_FIXED_SM: usize = 1;
pub const NUM_INSTANCE_SM: usize = 1;
pub const NUM_SELECTOR_SM: usize = 4;

#[derive(Clone, Debug)]
pub struct ScalarMulChipConfig<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    witness: [Column<Advice>; NUM_ADVICE_SM],
    fixed: [Column<Fixed>; NUM_FIXED_SM],
    selector: [Selector; NUM_SELECTOR_SM],
    _marker: PhantomData<C>,
}

impl<C> ScalarMulChipConfig<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    //todo might not need to constraint sum of rbits to r_given -- this is alreadey done by the primary verifier when converting challenge to bits
    pub fn configure(
        meta: &mut ConstraintSystem<C::Scalar>,
        advices: [Column<Advice>; NUM_ADVICE_SM],
        fixed: [Column<Fixed>; NUM_FIXED_SM],
    ) -> Self {
        // | row |  r_bits   |    e2     |    lc     |    ptx    |   pty     |   acc.x   |   acc.y   |   acc.z   |  lambda   |
        // | 0   |    -      |    -      |    -      |     -     |    -      |    0      |    0      |           |           |
        // | 1   |    0      |    1      |    0      |     x     |    y      |    x      |    y      |    z      |    1      |
        // | 2   |    1      |    2      |    2      |     x     |    y      |    2x     |    2y     |    2z     |    0      |
        // | 3   |    1      |    4      |    4      |     x     |    y      |    4x     |    4y     |    4z     |    1      |
        // | 4   |    0      |    8      |    6      |     x     |    y      |    16x    |    16y    |    16z    |    0      |
        // ...
        // | 128 |    1      |   2^127   |    1      |     x     |    y      |    sm.x   |    sm.y   |    sm.z   |    1      |
        // | 129 |  comm_sel |   2^128   |    r      |  comm_x   |  comm_y   |    sm.X   |    sm.Y   |     X3    |    Y3     |

        let col_re2 = fixed[0];
        let [q_ec_double_add, q_ec_add_unequal_last, q_ec_convert_affine, q_ec_num] =
            [(); NUM_SELECTOR_SM].map(|_| meta.selector());
        let [col_rbits, col_rlc, col_ptx, col_pty, col_acc_x, col_acc_y, col_acc_z, col_lambda] =
            advices;

        let pow4 = |x: Expression<C::Scalar>| {
            let x_sq = x.clone() * x.clone();
            x_sq.clone() * x_sq
        };

        meta.create_gate("q_ec_double_add", |meta| {
            let q_ec_double_add = meta.query_selector(q_ec_double_add);
            let acc_prev_x = meta.query_advice(col_acc_x, Rotation(-1));
            let acc_prev_y = meta.query_advice(col_acc_y, Rotation(-1));
            let acc_prev_z = meta.query_advice(col_acc_z, Rotation(-1));

            let x = meta.query_advice(col_ptx, Rotation(0));
            let y = meta.query_advice(col_pty, Rotation(0));
            let r = meta.query_advice(col_rbits, Rotation(0));
            let lambda = meta.query_advice(col_lambda, Rotation(0));

            let acc_next_x = meta.query_advice(col_acc_x, Rotation(0));
            let acc_next_y = meta.query_advice(col_acc_y, Rotation(0));
            let acc_next_z = meta.query_advice(col_acc_z, Rotation(0));
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

            // pt double, b = 3 for bn254
            //  x' = 2xy(y^2 - 9bz^2)
            //  y' = (y^2 - 9bz^2)(y^2 + 3bz^2) + 24*b*y^2*z^2
            //  z' = 8y^3*z

            // simplified for b = 3,
            let acc_double_x = two * acc_prev_x.clone() * acc_prev_y.clone() * (acc_prev_y_sq.clone() - twenty_seven.clone() * acc_prev_z_sq.clone());
            let acc_double_y = (acc_prev_y_sq.clone() - twenty_seven.clone() * acc_prev_z_sq.clone())
                             * (acc_prev_y_sq.clone() + nine.clone() * acc_prev_z_sq.clone()) + seventy_two.clone() * acc_prev_y_sq.clone() * acc_prev_z_sq.clone();
            let acc_double_z = eight.clone() * acc_prev_y_sq.clone() * acc_prev_y.clone() * acc_prev_z.clone();

            // choice poly in projective coordinates, identity is (0,1,0)
            let sel_x = r.clone() * x.clone();
            let sel_y = (one.clone() - r.clone()) + r.clone() * y.clone();
            let sel_z = r.clone();

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

            vec![q_ec_double_add.clone() * (acc_sub_x - lambda.clone() * acc_double_x.clone()),
                 q_ec_double_add.clone() * (acc_sub_y - lambda.clone() * acc_double_y.clone()),
                 q_ec_double_add.clone() * (acc_sub_z - lambda.clone() * acc_double_z.clone())]

        });

        //todo need to constrain that comm_x != sm_x
        meta.create_gate("ec_add_unequal_last", |meta| {
            let q_ec_add_unequal_last = meta.query_selector(q_ec_add_unequal_last);
            let comm_x = meta.query_advice(col_ptx, Rotation(0));
            let comm_y = meta.query_advice(col_pty, Rotation(0));
            let comm_sel_bit = meta.query_advice(col_rbits, Rotation(0));
            let sm_x = meta.query_advice(col_acc_x, Rotation(0));
            let sm_y = meta.query_advice(col_acc_y, Rotation(0));
            let x3 = meta.query_advice(col_acc_z, Rotation(0));
            let y3 = meta.query_advice(col_lambda, Rotation(0));
            let one = Expression::Constant(C::Scalar::ONE);

            // dx = x2 - x1
            let dx = sm_x.clone() - comm_x.clone();
            let dy = sm_y.clone() - comm_y.clone();
            let dx_sq = dx.clone() * dx.clone();
            let dy_sq = dy.clone() * dy.clone();

            //  x_3 * dx_sq = dy_sq - x_1 * dx_sq - x_2 * dx_sq
            //  y_3 * dx = dy * (x_1 - x_3) - y_1 * dx

            vec![q_ec_add_unequal_last.clone() * ((x3.clone() * dx_sq.clone() - dy_sq.clone() + comm_x.clone() * dx_sq.clone() + sm_x.clone() * dx_sq.clone()) * comm_sel_bit.clone() + (one.clone() - comm_sel_bit.clone()) * (x3.clone() - sm_x.clone())),
                 q_ec_add_unequal_last * ((y3.clone() * dx.clone() - dy.clone() * (comm_x.clone() - x3.clone()) + comm_y.clone() * dx.clone()) * comm_sel_bit.clone() + (one.clone() - comm_sel_bit.clone()) * (y3.clone() - sm_y.clone()))]
        });

        meta.create_gate("ec_convert_affine", |meta| {
            let q_ec_convert_affine = meta.query_selector(q_ec_convert_affine);
            let sm_x = meta.query_advice(col_acc_x, Rotation(-1));
            let sm_y = meta.query_advice(col_acc_y, Rotation(-1));
            let sm_z = meta.query_advice(col_acc_z, Rotation(-1));
            let u = Expression::AccU(AccU{index: 0});

            let sm_xaff = meta.query_advice(col_acc_x, Rotation(0));
            let sm_yaff = meta.query_advice(col_acc_y, Rotation(0));

            Constraints::with_selector(
                q_ec_convert_affine,
                [
                    (
                        "Constrain affine_x conversion",
                        (sm_z.clone() * sm_xaff - sm_x.clone() * u.clone()) * pow4(u.clone()),
                    ),
                    (
                        "Constrain affine_y conversion",
                        (sm_z.clone() * sm_yaff - sm_y.clone() * u.clone()) * pow4(u.clone()),
                    )
                ],
            )
        });

        meta.create_gate("q_ec_num", |meta| {
            let q_ec_num = meta.query_selector(q_ec_num);
            let rbit = meta.query_advice(col_rbits, Rotation(0));
            let e2_prev = meta.query_fixed(col_re2, Rotation(0));
            let lc_prev = meta.query_advice(col_rlc, Rotation(0));
            let lc_next = meta.query_advice(col_rlc, Rotation(1));
            let one = Expression::Constant(C::Scalar::ONE);

            Constraints::with_selector(
                q_ec_num,
                [
                    (
                        "Constrain bit is boolean",
                        rbit.clone() * (one - rbit.clone()),
                    ),
                    (
                        "If bit is 1, e2 added to sum",
                        rbit.clone() * e2_prev.clone() + lc_prev.clone() - lc_next.clone(),
                    ),
                ],
            )
        });

        Self {
            witness: [
                col_rbits, col_rlc, col_ptx, col_pty, col_acc_x, col_acc_y, col_acc_z, col_lambda,
            ],
            fixed: [col_re2],
            selector: [
                q_ec_double_add,
                q_ec_add_unequal_last,
                q_ec_convert_affine,
                q_ec_num,
            ],
            _marker: PhantomData,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        inputs: ScalarMulConfigInputs<C>,
        //copy_r: Option<bool>,
    ) -> Result<[AssignedCell<C::Scalar, C::Scalar>; NUM_IO], Error> {
        layouter.assign_region(
            || "ScalarMulChipConfig assign",
            |mut region| {
                //                   |   fixed   |
                // | row |  r_bits   |    e2     |    lc     |    ptx    |   pty     |   acc.x   |   acc.y   |   acc.z   |  lambda   |
                // | 0   |    -      |    -      |    -      |     -     |    -      |    0      |    1      |    0      |           |
                // | 1   |    0      |    1      |    0      |     x     |    y      |    x      |    y      |    z      |    1      |
                // | 2   |    1      |    2      |    2      |     x     |    y      |    2x     |    2y     |    2z     |    0      |
                // | 3   |    1      |    4      |    4      |     x     |    y      |    4x     |    4y     |    4z     |    1      |
                // | 4   |    0      |    8      |    6      |     x     |    y      |    16x    |    16y    |    16z    |    0      |
                // ...
                // | 128 |    1      |   2^127   |    1      |     x     |    y      |    sm.x   |    sm.y   |    sm.z   |    1      |
                // | 129 |    -      |   2^128   |    r      |  comm_x   |  comm_y   |    sm.X   |    sm.Y   |     X3    |    Y3     |

                let last_row = NUM_CHALLENGE_BITS + 1; // counting from 0
                let ptx =
                    region.assign_advice(|| "ptx_vec", self.witness[2], 1, || inputs.ptx_vec[0])?;
                let pty =
                    region.assign_advice(|| "pty_vec", self.witness[3], 1, || inputs.pty_vec[0])?;

                for row in 0..(last_row + 1) {
                    if row != last_row {
                        if row != 0 {
                            self.selector[0].enable(&mut region, row)?;
                            self.selector[3].enable(&mut region, row)?;
                            region.assign_advice(
                                || "rbits",
                                self.witness[0],
                                row,
                                || inputs.rbits_vec[row - 1],
                            )?;
                            region.assign_advice(
                                || "rlc",
                                self.witness[1],
                                row,
                                || inputs.rlc_vec[row - 1],
                            )?;
                            region.assign_advice(
                                || "lambda",
                                self.witness[7],
                                row,
                                || inputs.lambda_vec[row - 1],
                            )?;
                            region.assign_fixed(
                                || "re2",
                                self.fixed[0],
                                row,
                                || inputs.re2_vec[row - 1],
                            )?;

                            if row != 1 {
                                ptx.copy_advice(|| "ptx_vec", &mut region, self.witness[2], row)?;
                                pty.copy_advice(|| "pty_vec", &mut region, self.witness[3], row)?;
                            }
                        }

                        region.assign_advice(
                            || "acc_x",
                            self.witness[4],
                            row,
                            || inputs.acc_x_vec[row],
                        )?;
                        region.assign_advice(
                            || "acc_y",
                            self.witness[5],
                            row,
                            || inputs.acc_y_vec[row],
                        )?;
                        region.assign_advice(
                            || "acc_z",
                            self.witness[6],
                            row,
                            || inputs.acc_z_vec[row],
                        )?;
                    }

                    if row == last_row {
                        self.selector[1].enable(&mut region, row)?;
                        self.selector[2].enable(&mut region, row)?;
                        region.assign_advice(
                            || "comm_sel",
                            self.witness[0],
                            row,
                            || inputs.rbits_vec[row - 1],
                        )?;
                        region.assign_fixed(
                            || "re2_last",
                            self.fixed[0],
                            row,
                            || inputs.re2_vec[row - 1],
                        )?;
                        region.assign_advice(|| "sm_X", self.witness[4], row, || inputs.sm_X)?;
                        region.assign_advice(|| "sm_Y", self.witness[5], row, || inputs.sm_Y)?;
                        region.assign_advice(|| "X3", self.witness[6], row, || inputs.X3)?;
                        region.assign_advice(|| "Y3", self.witness[7], row, || inputs.Y3)?;
                    }
                }

                let r = region.assign_advice(
                    || "r",
                    self.witness[1],
                    last_row,
                    || inputs.rlc_vec[last_row - 1],
                )?;
                let nark_x =
                    region.assign_advice(|| "nark_X", self.witness[2], 1, || inputs.ptx_vec[0])?;
                let nark_y =
                    region.assign_advice(|| "nark_Y", self.witness[3], 1, || inputs.pty_vec[0])?;
                let acc_x = region.assign_advice(
                    || "comm_X",
                    self.witness[2],
                    last_row,
                    || inputs.comm_X,
                )?;
                let acc_y = region.assign_advice(
                    || "comm_Y",
                    self.witness[3],
                    last_row,
                    || inputs.comm_Y,
                )?;

                Ok([r, nark_x, nark_y, acc_x, acc_y])
            },
        )
    }
}

#[derive(Debug)]
pub struct ScalarMulChipInputs<F, C> {
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
    pub re2_vec: Vec<Value<C::Scalar>>,
    pub rlc_vec: Vec<Value<C::Scalar>>,
    pub ptx_vec: Vec<Value<C::Scalar>>,
    pub pty_vec: Vec<Value<C::Scalar>>,
    pub acc_x_vec: Vec<Value<C::Scalar>>,
    pub acc_y_vec: Vec<Value<C::Scalar>>,
    pub acc_z_vec: Vec<Value<C::Scalar>>,
    pub lambda_vec: Vec<Value<C::Scalar>>,
    pub comm_X: Value<C::Scalar>,
    pub comm_Y: Value<C::Scalar>,
    pub sm_X: Value<C::Scalar>,
    pub sm_Y: Value<C::Scalar>,
    pub X3: Value<C::Scalar>,
    pub Y3: Value<C::Scalar>,
}

#[derive(Clone, Default)]
pub struct ScalarMulChip<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub inputs: Vec<ScalarMulConfigInputs<C>>,
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
        for col in &advices {
            meta.enable_equality(*col);
        }

        let fixed = [0; NUM_FIXED_SM].map(|_| meta.fixed_column());
        for col in &fixed {
            meta.enable_constant(*col);
        }

        ScalarMulChipConfig::configure(meta, advices, fixed)
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
    use super::{ScalarMulChip, ScalarMulConfigInputs};
    use crate::util::{
        arithmetic::{
            add_proj_comp, double_proj_comp, fe_from_bits_le, fe_to_fe, is_identity_proj,
            is_scaled_identity_proj, powers, sub_proj, sub_proj_comp, ProjectivePoint,
        },
        izip_eq,
    };
    use bitvec::vec;
    use halo2_proofs::{
        arithmetic::Field,
        halo2curves::{
            ff::BatchInvert,
            group::{cofactor::CofactorCurveAffine, Curve, Group},
            Coordinates, CurveAffine,
        },
    };
    use halo2_proofs::{
        circuit::Value,
        dev::MockProver,
        halo2curves::{
            bn256::{Fq, Fr, G1Affine, G1},
            grumpkin,
        },
        plonk::Assigned,
    };
    use itertools::Itertools;
    use rand::{rngs::OsRng, Rng};
    use std::{marker::PhantomData, time::Instant};

    pub const NUM_CHALLENGE_BITS: usize = 128;

    #[test]
    fn ec_vec() {
        use plotters::prelude::*;
        let root = BitMapBackend::new("ECChip_deg6.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("ECChip_deg6", ("sans-serif", 60)).unwrap();

        let k = 8;
        let mut rng = OsRng;
        let scalar_bits = NUM_CHALLENGE_BITS;

        let mut rbits = Vec::new();
        rbits.extend((0..scalar_bits).map(|_| rng.gen_bool(1.0 / 3.0)));
        let rbits_rev = rbits.iter().rev().cloned().collect_vec();
        let mut rbits_vec = rbits
            .iter()
            .map(|bit| Value::known(if *bit { Fq::ONE } else { Fq::ZERO }))
            .rev()
            .collect_vec();

        let witness_gen_time = Instant::now();
        let re2_vec = powers(Fq::from(2))
            .take(scalar_bits + 1)
            .map(Value::known)
            .collect_vec()
            .into_iter()
            .rev()
            .collect_vec();
        let mut rlc_vec = vec![Value::known(Fq::ZERO)];
        for i in 0..scalar_bits {
            let rlc = if rbits_rev[i] {
                rlc_vec[i] + re2_vec[i]
            } else {
                rlc_vec[i]
            };
            rlc_vec.push(rlc);
        }
        // assert_eq!(rlc_vec.last().unwrap(), scalar_bits + 1);
        let zero = ProjectivePoint {
            x: Fq::zero(),
            y: Fq::one(),
            z: Fq::zero(),
        };

        let mut p = G1Affine::identity();
        while p == G1Affine::identity() {
            p = G1Affine::random(&mut rng);
        }

        let p_single = p;
        let mut ptx_vec = Vec::new();
        let mut pty_vec = Vec::new();
        for i in 0..scalar_bits {
            ptx_vec.push(Value::known(p_single.x));
            pty_vec.push(Value::known(p_single.y));
        }

        let comm = G1::random(rng);
        if comm == G1::identity() {
            rbits_vec.push(Value::known(Fq::ZERO));
        } else {
            rbits_vec.push(Value::known(Fq::ONE));
        }
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
                ProjectivePoint::new(p_single.x, p_single.y, Fq::one())
            } else {
                zero
            };

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
            let acc_prev_proj = ProjectivePoint::new(
                acc_prev_xvec[i + 1],
                acc_prev_yvec[i + 1],
                acc_prev_zvec[i + 1],
            );
            let lhs_double_proj =
                ProjectivePoint::new(lhs_double_xvec[i], lhs_double_yvec[i], lhs_double_zvec[i]);
            let p_single_proj = if rbits_rev[i] {
                ProjectivePoint::new(p_single.x, p_single.y, Fq::one())
            } else {
                zero
            };

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

        let batch_invert_time = Instant::now();
        lhs_zvec.batch_invert();
        println!("batch_invert_time2: {:?}", batch_invert_time.elapsed());

        let lambda_vec = lhs_zvec
            .iter()
            .zip(rhs_zvec)
            .map(|(lhs, rhs)| Value::known(lhs * rhs))
            .collect_vec();
        let rbits_native = rbits
            .iter()
            .map(|bit| if *bit { Fr::ONE } else { Fr::ZERO })
            .collect_vec();

        let r = fe_from_bits_le(rbits_native);
        let r_non_native: Fq = fe_to_fe(r);
        let scalar_mul_given = p * r;
        let scalar_mul_proj = ProjectivePoint::new(
            *acc_prev_xvec.last().unwrap(),
            *acc_prev_yvec.last().unwrap(),
            *acc_prev_zvec.last().unwrap(),
        );
        assert_eq!(
            scalar_mul_given.x * scalar_mul_proj.z,
            scalar_mul_proj.x * scalar_mul_given.z
        );
        assert_eq!(
            scalar_mul_given.y * scalar_mul_proj.z,
            scalar_mul_proj.y * scalar_mul_given.z
        );

        // do point addition of comm and sm
        let result_given = comm + scalar_mul_given;
        let comm_affine = comm.to_affine();
        let comm_proj = ProjectivePoint::new(comm.x, comm.y, comm.z);
        let result_calc = add_proj_comp(comm_proj, scalar_mul_proj);
        assert_eq!(
            result_given.x * result_calc.z,
            result_calc.x * result_given.z
        );
        assert_eq!(
            result_given.y * result_calc.z,
            result_calc.y * result_given.z
        );

        let scalar_mul_given_affine = scalar_mul_given.to_affine();
        let result_given_affine = result_given.to_affine();
        let acc_x_vec = acc_prev_xvec
            .iter()
            .map(|fe| Value::known(*fe))
            .collect_vec();
        let acc_y_vec = acc_prev_yvec
            .iter()
            .map(|fe| Value::known(*fe))
            .collect_vec();
        let acc_z_vec = acc_prev_zvec
            .iter()
            .map(|fe| Value::known(*fe))
            .collect_vec();
        println!("witness_gen_time: {:?}", witness_gen_time.elapsed());

        let inputs = ScalarMulConfigInputs::<grumpkin::G1Affine> {
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

        let circuit = ScalarMulChip::<grumpkin::G1Affine> {
            inputs: vec![inputs],
        };
        MockProver::run(k, &circuit, vec![])
            .unwrap()
            .assert_satisfied();

        // halo2_base::halo2_proofs::dev::CircuitLayout::default()
        // .render(k, &circuit, &root)
        // .unwrap();
    }

//     #[test]
//     fn ec_vec_g1() {
//         use plotters::prelude::*;
//         let root = BitMapBackend::new("ECChip_deg6.png", (1024, 3096)).into_drawing_area();
//         root.fill(&WHITE).unwrap();
//         let root = root.titled("ECChip_deg6", ("sans-serif", 60)).unwrap();

//         let k = 8;
//         let mut rng = OsRng;
//         let scalar_bits = NUM_CHALLENGE_BITS;

//         let mut rbits = Vec::new();
//         rbits.extend((0..scalar_bits).map(|_| rng.gen_bool(1.0 / 3.0)));
//         let rbits_rev = rbits.iter().rev().cloned().collect_vec();
//         let mut rbits_vec = rbits
//             .iter()
//             .map(|bit| Value::known(if *bit { Fq::ONE } else { Fq::ZERO }))
//             .rev()
//             .collect_vec();

//         // let powers_time = Instant::now();
//         // let re2_vec = powers(Fq::from(2)).take(scalar_bits + 1).map(Value::known).collect_vec().into_iter().rev().collect_vec();
//         // println!("powers_time: {:?}", powers_time.elapsed());

//         let witness_gen_time = Instant::now();
//         let re2_vec = powers(Fq::from(2))
//             .take(scalar_bits + 1)
//             .map(Value::known)
//             .collect_vec()
//             .into_iter()
//             .rev()
//             .collect_vec();
//         let mut rlc_vec = vec![Value::known(Fq::ZERO)];
//         for i in 0..scalar_bits {
//             let rlc = if rbits_rev[i] {
//                 rlc_vec[i] + re2_vec[i]
//             } else {
//                 rlc_vec[i]
//             };
//             rlc_vec.push(rlc);
//         }
//         // let zero = ProjectivePoint {
//         //     x: Fq::zero(),
//         //     y: Fq::one(),
//         //     z: Fq::zero(),
//         // };
//         let zero = G1::identity();
//         let mut p = G1::identity();
//         while p == G1::identity() {
//             p = G1::random(&mut rng);
//         }

//         let p_single = p.to_affine();
//         let mut ptx_vec = Vec::new();
//         let mut pty_vec = Vec::new();
//         for i in 0..scalar_bits {
//             ptx_vec.push(Value::known(p_single.x));
//             pty_vec.push(Value::known(p_single.y));
//         }

//         let comm = G1::random(rng);
//         if comm == G1::identity() {
//             rbits_vec.push(Value::known(Fq::ZERO));
//         } else {
//             rbits_vec.push(Value::known(Fq::ONE));
//         }

//         //let mut acc_prev = ProjectivePoint::identity();
//         let mut acc_prev = G1::identity();
//         let mut acc_prev_xvec = Vec::new();
//         let mut acc_prev_yvec = Vec::new();
//         let mut acc_prev_zvec = Vec::new();

//         let mut lhs_double_xvec = Vec::new();
//         let mut lhs_double_yvec = Vec::new();
//         let mut lhs_double_zvec = Vec::new();
//         let mut lhs_zvec = Vec::new();
//         let mut rhs_zvec = Vec::new();

//         acc_prev_xvec.push(acc_prev.x);
//         acc_prev_yvec.push(acc_prev.y);
//         acc_prev_zvec.push(acc_prev.z);

//         for i in 0..scalar_bits {
//             let choice_proj = if rbits_rev[i] {
//                 p
//                 // ProjectivePoint::new(p_single.x, p_single.y, Fq::one())
//             } else {
//                 zero
//             };

//             acc_prev = G1::double(&acc_prev); //double_proj_comp(acc_prev);
//             let lhs = acc_prev;
//             acc_prev = acc_prev + choice_proj; //add_proj_comp(acc_prev, choice_proj);
//             acc_prev_xvec.push(acc_prev.x);
//             acc_prev_yvec.push(acc_prev.y);
//             acc_prev_zvec.push(acc_prev.z);

//             lhs_double_xvec.push(lhs.x);
//             lhs_double_yvec.push(lhs.y);
//             lhs_double_zvec.push(lhs.z);

//             let lhs_double_proj =
//                 ProjectivePoint::new(lhs_double_xvec[i], lhs_double_yvec[i], lhs_double_zvec[i]);
//             let rhs = acc_prev - choice_proj; //sub_proj_comp(acc_prev_proj, p_single_proj);
//             let rhs_proj = ProjectivePoint::new(rhs.x, rhs.y, rhs.z);
//             if is_identity_proj(rhs_proj) && is_identity_proj(lhs_double_proj) {
//                 lhs_zvec.push(Fq::one());
//                 rhs_zvec.push(Fq::one());
//             } else if is_identity_proj(rhs_proj) && is_scaled_identity_proj(lhs_double_proj) {
//                 lhs_zvec.push(lhs_double_proj.y);
//                 rhs_zvec.push(Fq::one());
//             } else if is_identity_proj(lhs_double_proj) && is_scaled_identity_proj(rhs_proj) {
//                 lhs_zvec.push(Fq::one());
//                 rhs_zvec.push(rhs.y);
//             } else {
//                 lhs_zvec.push(lhs_double_zvec[i]);
//                 rhs_zvec.push(rhs.z);
//             }
//         }

//         let batch_invert_time = Instant::now();
//         lhs_zvec.batch_invert();
//         println!("batch_invert_time2: {:?}", batch_invert_time.elapsed());

//         let lambda_vec = lhs_zvec
//             .iter()
//             .zip(rhs_zvec)
//             .map(|(lhs, rhs)| Value::known(lhs * rhs))
//             .collect_vec();

//         let rbits_native = rbits
//             .iter()
//             .map(|bit| if *bit { Fr::ONE } else { Fr::ZERO })
//             .collect_vec();

//         let r = fe_from_bits_le(rbits_native);
//         let r_non_native: Fq = fe_to_fe(r);
//         let scalar_mul_given = p * r;
//         let scalar_mul_proj = ProjectivePoint::new(
//             acc_prev_xvec.last().unwrap().clone(),
//             acc_prev_yvec.last().unwrap().clone(),
//             acc_prev_zvec.last().unwrap().clone(),
//         );
//         assert_eq!(
//             scalar_mul_given.x * scalar_mul_proj.z,
//             scalar_mul_proj.x * scalar_mul_given.z
//         );
//         assert_eq!(
//             scalar_mul_given.y * scalar_mul_proj.z,
//             scalar_mul_proj.y * scalar_mul_given.z
//         );

//         // do point addition of comm and sm
//         let result_given = comm + scalar_mul_given;
//         let comm_proj = ProjectivePoint::new(comm.x, comm.y, comm.z);
//         let result_calc = add_proj_comp(comm_proj, scalar_mul_proj);
//         // assert_eq!(result_given.x * result_calc.z, result_calc.x * result_given.z);
//         // assert_eq!(result_given.y * result_calc.z, result_calc.y * result_given.z);

//         let comm_affine = comm.to_affine();
//         let scalar_mul_given_affine = scalar_mul_given.to_affine();
//         let result_given_affine = result_given.to_affine();
//         let acc_x_vec = acc_prev_xvec
//             .iter()
//             .map(|fe| Value::known(*fe))
//             .collect_vec();
//         let acc_y_vec = acc_prev_yvec
//             .iter()
//             .map(|fe| Value::known(*fe))
//             .collect_vec();
//         let acc_z_vec = acc_prev_zvec
//             .iter()
//             .map(|fe| Value::known(*fe))
//             .collect_vec();
//         println!("witness_gen_time: {:?}", witness_gen_time.elapsed());

//         let inputs = ScalarMulConfigInputs::<grumpkin::G1Affine> {
//             rbits_vec,
//             re2_vec,
//             rlc_vec,
//             ptx_vec,
//             pty_vec,
//             acc_x_vec,
//             acc_y_vec,
//             acc_z_vec,
//             lambda_vec,
//             comm_X: Value::known(comm_affine.x),
//             comm_Y: Value::known(comm_affine.y),
//             sm_X: Value::known(scalar_mul_given_affine.x),
//             sm_Y: Value::known(scalar_mul_given_affine.y),
//             X3: Value::known(result_given_affine.x),
//             Y3: Value::known(result_given_affine.y),
//         };

//         let circuit = ScalarMulChip::<grumpkin::G1Affine> {
//             inputs: vec![inputs],
//         };
//         MockProver::run(k, &circuit, vec![])
//             .unwrap()
//             .assert_satisfied();

//         halo2_base::halo2_proofs::dev::CircuitLayout::default()
//             .render(k, &circuit, &root)
//             .unwrap();
//     }

}
