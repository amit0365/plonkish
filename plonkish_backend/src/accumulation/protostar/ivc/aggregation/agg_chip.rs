use std::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
};

use halo2_base::{
    AssignedValue,
    gates::flex_gate::threads::SinglePhaseCoreManager,
    halo2_proofs::{
        arithmetic::Field,
        circuit::Value,
        halo2curves::{
            ff::PrimeFieldBits,
            group::prime::PrimeCurveAffine,
        },
        plonk::Error,
    },
    utils::BigPrimeField,
};

use halo2_ecc::{
    bigint::ProperCrtUint,
    ecc::EcPoint,
};

use serde::{
    de::DeserializeOwned,
    Serialize,
};

use crate::{
    accumulation::protostar::ivc::halo2::test::strawman::{Chip, PoseidonTranscriptChip},
    backend::hyperplonk::{HyperPlonkVerifierParam, verifier::point_offset},
    pcs::{Evaluation, multilinear::{MultilinearHyrax, MultilinearHyraxParams, MultilinearIpaParams}},
    poly::multilinear::{rotation_eval_coeff_pattern, rotation_eval_point_pattern, zip_self},
    util::{
        arithmetic::{barycentric_weights, powers, steps, BooleanHypercube, TwoChainCurve},
        expression::{CommonPolynomial, Expression, Query, Rotation},
        izip_eq,
    },
};

use core::iter;
use itertools::{Itertools, chain};
use crate::util::BitIndex;


impl<C: TwoChainCurve> Chip<C>
where
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    fn hornor(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        coeffs: &[ProperCrtUint<C::Scalar>],
        x: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> 
    {
        let powers_of_x = self.powers_base(builder, x, coeffs.len())?;
        self.inner_product_base(builder, coeffs, &powers_of_x)
    }

    pub fn barycentric_weights(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        points: &[ProperCrtUint<C::Scalar>],
        ) -> Result<Vec<ProperCrtUint<C::Scalar>>, Error> {
        if points.len() == 1 {
            return Ok(vec![self.assign_constant_base(builder, C::Base::ONE)?]);
        }
        points
            .iter()
            .enumerate()
            .map(|(j, point_j)| {
                let diffs = points
                    .iter()
                    .enumerate()
                    .filter_map(|(i, point_i)| {
                        (i != j).then(|| self.sub_base(builder, point_j, point_i))
                    })
                    .try_collect::<_, Vec<_>, _>()?;
                let weight_inv = self.product_base(builder, &diffs)?;
                self.invert_incomplete_base(builder, &weight_inv)
            })
        .collect()
    }

    pub fn barycentric_interpolate(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        weights: &[ProperCrtUint<C::Scalar>],
        points: &[ProperCrtUint<C::Scalar>],
        evals: &[ProperCrtUint<C::Scalar>],
        x: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
        let (coeffs, sum_inv) = {
            let coeffs = izip_eq!(weights, points)
                .map(|(weight, point)| {
                    let coeff = self.sub_base(builder, x, point)?;
                    self.div_incomplete_base(builder, weight, &coeff)
                })
                .try_collect::<_, Vec<_>, _>()?;
            let sum = self.sum_base(builder, &coeffs)?;
            let sum_inv = self.invert_incomplete_base(builder, &sum)?;
            (coeffs, sum_inv)
        };
        let numer = self.inner_product_base(builder, &coeffs, evals)?;
        self.mul_base(builder, &numer, &sum_inv)
    }

    fn rotation_eval_points(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        x: &[ProperCrtUint<C::Scalar>],
        one_minus_x: &[ProperCrtUint<C::Scalar>],
        rotation: Rotation,
        ) -> Result<Vec<Vec<ProperCrtUint<C::Scalar>>>, Error> {
        if rotation == Rotation::cur() {
            return Ok(vec![x.to_vec()]);
        }

        let zero = self.assign_constant_base(builder, C::Base::ZERO)?;
        let one = self.assign_constant_base(builder, C::Base::ONE)?;
        let distance = rotation.distance();
        let num_x = x.len() - distance;
        let points = if rotation < Rotation::cur() {
            let pattern = rotation_eval_point_pattern::<false>(x.len(), distance);
            let x = &x[distance..];
            let one_minus_x = &one_minus_x[distance..];
            pattern
                .iter()
                .map(|pat| {
                    iter::empty()
                        .chain((0..num_x).map(|idx| {
                            if pat.nth_bit(idx) {
                                &one_minus_x[idx]
                            } else {
                                &x[idx]
                            }
                        }))
                        .chain((0..distance).map(|idx| {
                            if pat.nth_bit(idx + num_x) {
                                &one
                            } else {
                                &zero
                            }
                        }))
                        .cloned()
                        .collect_vec()
                })
                .collect_vec()
        } else {
            let pattern = rotation_eval_point_pattern::<true>(x.len(), distance);
            let x = &x[..num_x];
            let one_minus_x = &one_minus_x[..num_x];
            pattern
                .iter()
                .map(|pat| {
                    iter::empty()
                        .chain((0..distance).map(|idx| if pat.nth_bit(idx) { &one } else { &zero }))
                        .chain((0..num_x).map(|idx| {
                            if pat.nth_bit(idx + distance) {
                                &one_minus_x[idx]
                            } else {
                                &x[idx]
                            }
                        }))
                        .cloned()
                        .collect_vec()
                })
                .collect()
        };

        Ok(points)
    }

    fn rotation_eval(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        x: &[ProperCrtUint<C::Scalar>],
        rotation: Rotation,
        evals_for_rotation: &[ProperCrtUint<C::Scalar>],
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
        if rotation == Rotation::cur() {
            assert!(evals_for_rotation.len() == 1);
            return Ok(evals_for_rotation[0].clone());
        }

        let num_vars = x.len();
        let distance = rotation.distance();
        assert!(evals_for_rotation.len() == 1 << distance);
        assert!(distance <= num_vars);

        let (pattern, nths, x) = if rotation < Rotation::cur() {
            (
                rotation_eval_coeff_pattern::<false>(num_vars, distance),
                (1..=distance).rev().collect_vec(),
                x[0..distance].iter().rev().collect_vec(),
            )
        } else {
            (
                rotation_eval_coeff_pattern::<true>(num_vars, distance),
                (num_vars - 1..).take(distance).collect(),
                x[num_vars - distance..].iter().collect(),
            )
        };
        x.into_iter()
            .zip(nths)
            .enumerate()
            .fold(
                Ok(Cow::Borrowed(evals_for_rotation)),
                |evals, (idx, (x_i, nth))| {
                    evals.and_then(|evals| {
                        pattern
                            .iter()
                            .step_by(1 << idx)
                            .map(|pat| pat.nth_bit(nth))
                            .zip(zip_self!(evals.iter()))
                            .map(|(bit, (mut eval_0, mut eval_1))| {
                                if bit {
                                    std::mem::swap(&mut eval_0, &mut eval_1);
                                }
                                let diff = self.sub_base(builder, eval_1, eval_0)?;
                                let diff_x_i = self.mul_base(builder, &diff, x_i)?;
                                self.add_base(builder, &diff_x_i, eval_0)
                            })
                            .try_collect::<_, Vec<_>, _>()
                            .map(Into::into)
                    })
                },
            )
        .map(|evals| evals[0].clone())
    }

    fn eq_xy_coeffs(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        y: &[ProperCrtUint<C::Scalar>],
        ) -> Result<Vec<ProperCrtUint<C::Scalar>>, Error> {
        let mut evals = vec![self.assign_constant_base(builder, C::Base::ONE)?];

        for y_i in y.iter().rev() {
            evals = evals
                .iter()
                .map(|eval| {
                    let hi = self.mul_base(builder, eval, y_i)?;
                    let lo = self.sub_base(builder, eval, &hi)?;
                    Ok([lo, hi])
                })
                .try_collect::<_, Vec<_>, Error>()?
                .into_iter()
                .flatten()
                .collect();
        }

        Ok(evals)
    }

    fn eq_xy_eval(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        x: &[ProperCrtUint<C::Scalar>],
        y: &[ProperCrtUint<C::Scalar>],
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
        let terms = izip_eq!(x, y)
            .map(|(x, y)| {
                let one = self.assign_constant_base(builder, C::Base::ONE)?;
                let xy = self.mul_base(builder, x, y)?;
                let two_xy = self.add_base(builder, &xy, &xy)?;
                let two_xy_plus_one = self.add_base(builder, &two_xy, &one)?;
                let x_plus_y = self.add_base(builder, x, y)?;
                self.sub_base(builder, &two_xy_plus_one, &x_plus_y)
            })
            .try_collect::<_, Vec<_>, _>()?;
        self.product_base(builder, &terms)
        }

        #[allow(clippy::too_many_arguments)]
    fn evaluate(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        expression: &Expression<C::Base>,
        identity_eval: &ProperCrtUint<C::Scalar>,
        lagrange_evals: &BTreeMap<i32, ProperCrtUint<C::Scalar>>,
        eq_xy_eval: &ProperCrtUint<C::Scalar>,
        query_evals: &BTreeMap<Query, ProperCrtUint<C::Scalar>>,
        challenges: &[ProperCrtUint<C::Scalar>],
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
        let mut evaluate = |expression| {
            self.evaluate(
                builder,
                expression,
                identity_eval,
                lagrange_evals,
                eq_xy_eval,
                query_evals,
                challenges,
            )
        };
        match expression {
            Expression::Constant(scalar) => self.assign_constant_base(builder, *scalar),
            Expression::CommonPolynomial(poly) => match poly {
                CommonPolynomial::Identity => Ok(identity_eval.clone()),
                CommonPolynomial::Lagrange(i) => Ok(lagrange_evals[i].clone()),
                CommonPolynomial::EqXY(idx) => {
                    assert_eq!(*idx, 0);
                    Ok(eq_xy_eval.clone())
                }
            },
            Expression::Polynomial(query) => Ok(query_evals[query].clone()),
            Expression::Challenge(index) => Ok(challenges[*index].clone()),
            Expression::Negated(a) => {
                let a = evaluate(a)?;
                self.neg_base(builder, &a)
            }
            Expression::Sum(a, b) => {
                let a = evaluate(a)?;
                let b = evaluate(b)?;
                self.add_base(builder, &a, &b)
            }
            Expression::Product(a, b) => {
                let a = evaluate(a)?;
                let b = evaluate(b)?;
                self.mul_base(builder, &a, &b)
            }
            Expression::Scaled(a, scalar) => {
                let a = evaluate(a)?;
                let scalar = self.assign_constant_base(builder, *scalar)?;
                self.mul_base(builder, &a, &scalar)
            }
            Expression::DistributePowers(exprs, scalar) => {
                assert!(!exprs.is_empty());
                if exprs.len() == 1 {
                    return evaluate(&exprs[0]);
                }
                let scalar = evaluate(scalar)?;
                let exprs = exprs.iter().map(evaluate).try_collect::<_, Vec<_>, _>()?;
                let mut scalars = Vec::with_capacity(exprs.len());
                scalars.push(self.assign_constant_base(builder, C::Base::ONE)?);
                scalars.push(scalar);
                for _ in 2..exprs.len() {
                    scalars.push(self.mul_base(builder, &scalars[1], scalars.last().unwrap())?);
                }
                self.inner_product_base(builder, &scalars, &exprs)
            }
        }
    }

    fn verify_sum_check<const IS_MSG_EVALS: bool>(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        num_vars: usize,
        degree: usize,
        sum: &ProperCrtUint<C::Scalar>,
        transcript: &mut PoseidonTranscriptChip<C>,
        ) -> Result<(ProperCrtUint<C::Scalar>, Vec<ProperCrtUint<C::Scalar>>), Error> {
        let points = steps(C::Base::ZERO).take(degree + 1).collect_vec();
        let weights = barycentric_weights(&points)
            .into_iter()
            .map(|weight| self.assign_constant_base(builder, weight))
            .try_collect::<_, Vec<_>, _>()?;
        let points = points
            .into_iter()
            .map(|point| self.assign_constant_base(builder, point))
            .try_collect::<_, Vec<_>, _>()?;

        let mut sum = Cow::Borrowed(sum);
        let mut x = Vec::with_capacity(num_vars);
        for _ in 0..num_vars {
            let msg = transcript.read_field_elements(builder, degree + 1)?;
            x.push(transcript.squeeze_challenge(builder)?.as_ref().clone());

            let sum_from_evals = if IS_MSG_EVALS {
                self.add_base(builder, &msg[0], &msg[1])?
            } else {
                self.sum_base(builder, chain![[&msg[0], &msg[0]], &msg[1..]])?
            };
            self.constrain_equal_base(builder, &sum, &sum_from_evals)?;

            if IS_MSG_EVALS {
                sum = Cow::Owned(self.barycentric_interpolate(
                    builder,
                    &weights,
                    &points,
                    &msg,
                    x.last().unwrap(),
                )?);
            } else {
                sum = Cow::Owned(self.hornor(builder,  &msg, x.last().unwrap())?);
            }
        }

        Ok((sum.into_owned(), x))
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    pub fn verify_sum_check_and_query(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        num_vars: usize,
        expression: &Expression<C::Base>,
        sum: &ProperCrtUint<C::Scalar>,
        instances: &[Vec<ProperCrtUint<C::Scalar>>],
        challenges: &[ProperCrtUint<C::Scalar>],
        y: &[ProperCrtUint<C::Scalar>],
        transcript: &mut PoseidonTranscriptChip<C>,
        ) -> Result<
        (
            Vec<Vec<ProperCrtUint<C::Scalar>>>,
            Vec<Evaluation<ProperCrtUint<C::Scalar>>>,
        ),
        Error,
        > {
        let degree = expression.degree();

        let (x_eval, x) =
            self.verify_sum_check::<true>(builder,  num_vars, degree, sum, transcript)?;

        let pcs_query = {
            let mut used_query = expression.used_query();
            used_query.retain(|query| query.poly() >= instances.len());
            used_query
        };
        let (evals_for_rotation, query_evals) = pcs_query
            .iter()
            .map(|query| {
                let evals_for_rotation =
                    transcript.read_field_elements(builder, 1 << query.rotation().distance())?;
                let eval = self.rotation_eval(
                    builder,
                    x.as_ref(),
                    query.rotation(),
                    &evals_for_rotation,
                )?;
                Ok((evals_for_rotation, (*query, eval)))
            })
            .try_collect::<_, Vec<_>, Error>()?
            .into_iter()
            .unzip::<_, _, Vec<_>, Vec<_>>();

        let one = self.assign_constant_base(builder, C::Base::ONE)?;
        let one_minus_x = x
            .iter()
            .map(|x_i| self.sub_base(builder, &one, x_i))
            .try_collect::<_, Vec<_>, _>()?;

        let (lagrange_evals, query_evals) = {
            let mut instance_query = expression.used_query();
            instance_query.retain(|query| query.poly() < instances.len());

            let lagranges = {
                let mut lagranges = instance_query.iter().fold(0..0, |range, query| {
                    let i = -query.rotation().0;
                    range.start.min(i)..range.end.max(i + instances[query.poly()].len() as i32)
                });
                if lagranges.start < 0 {
                    lagranges.start -= 1;
                }
                if lagranges.end > 0 {
                    lagranges.end += 1;
                }
                chain![lagranges, expression.used_langrange()].collect::<BTreeSet<_>>()
            };

            let bh = BooleanHypercube::new(num_vars).iter().collect_vec();
            let lagrange_evals = lagranges
                .into_iter()
                .map(|i| {
                    let b = bh[i.rem_euclid(1 << num_vars as i32) as usize];
                    let eval = self.product_base(
                        builder,
                        (0..num_vars).map(|idx| {
                            if b.nth_bit(idx) {
                                &x[idx]
                            } else {
                                &one_minus_x[idx]
                            }
                        }),
                    )?;
                    Ok((i, eval))
                })
                .try_collect::<_, BTreeMap<_, _>, Error>()?;

            let instance_evals = instance_query
                .into_iter()
                .map(|query| {
                    let is = if query.rotation() > Rotation::cur() {
                        (-query.rotation().0..0)
                            .chain(1..)
                            .take(instances[query.poly()].len())
                            .collect_vec()
                    } else {
                        (1 - query.rotation().0..)
                            .take(instances[query.poly()].len())
                            .collect_vec()
                    };
                    let eval = self.inner_product_base(
                        builder,
                        &instances[query.poly()],
                        is.iter().map(|i| lagrange_evals.get(i).unwrap()),
                    )?;
                    Ok((query, eval))
                })
                .try_collect::<_, BTreeMap<_, _>, Error>()?;

            (
                lagrange_evals,
                chain![query_evals, instance_evals].collect(),
            )
        };
        let identity_eval = {
            let powers_of_two = powers(C::Base::ONE.double())
                .take(x.len())
                .map(|power_of_two| self.assign_constant_base(builder, power_of_two))
                .try_collect::<_, Vec<_>, Error>()?;
            self.inner_product_base(builder, &powers_of_two, &x)?
        };
        let eq_xy_eval = self.eq_xy_eval(builder, &x, y)?;

        let eval = self.evaluate(
            builder,
            expression,
            &identity_eval,
            &lagrange_evals,
            &eq_xy_eval,
            &query_evals,
            challenges,
        )?;

        self.constrain_equal_base(builder, &x_eval, &eval)?;

        let points = pcs_query
            .iter()
            .map(Query::rotation)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|rotation| self.rotation_eval_points(builder, &x, &one_minus_x, rotation))
            .try_collect::<_, Vec<_>, _>()?
            .into_iter()
            .flatten()
            .collect_vec();

        let point_offset = point_offset(&pcs_query);
        let evals = pcs_query
            .iter()
            .zip(evals_for_rotation)
            .flat_map(|(query, evals_for_rotation)| {
                (point_offset[&query.rotation()]..)
                    .zip(evals_for_rotation)
                    .map(|(point, eval)| Evaluation::new(query.poly(), point, eval))
            })
            .collect();
        Ok((points, evals))
    }

    #[allow(clippy::type_complexity)]
    pub fn multilinear_pcs_batch_verify<'a, Comm>(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        comms: &'a [Comm],
        points: &[Vec<ProperCrtUint<C::Scalar>>],
        evals: &[Evaluation<ProperCrtUint<C::Scalar>>],
        transcript: &mut PoseidonTranscriptChip<C>,
        ) -> Result<
        (
            Vec<(&'a Comm, ProperCrtUint<C::Scalar>)>,
            Vec<ProperCrtUint<C::Scalar>>,
            ProperCrtUint<C::Scalar>,
        ),
        Error,
        > 
        {
        let num_vars = points[0].len();

        let ell = evals.len().next_power_of_two().ilog2() as usize;
        let t = transcript
            .squeeze_challenges(builder, ell)?
            .iter()
            .map(AsRef::as_ref)
            .cloned()
            .collect_vec();

        let eq_xt = self.eq_xy_coeffs(builder, &t)?;
        let tilde_gs_sum = self.inner_product_base(
            builder,
            &eq_xt[..evals.len()],
            evals.iter().map(Evaluation::value),
        )?;
        let (g_prime_eval, x) =
            self.verify_sum_check::<false>(builder,  num_vars, 2, &tilde_gs_sum, transcript)?;
        let eq_xy_evals = points
            .iter()
            .map(|point| self.eq_xy_eval(builder, &x, point))
            .try_collect::<_, Vec<_>, _>()?;

        let g_prime_comm = {
            let scalars = evals.iter().zip(&eq_xt).fold(
                Ok::<_, Error>(BTreeMap::<_, _>::new()),
                |scalars, (eval, eq_xt_i)| {
                    let mut scalars = scalars?;
                    let scalar = self.mul_base(builder, &eq_xy_evals[eval.point()], eq_xt_i)?;
                    match scalars.entry(eval.poly()) {
                        Entry::Occupied(mut entry) => {
                            *entry.get_mut() = self.add_base(builder, entry.get(), &scalar)?;
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(scalar);
                        }
                    }
                    Ok(scalars)
                },
            )?;
            scalars
                .into_iter()
                .map(|(poly, scalar)| (&comms[poly], scalar))
                .collect_vec()
        };

        Ok((g_prime_comm, x, g_prime_eval))
    }

    pub fn verify_ipa<'a>(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        vp: &MultilinearIpaParams<C::Secondary>,
        comm: impl IntoIterator<Item = (&'a EcPoint<C::Scalar, AssignedValue<C::Scalar>>, &'a ProperCrtUint<C::Scalar>)>,
        point: &[ProperCrtUint<C::Scalar>],
        eval: &ProperCrtUint<C::Scalar>,
        transcript: &mut PoseidonTranscriptChip<C>,
        ) -> Result<(), Error>
        where
        EcPoint<C::Scalar, AssignedValue<C::Scalar>>: 'a,
        ProperCrtUint<C::Scalar>: 'a,
        {
        let xi_0 = transcript.squeeze_challenge(builder)?.as_ref().clone();

        let (ls, rs, xis) = iter::repeat_with(|| {
            Ok::<_, Error>((
                transcript.read_commitment(builder)?,
                transcript.read_commitment(builder)?,
                transcript.squeeze_challenge(builder)?.as_ref().clone(),
            ))
        })
        .take(point.len())
        .try_collect::<_, Vec<_>, _>()?
        .into_iter()
        .multiunzip::<(Vec<_>, Vec<_>, Vec<_>)>();
        let g_k = transcript.read_commitment(builder)?;
        let c = transcript.read_field_element(builder)?;

        let xi_invs = xis
            .iter()
            .map(|xi| self.invert_incomplete_base(builder, xi))
            .try_collect::<_, Vec<_>, _>()?;
        let eval_prime = self.mul_base(builder, &xi_0, eval)?;

        let h_eval = {
            let one = self.assign_constant_base(builder, C::Base::ONE)?;
            let terms = izip_eq!(point, xis.iter().rev())
                .map(|(point, xi)| {
                    let point_xi = self.mul_base(builder, point, xi)?;
                    let neg_point = self.neg_base(builder, point)?;
                    self.sum_base(builder, [&one, &neg_point, &point_xi])
                })
                .try_collect::<_, Vec<_>, _>()?;
            self.product_base(builder, &terms)?
        };
        let h_coeffs = {
            let one = self.assign_constant_base(builder, C::Base::ONE)?;

            let mut coeff = vec![one];

            for xi in xis.iter().rev() {
                let extended = coeff
                    .iter()
                    .map(|coeff| self.mul_base(builder, coeff, xi))
                    .try_collect::<_, Vec<_>, _>()?;
                coeff.extend(extended);
            }

            coeff
        };

        let neg_c = self.neg_base(builder, &c)?;
        let h_scalar = {
            let mut tmp = self.mul_base(builder, &neg_c, &h_eval)?;
            tmp = self.mul_base(builder, &tmp, &xi_0)?;
            self.add_base(builder, &tmp, &eval_prime)?
        };
        let identity = self.assign_constant_secondary(builder, C::Secondary::identity())?;
        let out = {
            let h = self.assign_constant_secondary(builder, *vp.h())?;
            let (mut bases, mut scalars) = comm.into_iter().map(|(base, scalar)| (base, scalar.clone())).unzip::<_, _, Vec<_>, Vec<_>>();
            scalars.extend(chain![&xi_invs, &xis, [&h_scalar, &neg_c]].map(|scalar| scalar.clone()));          
            bases.extend(chain![&ls, &rs, [&h, &g_k]]);
            let deref_bases = bases.iter().map(|&x| x.clone()).collect_vec();
            self.variable_base_msm_secondary(builder, &deref_bases, scalars)?
        };
        self.constrain_equal_secondary(builder, &out, &identity)?;

        let out = {
            let bases = vp.g();
            let scalars = h_coeffs;
            self.fixed_base_msm_secondary(builder, bases, scalars)?
        };
        self.constrain_equal_secondary(builder, &out, &g_k)?;

        Ok(())
    }

    pub fn verify_hyrax(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        vp: &MultilinearHyraxParams<C::Secondary>,
        comm: &[(&Vec<EcPoint<C::Scalar, AssignedValue<C::Scalar>>>, ProperCrtUint<C::Scalar>)],
        point: &[ProperCrtUint<C::Scalar>],
        eval: &ProperCrtUint<C::Scalar>,
        transcript: &mut PoseidonTranscriptChip<C>,
    ) -> Result<(), Error> 
    {
        let (lo, hi) = point.split_at(vp.row_num_vars());
        let scalars = self.eq_xy_coeffs(builder, hi)?;

        let comm = comm
            .iter()
            .map(|(comm, rhs)| {
                let scalars = scalars
                    .iter()
                    .map(|lhs| self.mul_base(builder, lhs, rhs))
                    .try_collect::<_, Vec<_>, _>()?;
                Ok::<_, Error>(izip_eq!(*comm, scalars))
            })
            .try_collect::<_, Vec<_>, _>()?
            .into_iter()
            .flatten()
            .collect_vec();
        let comm = comm.iter().map(|(comm, scalar)| (*comm, scalar));

        self.verify_ipa(builder, vp.ipa(), comm, lo, eval, transcript)
    }

    pub fn verify_hyrax_hyperplonk(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        vp: &HyperPlonkVerifierParam<C::Base, MultilinearHyrax<C::Secondary>>,
        instances: Value<&[C::Base]>,
        transcript: &mut PoseidonTranscriptChip<C>,
    ) -> Result<Vec<ProperCrtUint<C::Scalar>>, Error>
    where
        C::Scalar: Serialize + DeserializeOwned ,
        C::Base: Serialize + DeserializeOwned ,
        C::Secondary: Serialize + DeserializeOwned ,
    {
        assert_eq!(vp.num_instances.len(), 1);
        let instances = vec![instances
            .transpose_vec(vp.num_instances[0])
            .into_iter()
            .map(|instance| self.assign_witness_base(builder, instance.copied().assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?];

        transcript.common_field_elements(&instances[0])?;

        let mut witness_comms = Vec::with_capacity(vp.num_witness_polys.iter().sum());
        let mut challenges = Vec::with_capacity(vp.num_challenges.iter().sum::<usize>() + 3);
        for (num_polys, num_challenges) in
            vp.num_witness_polys.iter().zip_eq(vp.num_challenges.iter())
        {
            witness_comms.extend(
                iter::repeat_with(|| transcript.read_commitments(builder, vp.pcs.num_chunks()))
                    .take(*num_polys)
                    .try_collect::<_, Vec<_>, _>()?,
            );
            challenges.extend(
                transcript
                    .squeeze_challenges(builder, *num_challenges)?
                    .iter()
                    .map(AsRef::as_ref)
                    .cloned(),
            );
        }

        let beta = transcript.squeeze_challenge(builder)?.as_ref().clone();

        let lookup_m_comms =
            iter::repeat_with(|| transcript.read_commitments(builder, vp.pcs.num_chunks()))
                .take(vp.num_lookups)
                .try_collect::<_, Vec<_>, _>()?;

        let gamma = transcript.squeeze_challenge(builder)?.as_ref().clone();

        let lookup_h_permutation_z_comms =
            iter::repeat_with(|| transcript.read_commitments(builder, vp.pcs.num_chunks()))
                .take(vp.num_lookups + vp.num_permutation_z_polys)
                .try_collect::<_, Vec<_>, _>()?;

        let alpha = transcript.squeeze_challenge(builder)?.as_ref().clone();
        let y = transcript
            .squeeze_challenges(builder, vp.num_vars)?
            .iter()
            .map(AsRef::as_ref)
            .cloned()
            .collect_vec();

        challenges.extend([beta, gamma, alpha]);

        let zero = self.assign_constant_base(builder, C::Base::ZERO)?;
        let (points, evals) = self.verify_sum_check_and_query(
            builder,
            
            vp.num_vars,
            &vp.expression,
            &zero,
            &instances,
            &challenges,
            &y,
            transcript,
        )?;

        let dummy_comm = vec![
            self.assign_constant_secondary(builder, C::Secondary::identity())?;
            vp.pcs.num_chunks()
        ];
        let preprocess_comms = vp
            .preprocess_comms
            .iter()
            .map(|comm| {
                comm.0
                    .iter()
                    .map(|c| self.assign_constant_secondary(builder, *c))
                    .try_collect::<_, Vec<_>, _>()
            })
            .try_collect::<_, Vec<_>, _>()?;
        let permutation_comms = vp
            .permutation_comms
            .iter()
            .map(|comm| {
                comm.1
                    .0
                    .iter()
                    .map(|c| self.assign_constant_secondary(builder, *c))
                    .try_collect::<_, Vec<_>, _>()
            })
            .try_collect::<_, Vec<_>, _>()?;
        let comms = iter::empty()
            .chain(iter::repeat(dummy_comm).take(vp.num_instances.len()))
            .chain(preprocess_comms)
            .chain(witness_comms)
            .chain(permutation_comms)
            .chain(lookup_m_comms)
            .chain(lookup_h_permutation_z_comms)
            .collect_vec();

        let (comm, point, eval) =
            self.multilinear_pcs_batch_verify(builder,  &comms, &points, &evals, transcript)?;

        self.verify_hyrax(builder, &vp.pcs, &comm, &point, &eval, transcript)?;

        Ok(instances.into_iter().next().unwrap())
    }
}