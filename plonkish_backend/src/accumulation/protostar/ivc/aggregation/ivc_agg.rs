use std::{
    borrow::Cow, collections::{btree_map::Entry, BTreeMap, BTreeSet}, hash::Hash, marker::PhantomData
};

use halo2_base::{
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
    AssignedValue,
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
    accumulation::protostar::{
        ivc::{
            halo2::{
                test::strawman::{Chip, PoseidonTranscriptChip},
                AssignedProtostarAccumulatorInstance, ProtostarAccumulationVerifier,
            },
            ProtostarAccumulationVerifierParam,
        },
        ProtostarAccumulatorInstance,
        ProtostarVerifierParam,
    },
    backend::{
        hyperplonk::{verifier::point_offset, HyperPlonk, HyperPlonkVerifierParam},
        PlonkishBackend,
    },
    pcs::{
        multilinear::{Gemini, MultilinearHyrax, MultilinearHyraxParams, MultilinearIpa, MultilinearIpaParams},
        univariate::{kzg::eval_sets, UnivariateKzg},
        Evaluation,
        PolynomialCommitmentScheme,
    },
    poly::multilinear::{rotation_eval_coeff_pattern, rotation_eval_point_pattern, zip_self},
    util::{
        arithmetic::{barycentric_weights, powers, steps, BooleanHypercube, MultiMillerLoop, TwoChainCurve}, expression::{CommonPolynomial, Expression, Query, Rotation}, izip_eq, BitIndex
    },
};

use core::iter;
use itertools::{chain, izip, Itertools};


#[derive(Debug)]
pub struct ProtostarIvcAggregator<C, Pcs>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
    HyperPlonk<Pcs>: PlonkishBackend<C::Base>,
{
    vp_digest: C::Scalar,
    vp: ProtostarVerifierParam<C::Base, HyperPlonk<Pcs>>,
    arity: usize,
    tcc_chip: Chip<C>,
    hash_chip: Chip<C>,
    _marker: PhantomData<(C, Pcs)>,
}

impl<'a, C, Pcs> ProtostarIvcAggregator<C, Pcs>
where
    C: TwoChainCurve,
    C::ScalarExt: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
    Pcs: PolynomialCommitmentScheme<C::Base>,
    Pcs::Commitment: AsRef<C::Secondary>,
    HyperPlonk<Pcs>:
        PlonkishBackend<C::Base, VerifierParam = HyperPlonkVerifierParam<C::Base, Pcs>>,
{
    pub fn new(
        vp_digest: C::Scalar,
        vp: ProtostarVerifierParam<C::Base, HyperPlonk<Pcs>>,
        arity: usize,
        tcc_chip: Chip<C>,
        hash_chip: Chip<C>,
    ) -> Self {
        Self {
            vp_digest,
            vp,
            arity,
            tcc_chip,
            hash_chip,
            _marker: PhantomData,
        }
    }

    #[allow(clippy::type_complexity)]
    fn hash_state(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        num_steps: Value<usize>,
        initial_input: Value<Vec<C::Scalar>>,
        output: Value<Vec<C::Scalar>>,
        acc: &AssignedProtostarAccumulatorInstance<
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        >,
    ) -> Result<
        (
            AssignedValue<C::Scalar>,
            Vec<AssignedValue<C::Scalar>>,
            Vec<AssignedValue<C::Scalar>>,
            AssignedValue<C::Scalar>,
        ),
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let hash_chip = &self.hash_chip;

        let vp_digest = tcc_chip.assign_constant(builder, self.vp_digest)?;
        let num_steps = tcc_chip.assign_witness(
            builder,
            (num_steps.map(|num_steps| C::Scalar::from(num_steps as u64))).assign().unwrap(),
        )?;
        let initial_input = initial_input
            .transpose_vec(self.arity)
            .into_iter()
            .map(|input| tcc_chip.assign_witness(builder, input.assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;
        let output = output
            .transpose_vec(self.arity)
            .into_iter()
            .map(|input| tcc_chip.assign_witness(builder, input.assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;
        let h = hash_chip.hash_assigned_state(
            builder,
            &vp_digest,
            &num_steps,
            &initial_input,
            &output,
            acc,
        )?;

        Ok((num_steps, initial_input, output, h))
    }

    #[allow(clippy::type_complexity)]
    fn reduce_decider_inner(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        >,
        transcript: &mut PoseidonTranscriptChip<C>,
    ) -> Result<
        (
            Vec<EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
            Vec<Vec<ProperCrtUint<C::Scalar>>>,
            Vec<Evaluation<ProperCrtUint<C::Scalar>>>,
        ),
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let vp = &self.vp.vp;

        transcript.absorb_accumulator(acc)?;

        let beta = transcript.squeeze_challenge(builder)?;
        let gamma = transcript.squeeze_challenge(builder)?;

        let permutation_z_comms =
            transcript.read_commitments(builder, vp.num_permutation_z_polys)?;

        let alpha = transcript.squeeze_challenge(builder)?;
        let y = transcript.squeeze_challenges(builder, vp.num_vars)?;

        let challenges = chain![
            &acc.challenges,
            [&acc.u],
            [&beta, &gamma, &alpha].map(AsRef::as_ref)
        ]
        .cloned()
        .collect_vec();
        let y = y.iter().map(AsRef::as_ref).cloned().collect_vec();

        let claimed_sum = if let Some(compressed_e_sum) = acc.compressed_e_sum.as_ref() {
            Cow::Borrowed(compressed_e_sum)
        } else {
            Cow::Owned(tcc_chip.assign_constant_base(builder, C::Base::ZERO)?)
        };
        let (points, evals) = tcc_chip.verify_sum_check_and_query(
            builder,
            self.vp.vp.num_vars,
            &self.vp.vp.expression,
            &claimed_sum,
            acc.instances(),
            &challenges,
            &y,
            transcript,
        )?;

        let builtin_witness_poly_offset = vp.num_witness_polys.iter().sum::<usize>();
        let dummy_comm = tcc_chip.assign_constant_secondary(builder, C::Secondary::identity())?;
        let preprocess_comms = vp
            .preprocess_comms
            .iter()
            .map(|comm| tcc_chip.assign_constant_secondary(builder, *comm.as_ref()))
            .try_collect::<_, Vec<_>, _>()?;
        let permutation_comms = vp
            .permutation_comms
            .iter()
            .map(|(_, comm)| tcc_chip.assign_constant_secondary(builder, *comm.as_ref()))
            .try_collect::<_, Vec<_>, _>()?;
        let comms = chain![
            iter::repeat(&dummy_comm)
                .take(vp.num_instances.len())
                .cloned(),
            preprocess_comms,
            acc.witness_comms[..builtin_witness_poly_offset]
                .iter()
                .cloned(),
            permutation_comms,
            acc.witness_comms[builtin_witness_poly_offset..]
                .iter()
                .cloned(),
            permutation_z_comms,
            [acc.e_comm.clone()]
        ]
        .collect_vec();
        Ok((comms, points, evals))
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    pub fn reduce_decider(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        num_steps: Value<usize>,
        initial_input: Value<Vec<C::Scalar>>,
        output: Value<Vec<C::Scalar>>,
        acc: Value<ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
        transcript: &mut PoseidonTranscriptChip<C>,
    ) -> Result<
        (
            AssignedValue<C::Scalar>,
            Vec<AssignedValue<C::Scalar>>,
            Vec<AssignedValue<C::Scalar>>,
            AssignedValue<C::Scalar>,
            Vec<EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
            Vec<Vec<ProperCrtUint<C::Scalar>>>,
            Vec<Evaluation<ProperCrtUint<C::Scalar>>>,
        ),
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let avp = ProtostarAccumulationVerifierParam::from(&self.vp);
        let acc_verifier = ProtostarAccumulationVerifier::new(avp, tcc_chip.clone());

        let acc = acc_verifier.assign_accumulator(builder, acc.as_ref())?;

        let (num_steps, initial_input, output, h) =
            self.hash_state(builder, num_steps, initial_input, output, &acc)?;

        let (comms, points, evals) = self.reduce_decider_inner(builder,  &acc, transcript)?;

        Ok((num_steps, initial_input, output, h, comms, points, evals))
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    pub fn reduce_decider_with_last_nark(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        num_steps: Value<usize>,
        initial_input: Value<Vec<C::Scalar>>,
        output: Value<Vec<C::Scalar>>,
        acc_before_last: Value<ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
        last_instance: Value<[C::Base; 2]>,
        transcript: &mut PoseidonTranscriptChip<C>,
    ) -> Result<
        (
            AssignedValue<C::Scalar>,
            Vec<AssignedValue<C::Scalar>>,
            Vec<AssignedValue<C::Scalar>>,
            Vec<EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
            Vec<Vec<ProperCrtUint<C::Scalar>>>,
            Vec<Evaluation<ProperCrtUint<C::Scalar>>>,
            AssignedValue<C::Scalar>,
        ),
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let avp = ProtostarAccumulationVerifierParam::from(&self.vp);
        let acc_verifier = ProtostarAccumulationVerifier::new(avp, tcc_chip.clone());

        let acc_before_last =
            acc_verifier.assign_accumulator(builder, acc_before_last.as_ref())?;
        let (last_nark, _, acc) = {
            let instances = last_instance
                .as_ref()
                .map(|instances| [&instances[0], &instances[1]])
                .transpose_array();
            acc_verifier.verify_accumulation_from_nark(
                builder,
                &acc_before_last,
                instances,
                transcript,
            )?
        };

        let (num_steps, initial_input, output, h) =
            self.hash_state(builder, num_steps, initial_input, output, &acc_before_last)?;

        let h_from_last_nark = tcc_chip.fit_base_in_scalar(builder, &last_nark.instances[0][0])?;
        let h_ohs_from_last_nark =
            tcc_chip.fit_base_in_scalar(builder,&last_nark.instances[0][1])?;
        tcc_chip.constrain_equal(builder, &h, &h_from_last_nark)?;

        let (comms, points, evals) = self.reduce_decider_inner(builder,  &acc, transcript)?;

        Ok((
            num_steps,
            initial_input,
            output,
            comms,
            points,
            evals,
            h_ohs_from_last_nark,
        ))
    }
}



impl<C, M> ProtostarIvcAggregator<C, Gemini<UnivariateKzg<M>>>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
    M: MultiMillerLoop<Scalar = C::Base, G1Affine = C::Secondary>,
    M::G1Affine: Serialize + DeserializeOwned,
    M::G2Affine: Serialize + DeserializeOwned,
    M::Scalar: Hash + Serialize + DeserializeOwned,
{
    #[allow(clippy::type_complexity)]
    pub fn aggregate_gemini_kzg_ivc(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        num_steps: Value<usize>,
        initial_input: Value<Vec<C::Scalar>>,
        output: Value<Vec<C::Scalar>>,
        acc: Value<ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
        transcript: &mut PoseidonTranscriptChip<C>,
    ) -> Result<
        (
            AssignedValue<C::Scalar>,
            Vec<AssignedValue<C::Scalar>>,
            Vec<AssignedValue<C::Scalar>>,
            AssignedValue<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        ),
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let (num_steps, initial_input, output, h, comms, points, evals) =
            self.reduce_decider(builder, num_steps, initial_input, output, acc, transcript)?;
        let (comm, point, eval) =
            tcc_chip.multilinear_pcs_batch_verify(builder, &comms, &points, &evals, transcript)?;

        let (fs, points, evals) = {
            let num_vars = point.len();
            let fs = transcript.read_commitments(builder, num_vars - 1)?;

            let beta = transcript.squeeze_challenge(builder)?;
            let squares_of_beta = tcc_chip.squares_base(builder, beta.as_ref(), num_vars)?;

            let evals = transcript.read_field_elements(builder, num_vars)?;

            let one = tcc_chip.assign_constant_base(builder, C::Base::ONE)?;
            let two = tcc_chip.assign_constant_base(builder, C::Base::ONE.double())?;
            let eval_0 = evals.iter().zip(&squares_of_beta).zip(&point).rev().fold(
                Ok::<_, Error>(eval),
                |eval_pos, ((eval_neg, sqaure_of_beta), x_i)| {
                    let eval_pos = eval_pos?;
                    let mut tmp = tcc_chip.sub_base(builder, &one, x_i)?;
                    tmp = tcc_chip.mul_base(builder, &tmp, sqaure_of_beta)?;
                    let numer = {
                        let mut numer_lhs = tcc_chip.mul_base(builder, &two, sqaure_of_beta)?;
                        numer_lhs = tcc_chip.mul_base(builder, &numer_lhs, &eval_pos)?;
                        let mut numer_rhs = tcc_chip.sub_base(builder, &tmp, x_i)?;
                        numer_rhs = tcc_chip.mul_base(builder, &numer_rhs, eval_neg)?;
                        tcc_chip.sub_base(builder, &numer_lhs, &numer_rhs)?
                    };
                    let denom = tcc_chip.add_base(builder, &tmp, x_i)?;
                    tcc_chip.div_incomplete_base(builder, &numer, &denom)
                },
            )?;

            let evals = chain!([(0, 0), (0, 1)], (1..num_vars).zip(2..))
                .zip(chain![[eval_0], evals])
                .map(|((idx, point), eval)| Evaluation::new(idx, point, eval))
                .collect_vec();
            let points = chain![
                [squares_of_beta[0].clone()],
                squares_of_beta
                    .iter()
                    .map(|sqaure_of_beta| tcc_chip.neg_base(builder, sqaure_of_beta))
                    .try_collect::<_, Vec<_>, _>()?
            ]
            .collect_vec();

            (fs, points, evals)
        };

        let (sets, superset) = eval_sets(&evals);

        let beta = transcript.squeeze_challenge(builder)?;
        let gamma = transcript.squeeze_challenge(builder)?;

        let q = transcript.read_commitment(builder)?;

        let z = transcript.squeeze_challenge(builder)?;

        let max_set_len = sets.iter().map(|set| set.polys.len()).max().unwrap();
        let powers_of_beta = tcc_chip.powers_base(builder, beta.as_ref(), max_set_len)?;
        let powers_of_gamma = tcc_chip.powers_base(builder, gamma.as_ref(), sets.len())?;

        let vanishing_diff_evals = sets
            .iter()
            .map(|set| {
                let diffs = set
                    .diffs
                    .iter()
                    .map(|idx| tcc_chip.sub_base(builder, z.as_ref(), &points[*idx]))
                    .try_collect::<_, Vec<_>, _>()?;
                tcc_chip.product_base(builder, &diffs)
            })
            .try_collect::<_, Vec<_>, _>()?;
        let normalizer = tcc_chip.invert_incomplete_base(builder, &vanishing_diff_evals[0])?;
        let normalized_scalars = izip_eq!(&powers_of_gamma, &vanishing_diff_evals)
            .map(|(power_of_gamma, vanishing_diff_eval)| {
                tcc_chip.product_base(builder, [&normalizer, vanishing_diff_eval, power_of_gamma])
            })
            .try_collect::<_, Vec<_>, _>()?;
        let superset_eval = {
            let diffs = superset
                .iter()
                .map(|idx| tcc_chip.sub_base(builder, z.as_ref(), &points[*idx]))
                .try_collect::<_, Vec<_>, _>()?;
            tcc_chip.product_base(builder, &diffs)?
        };
        let q_scalar = {
            let neg_superset_eval = tcc_chip.neg_base(builder, &superset_eval)?;
            tcc_chip.mul_base(builder, &neg_superset_eval, &normalizer)?
        };
        let comm_scalars = sets.iter().zip(&normalized_scalars).fold(
            Ok::<_, Error>(vec![
                tcc_chip
                    .assign_constant_base(builder, C::Base::ZERO)?;
                fs.len() + 1
            ]),
            |scalars, (set, coeff)| {
                let mut scalars = scalars?;
                for (poly, power_of_beta) in izip!(&set.polys, &powers_of_beta) {
                    let scalar = tcc_chip.mul_base(builder, coeff, power_of_beta)?;
                    scalars[*poly] = tcc_chip.add_base(builder, &scalars[*poly], &scalar)?;
                }
                Ok(scalars)
            },
        )?;
        let r_evals = sets
            .iter()
            .map(|set| {
                let points = set
                    .points
                    .iter()
                    .map(|idx| points[*idx].clone())
                    .collect_vec();
                let weights = tcc_chip.barycentric_weights(builder, &points)?;
                let r_evals = set
                    .evals
                    .iter()
                    .map(|evals| {
                        tcc_chip.barycentric_interpolate(
                            builder,
                            &weights,
                            &points,
                            evals,
                            z.as_ref(),
                        )
                    })
                    .try_collect::<_, Vec<_>, _>()?;
                tcc_chip.inner_product_base(builder, &powers_of_beta[..r_evals.len()], &r_evals)
            })
            .try_collect::<_, Vec<_>, _>()?;
        let eval = tcc_chip.inner_product_base(builder, &normalized_scalars, &r_evals)?;
        let pi = transcript.read_commitment(builder)?;

        let pi_scalar = z.as_ref().clone();
        let g_scalar = tcc_chip.neg_base(builder, &eval)?;

        let g = tcc_chip.assign_constant_secondary(builder, self.vp.vp.pcs.g1())?;
        let (mut bases, mut scalars) = comm.into_iter().unzip::<_, _, Vec<_>, Vec<_>>();

        scalars.extend(chain![comm_scalars.into_iter().skip(1),[q_scalar, pi_scalar, g_scalar]]);
        bases.extend(chain![&fs, [&q, &pi, &g]]);

        let deref_bases = bases.iter().map(|&x| x.clone()).collect_vec();
        let lhs = tcc_chip.variable_base_msm_secondary(builder, &deref_bases, scalars)?;
        let rhs = pi;

        Ok((num_steps, initial_input, output, h, lhs, rhs))
    }
}

impl<C>
    ProtostarIvcAggregator<C, MultilinearIpa<C::Secondary>>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Secondary: Serialize + DeserializeOwned,
    C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
{
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    pub fn verify_ipa_grumpkin_ivc_with_last_nark(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        num_steps: Value<usize>,
        initial_input: Value<Vec<C::Scalar>>,
        output: Value<Vec<C::Scalar>>,
        acc_before_last: Value<ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
        last_instance: Value<[C::Base; 2]>,
        transcript: &mut PoseidonTranscriptChip<C>,
    ) -> Result<
        (
            AssignedValue<C::Scalar>,
            Vec<AssignedValue<C::Scalar>>,
            Vec<AssignedValue<C::Scalar>>,
            AssignedValue<C::Scalar>,
        ),
        Error,
    > 
    {
        let tcc_chip = &self.tcc_chip;
        let (num_steps, initial_input, output, comms, points, evals, h_ohs_from_last_nark) = self
            .reduce_decider_with_last_nark(
            builder,
            num_steps,
            initial_input,
            output,
            acc_before_last,
            last_instance,
            transcript,
        )?;
        let (comm, point, eval) =
            tcc_chip.multilinear_pcs_batch_verify(builder,  &comms, &points, &evals, transcript)?;
        let comm = comm.iter().map(|(comm, scalar)| (*comm, scalar));

        tcc_chip.verify_ipa(builder, &self.vp.vp.pcs, comm, &point, &eval, transcript)?;

        Ok((num_steps, initial_input, output, h_ohs_from_last_nark))
    }
}