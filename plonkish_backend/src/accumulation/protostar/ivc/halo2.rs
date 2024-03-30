use crate::{
    accumulation::{
        protostar::{
            ivc::{ProtostarAccumulationVerifierParam, cyclefold::{CycleFoldCircuit, self, CF_IO_LEN}, halo2::test::strawman::PoseidonTranscriptChip},
            PlonkishNarkInstance, Protostar, ProtostarAccumulator, ProtostarAccumulatorInstance,
            ProtostarProverParam,
            ProtostarStrategy::{Compressing, NoCompressing},
            ProtostarVerifierParam,
        },
        AccumulationScheme,
    },
    backend::{
        hyperplonk::{verifier::point_offset, HyperPlonk, HyperPlonkVerifierParam},
        PlonkishBackend, PlonkishCircuit
    },
    frontend::halo2::{Halo2Circuit, CircuitExt},
    pcs::{
        multilinear::{
            Gemini, MultilinearHyrax, MultilinearHyraxParams, MultilinearIpa, MultilinearIpaParams,
        },
        univariate::{kzg::eval_sets, UnivariateKzg},
        AdditiveCommitment, Evaluation, PolynomialCommitmentScheme,
    },
    poly::multilinear::{
        rotation_eval_coeff_pattern, rotation_eval_point_pattern, zip_self, MultilinearPolynomial,
    },
    util::{
        arithmetic::{
            barycentric_weights, fe_to_fe, fe_truncated_from_le_bytes, powers, steps, CurveAffine,
            BooleanHypercube, Field, MultiMillerLoop, PrimeCurveAffine, PrimeField, TwoChainCurve, OverridenCurveAffine
        },
        chain, end_timer,
        expression::{CommonPolynomial, Expression, Query, Rotation},
        hash::{Hash as _, Keccak256},
        izip, izip_eq, start_timer,
        transcript::{InMemoryTranscript, TranscriptRead, TranscriptWrite},
        BitIndex, DeserializeOwned, Itertools, Serialize,
    },
};

use std::{
    borrow::{Borrow, BorrowMut, Cow},
    collections::{btree_map::Entry, BTreeMap, HashMap, BTreeSet},
    fmt::Debug,
    hash::Hash,
    iter::{self, once},
    marker::PhantomData,
    mem,
    rc::Rc, time::Instant,
};

use poseidon::Spec;
use rand::RngCore;
use std::cell::RefCell;

use halo2_base::{
    Context,
    gates::{
        circuit::{builder::{RangeCircuitBuilder, BaseCircuitBuilder, self},
        CircuitBuilderStage, BaseCircuitParams, BaseConfig},
        flex_gate::{GateChip, GateInstructions, threads::SinglePhaseCoreManager}, RangeChip,
    },
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
    QuantumCell::{Constant, Existing, Witness, WitnessFraction},
    AssignedValue,
    poseidon::hasher::{PoseidonSponge, PoseidonHasher, spec::OptimizedPoseidonSpec, PoseidonHash}, 
    halo2_proofs::dev::MockProver, virtual_region::copy_constraints::SharedCopyConstraintManager,
};

use halo2_ecc::{
    fields::native_fp::NativeFieldChip,
    fields::fp::FpChip,
    ecc::{EccChip, EcPoint}, bigint::{ProperCrtUint, ProperUint},
};

use halo2_base::halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Circuit, Selector, Error, ConstraintSystem},
};

use halo2_base::halo2_proofs::halo2curves::{
    bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta},
    group::{
        ff::{FromUniformBytes, PrimeFieldBits},
        Curve, Group
    },
    Coordinates, CurveExt,
};

pub mod test;
use test::strawman::{self, T, RANGE_BITS, RATE, NUM_CHALLENGE_BITS, NUM_LIMBS, NUM_LIMB_BITS, R_F, R_P, SECURE_MDS, Chip};

use self::test::strawman::{PoseidonNativeTranscriptChip, fe_from_limbs};

pub const NUM_INSTANCES: usize = 1;

pub type AssignedCycleFoldInputsInPrimary<Assigned, AssignedSecondary> =
    CycleFoldInputsInPrimary<Assigned, AssignedSecondary>;
    
#[derive(Debug, Clone)]
pub struct CycleFoldInputsInPrimary<F, C> 
{   
    pub r: F,
    pub nark_witness_comms: Vec<C>,
    pub cross_term_comms: Vec<C>,
    pub acc_witness_comms: Vec<C>,
    pub acc_e_comm: C,
    pub acc_prime_witness_comms: Vec<C>,
    pub acc_prime_e_comm: C,
}

type AssignedPlonkishNarkInstance<AssignedBase, AssignedSecondary> =
    PlonkishNarkInstance<AssignedBase, AssignedSecondary>;

type AssignedProtostarAccumulatorInstance<AssignedBase, AssignedSecondary> =
    ProtostarAccumulatorInstance<AssignedBase, AssignedSecondary>;


pub trait StepCircuit<C: TwoChainCurve>: Clone + Debug + CircuitExt<C::Scalar> 
where
    C::Scalar: BigPrimeField,
    C::Base: BigPrimeField,
{   

    fn arity() -> usize;
    
    fn initial_input(&self) -> &[C::Scalar];

    fn setup(&mut self) -> C::Scalar;

    fn input(&self) -> &[C::Scalar];

    fn set_input(&mut self, input: &[C::Scalar]);

    fn output(&self) -> &[C::Scalar];

    fn set_output(&mut self, output: &[C::Scalar]);

    fn next_output(&self) -> Vec<C::Scalar>;

    fn step_idx(&self) -> usize;

    fn next(&mut self);

    fn num_constraints(&self) -> usize;

    #[allow(clippy::type_complexity)]
    fn synthesize(
        &mut self,
        config: BaseConfig<C::Scalar>,
        layouter: impl Layouter<C::Scalar>,
        builder: &mut BaseCircuitBuilder<C::Scalar>,
    ) -> Result<
        (
            Vec<AssignedValue<C::Scalar>>,
            Vec<AssignedValue<C::Scalar>>,
        ),
        Error,
    >;
}

pub struct ProtostarAccumulationVerifier<C: TwoChainCurve> 
where
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    avp: ProtostarAccumulationVerifierParam<C::Scalar>,
    tcc_chip: Chip<C>,
    _marker: PhantomData<C>,
}

impl<C> ProtostarAccumulationVerifier<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    pub fn new(avp: ProtostarAccumulationVerifierParam<C::Scalar>, tcc_chip: Chip<C>) -> Self {
        Self {
            avp,
            tcc_chip,
            _marker: PhantomData,
        }
    }

    pub fn assign_default_accumulator(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<
        AssignedValue<C::Scalar>, 
        EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>,
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let ProtostarAccumulationVerifierParam { num_instances, .. } = &self.avp;

        let instances = num_instances
            .iter()
            .map(|num_instances| {
                iter::repeat_with(|| tcc_chip.assign_constant(builder, C::Scalar::ZERO))
                    .take(*num_instances)
                    .try_collect::<_, Vec<_>, _>()
            })
            .try_collect::<_, Vec<_>, _>()?;
        let witness_comms = iter::repeat_with(|| {
            tcc_chip.assign_constant_primary_non_native(builder, C::identity())
            }).take(self.avp.num_folding_witness_polys())
            .try_collect::<_, Vec<_>, _>()?;
        let challenges =
            iter::repeat_with(|| tcc_chip.assign_constant(builder, C::Scalar::ZERO))
                .take(self.avp.num_folding_challenges())
                .try_collect::<_, Vec<_>, _>()?;
        let u = tcc_chip.assign_constant(builder, C::Scalar::ZERO)?;
        let e_comm = tcc_chip.assign_constant_primary_non_native(builder, C::identity())?;
        let compressed_e_sum = match self.avp.strategy {
            NoCompressing => None,
            Compressing => Some(tcc_chip.assign_constant(builder, C::Scalar::ZERO)?),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }

    pub fn assign_default_accumulator_ec(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<
        ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let ProtostarAccumulationVerifierParam { num_instances, .. } = &self.avp;

        let instances = num_instances
            .iter()
            .map(|num_instances| {
                iter::repeat_with(|| tcc_chip.assign_constant_base(builder, C::Base::ZERO))
                    .take(*num_instances)
                    .try_collect::<_, Vec<_>, _>()
            })
            .try_collect::<_, Vec<_>, _>()?;
        let witness_comms = iter::repeat_with(|| {
            tcc_chip.assign_constant_primary(builder, C::Secondary::identity())
        })
        .take(self.avp.num_folding_witness_polys())
        .try_collect::<_, Vec<_>, _>()?;
        let challenges =
            iter::repeat_with(|| tcc_chip.assign_constant_base(builder, C::Base::ZERO))
                .take(self.avp.num_folding_challenges())
                .try_collect::<_, Vec<_>, _>()?;
        let u = tcc_chip.assign_constant_base(builder, C::Base::ZERO)?;
        let e_comm = tcc_chip.assign_constant_primary(builder, C::Secondary::identity())?;
        let compressed_e_sum = match self.avp.strategy {
            NoCompressing => None,
            Compressing => Some(tcc_chip.assign_constant_base(builder, C::Base::ZERO)?),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }

    pub fn assign_comm_outputs_from_accumulator(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: Value<&ProtostarAccumulatorInstance<C::Scalar, C>>,
    ) -> Result<Vec<EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>, Error > {
        let tcc_chip = &self.tcc_chip;
        let avp = &self.avp;
        let witness_comms = acc
            .map(|acc| &acc.witness_comms)
            .transpose_vec(avp.num_folding_witness_polys())
            .into_iter()
            .map(|witness_comm| tcc_chip.assign_witness_primary_non_native(builder, witness_comm.copied().assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;
        let e_comm = tcc_chip.assign_witness_primary_non_native(builder, 
            acc.map(|acc| acc.e_comm).assign().unwrap())?;
        let mut assigned_comm = witness_comms.clone();
        assigned_comm.push(e_comm);
        Ok(assigned_comm)
    }

    pub fn assign_accumulator(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: Value<&ProtostarAccumulatorInstance<C::Scalar, C>>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<
        AssignedValue<C::Scalar>, EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>,
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let avp = &self.avp;
        let instances = avp
            .num_instances
            .iter()
            .zip(
                acc.map(|acc| &acc.instances)
                    .transpose_vec(avp.num_instances.len()),
            )
            .map(|(num_instances, instances)| {
                instances
                    .transpose_vec(*num_instances)
                    .into_iter()
                    .map(|instance| tcc_chip.assign_witness(builder, instance.copied().assign().unwrap()))
                    .try_collect::<_, Vec<_>, _>()
            }).try_collect::<_, Vec<_>, _>()?;
        
        let witness_comms = acc
            .map(|acc| &acc.witness_comms)
            .transpose_vec(avp.num_folding_witness_polys())
            .into_iter()
            .map(|witness_comm| tcc_chip.assign_witness_primary_non_native(builder, witness_comm.copied().assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;

        let challenges = acc
            .map(|acc| &acc.challenges)
            .transpose_vec(avp.num_folding_challenges())
            .into_iter()
            .map(|challenge| tcc_chip.assign_witness(builder, challenge.copied().assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;

        let u = tcc_chip.assign_witness(builder, acc.map(|acc| &acc.u).copied().assign().unwrap())?;
        let e_comm = tcc_chip.assign_witness_primary_non_native(builder, 
            acc.map(|acc| acc.e_comm).assign().unwrap())?;
        let compressed_e_sum = match avp.strategy {
            NoCompressing => None,
            Compressing => Some(
                tcc_chip
                    .assign_witness(builder, (acc.map(|acc| acc.compressed_e_sum.unwrap())).assign().unwrap())?,
            ),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }

    pub fn assign_accumulator_ec(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: Value<&ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<ProperCrtUint<C::Scalar>, 
        EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let avp = &self.avp;
        let instances = avp
            .num_instances
            .iter()
            .zip(
                acc.map(|acc| &acc.instances)
                    .transpose_vec(avp.num_instances.len()),
            )
            .map(|(num_instances, instances)| {
                instances
                    .transpose_vec(*num_instances)
                    .into_iter()
                    .map(|instance| tcc_chip.assign_witness_base(builder, instance.copied().assign().unwrap()))
                    .try_collect::<_, Vec<_>, _>()
            }).try_collect::<_, Vec<_>, _>()?;
        
        let witness_comms = acc
            .map(|acc| &acc.witness_comms)
            .transpose_vec(avp.num_folding_witness_polys())
            .into_iter()
            .map(|witness_comm| tcc_chip.assign_witness_primary(builder, witness_comm.copied().assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;

        let challenges = acc
            .map(|acc| &acc.challenges)
            .transpose_vec(avp.num_folding_challenges())
            .into_iter()
            .map(|challenge| tcc_chip.assign_witness_base(builder, challenge.copied().assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;

        let u = tcc_chip.assign_witness_base(builder, acc.map(|acc| &acc.u).copied().assign().unwrap())?;
        let e_comm = tcc_chip.assign_witness_primary(builder, acc.map(|acc| acc.e_comm).assign().unwrap())?;
        let compressed_e_sum = match avp.strategy {
            NoCompressing => None,
            Compressing => Some(
                tcc_chip
                    .assign_witness_base(builder, (acc.map(|acc| acc.compressed_e_sum.unwrap())).assign().unwrap())?,
            ),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }

    #[allow(clippy::type_complexity)]
    pub fn verify_accumulation_from_nark(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            AssignedValue<C::Scalar>,
            EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
        >,
        instances: [Value<&C::Scalar>; NUM_INSTANCES],
        transcript: &mut PoseidonNativeTranscriptChip<C>,
        assigned_acc_prime_comms_checked: Vec<EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>,
        // cyclefold_instances: [Value<&C::Base>; CF_IO_LEN],
    ) -> Result<
        (
            AssignedPlonkishNarkInstance<AssignedValue<C::Scalar>, EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>,
            AssignedProtostarAccumulatorInstance<AssignedValue<C::Scalar>, EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>,
        ),
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let ProtostarAccumulationVerifierParam {
            strategy,
            num_witness_polys,
            num_challenges,
            num_cross_terms,
            ..
        } = &self.avp;
        let instances = instances
            .into_iter()
            .map(|instance| tcc_chip.assign_witness(builder, instance.copied().assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;
        for instance in instances.iter() {
            transcript.common_field_element(instance)?;
        }

        let mut witness_comms = Vec::with_capacity(self.avp.num_folding_witness_polys());
        let mut challenges = Vec::with_capacity(self.avp.num_folding_challenges());
        for (num_witness_polys, num_powers_of_challenge) in
            num_witness_polys.iter().zip_eq(num_challenges.iter())
        {
            witness_comms.extend(transcript.read_commitments(builder, *num_witness_polys)?);
            for num_powers in num_powers_of_challenge.iter() {
                let challenge = transcript.squeeze_challenge(builder)?;
                let powers_of_challenges =
                    tcc_chip.powers(builder, challenge.as_ref(), *num_powers + 1)?;
                challenges.extend(powers_of_challenges.into_iter().skip(1));
            }
        }

        let nark = PlonkishNarkInstance::new(vec![instances], challenges, witness_comms);
        transcript.absorb_accumulator(acc)?;

        let (cross_term_comms, compressed_cross_term_sums) = match strategy {
            NoCompressing => {
                let cross_term_comms = transcript.read_commitments(builder, *num_cross_terms)?;

                (cross_term_comms, None)
            }
            Compressing => {
                let zeta_cross_term_comm = vec![transcript.read_commitment(builder)?];
                let compressed_cross_term_sums =
                    transcript.read_field_elements(builder, *num_cross_terms)?;
                (zeta_cross_term_comm, Some(compressed_cross_term_sums))
            }
        };

        let r = transcript.squeeze_challenge(builder)?;
        let r_le_bits = transcript.challenge_to_le_bits(&r)?;
    

        let acc_prime = self.fold_accumulator_from_nark(
            builder,
            acc,
            &nark,
            &cross_term_comms,
            compressed_cross_term_sums.as_deref(),
            r.as_ref(),
            &r_le_bits,
            assigned_acc_prime_comms_checked,
        )?;

        Ok((nark, acc_prime))
    }

    pub fn assign_cyclefold_instances_acc_prime(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        cyclefold_instances: [Value<&C::Base>; CF_IO_LEN]
    ) -> Result<Vec<EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>, Error> 
    {
        let tcc_chip = &self.tcc_chip;
        let avp = &self.avp;
        let num_witness_comms = avp.num_folding_witness_polys();

        let coordinates = cyclefold_instances[1..]
            .iter()
            .map(|input| input.copied().assign().unwrap())
            .collect_vec();

        let assigned_comms = coordinates.chunks(2).map(|chunk| {
            tcc_chip.assign_witness_primary_non_native(builder, C::from_xy(chunk[0], chunk[1]).unwrap()).unwrap()
        }).collect_vec();

        Ok(assigned_comms)
    }

    #[allow(clippy::type_complexity)]
    pub fn verify_accumulation_from_nark_ec(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        >,
        instances: [Value<&C::Base>; CF_IO_LEN], 
        transcript: &mut PoseidonTranscriptChip<C>,
    ) -> Result<
        (
            AssignedPlonkishNarkInstance<ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
            AssignedProtostarAccumulatorInstance<ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        ),
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let ProtostarAccumulationVerifierParam {
            strategy,
            num_witness_polys,
            num_challenges,
            num_cross_terms,
            ..
        } = &self.avp;
        assert!(instances.len() == CF_IO_LEN);
        let instances = instances
            .into_iter()
            .map(|instance| tcc_chip.assign_witness_base(builder, instance.copied().assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;
        for instance in instances.iter() {
            transcript.common_field_element(instance)?;
        }

        let witness_comm_len = self.avp.num_folding_witness_polys();
        let challenges_len = self.avp.num_folding_challenges();
        let mut witness_comms = Vec::with_capacity(witness_comm_len);
        let mut challenges: Vec<ProperCrtUint<C::Scalar>> = Vec::with_capacity(challenges_len);

        for i in 0..witness_comm_len {
            witness_comms.extend(transcript.read_commitments(builder, 1)?);

            if i != challenges_len {
                let challenge = transcript.squeeze_challenge(builder)?;
                challenges.push(challenge.as_ref().clone());
            }
        }

        let nark = AssignedPlonkishNarkInstance::new(vec![instances], challenges, witness_comms);
        transcript.absorb_accumulator(acc)?;

        let (cross_term_comms, compressed_cross_term_sums) = match strategy {
            NoCompressing => {
                let cross_term_comms = 
                transcript.read_commitments(builder, *num_cross_terms)?;
                (cross_term_comms, None)
            }
            Compressing => {
                let zeta_cross_term_comm = vec![transcript.read_commitment(builder)?];
                let compressed_cross_term_sums =
                    transcript.read_field_elements(builder, *num_cross_terms)?;
                (zeta_cross_term_comm, Some(compressed_cross_term_sums))
            }
        };

        let r = transcript.squeeze_challenge(builder)?;
        let r_le_bits = r.le_bits.clone();

        let acc_prime = self.fold_accumulator_from_nark_ec(
            builder,
            acc,
            &nark,
            &cross_term_comms,
            compressed_cross_term_sums.as_deref(),
            r.as_ref(),
            &r_le_bits,
        )?;

        Ok((nark, acc_prime))
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    fn fold_accumulator_from_nark(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            AssignedValue<C::Scalar>,
            EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
        >,
        nark: &AssignedPlonkishNarkInstance<
            AssignedValue<C::Scalar>, 
            EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>,
        cross_term_comms: &[EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>],
        compressed_cross_term_sums: Option<&[AssignedValue<C::Scalar>]>,
        r: &AssignedValue<C::Scalar>,
        r_le_bits: &[AssignedValue<C::Scalar>],
        assigned_cyclefold_instances: Vec<EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<
        AssignedValue<C::Scalar>, EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>,
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let ProtostarAccumulationVerifierParam {
            strategy,
            num_cross_terms,
            ..
        } = self.avp;

        let powers_of_r = tcc_chip.powers(builder, r, num_cross_terms + 1)?;

        // skip folding witness_comms
        let r_nark_instances = nark
            .instances
            .iter()
            .map(|instances| {
                instances
                    .iter()
                    .map(|instance| tcc_chip.mul(builder, r, instance))
                    .try_collect::<_, Vec<_>, _>()
            })
            .try_collect::<_, Vec<_>, _>()?;
        let r_nark_challenges = nark
            .challenges
            .iter()
            .map(|challenge| tcc_chip.mul(builder, r, challenge))
            .try_collect::<_, Vec<_>, _>()?;

        let acc_prime = {
            let instances = izip_eq!(&acc.instances, &r_nark_instances)
                .map(|(lhs, rhs)| {
                    izip_eq!(lhs, rhs)
                        .map(|(lhs, rhs)| tcc_chip.add(builder, lhs, rhs))
                        .try_collect::<_, Vec<_>, _>()
                })
                .try_collect::<_, Vec<_>, _>()?;
            let witness_comms = assigned_cyclefold_instances[..assigned_cyclefold_instances.len() - 1].to_vec();
            let challenges = izip_eq!(&acc.challenges, &r_nark_challenges)
                .map(|(lhs, rhs)| tcc_chip.add(builder, lhs, rhs))
                .try_collect::<_, Vec<_>, _>()?;
            let u = tcc_chip.add(builder, &acc.u, r)?;
            let e_comm = if cross_term_comms.is_empty() {
                acc.e_comm.clone()
            } else {
                assigned_cyclefold_instances.last().unwrap().clone()
            };
            let compressed_e_sum = match strategy {
                NoCompressing => None,
                Compressing => {
                    let rhs = tcc_chip.inner_product(
                        builder,
                        &powers_of_r[1..],
                        compressed_cross_term_sums.unwrap(),
                    )?;
                    Some(tcc_chip.add(
                        builder,
                        acc.compressed_e_sum.as_ref().unwrap(),
                        &rhs,
                    )?)
                }
            };

            ProtostarAccumulatorInstance {
                instances,
                witness_comms,
                challenges,
                u,
                e_comm,
                compressed_e_sum,
            }
        };

        Ok(acc_prime)
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    fn fold_accumulator_from_nark_ec(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        >,
        nark: &AssignedPlonkishNarkInstance<
            ProperCrtUint<C::Scalar>, 
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        cross_term_comms: &[EcPoint<C::Scalar, AssignedValue<C::Scalar>>],
        compressed_cross_term_sums: Option<&[ProperCrtUint<C::Scalar>]>,
        r: &ProperCrtUint<C::Scalar>,
        r_le_bits: &[AssignedValue<C::Scalar>],
    ) -> Result<
        AssignedProtostarAccumulatorInstance<
        ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let ProtostarAccumulationVerifierParam {
            strategy,
            num_cross_terms,
            ..
        } = self.avp;

        let powers_of_r = tcc_chip.powers_base(builder, r, num_cross_terms + 1)?;

        let r_nark = {
            let instances = nark
                .instances
                .iter()
                .map(|instances| {
                    instances
                        .iter()
                        .map(|instance| tcc_chip.mul_base(builder, r, instance))
                        .try_collect::<_, Vec<_>, _>()
                })
                .try_collect::<_, Vec<_>, _>()?;
            let timer = start_timer(|| format!("fold_accumulator_from_nark witness_comms-{}", nark.witness_comms.len()));
            let witness_comms = nark
                .witness_comms
                .iter()
                .map(|comm| tcc_chip.scalar_mul_primary(builder, comm, r_le_bits))
                .try_collect::<_, Vec<_>, _>()?;
            end_timer(timer);
            let challenges = nark
                .challenges
                .iter()
                .map(|challenge| tcc_chip.mul_base(builder, r, challenge))
                .try_collect::<_, Vec<_>, _>()?;
            AssignedPlonkishNarkInstance {
                instances,
                challenges,
                witness_comms,
            }
        };
        let acc_prime = {
            let instances = izip_eq!(&acc.instances, &r_nark.instances)
                .map(|(lhs, rhs)| {
                    izip_eq!(lhs, rhs)
                        .map(|(lhs, rhs)| tcc_chip.add_base(builder, lhs, rhs))
                        .try_collect::<_, Vec<_>, _>()
                })
                .try_collect::<_, Vec<_>, _>()?;
            let witness_comms = izip_eq!(&acc.witness_comms, &r_nark.witness_comms)
                .map(|(lhs, rhs)| tcc_chip.add_primary(builder, lhs, rhs))
                .try_collect::<_, Vec<_>, _>()?;
            let challenges = izip_eq!(&acc.challenges, &r_nark.challenges)
                .map(|(lhs, rhs)| tcc_chip.add_base(builder, lhs, rhs))
                .try_collect::<_, Vec<_>, _>()?;
            let u = tcc_chip.add_base(builder, &acc.u, r)?;
            let e_comm = if cross_term_comms.is_empty() {
                acc.e_comm.clone()
            } else {
                let timer = start_timer(|| format!("fold_accumulator_from_nark e_comm-cross_term_comms.len()-{}", cross_term_comms.len()));
                let mut e_comm = cross_term_comms.last().unwrap().clone();
                for item in cross_term_comms.iter().rev().skip(1).chain([&acc.e_comm]) {
                    e_comm = tcc_chip.scalar_mul_primary(builder, &e_comm, r_le_bits)?;
                    e_comm = tcc_chip.add_primary(builder, &e_comm, item)?;
                }
                end_timer(timer);
                e_comm
            };
            let compressed_e_sum = match strategy {
                NoCompressing => None,
                Compressing => {
                    let rhs = tcc_chip.inner_product_base(
                        builder,
                        &powers_of_r[1..],
                        compressed_cross_term_sums.unwrap(),
                    )?;
                    Some(tcc_chip.add_base(
                        builder,
                        acc.compressed_e_sum.as_ref().unwrap(),
                        &rhs,
                    )?)
                }
            };

            ProtostarAccumulatorInstance {
                instances,
                witness_comms,
                challenges,
                u,
                e_comm,
                compressed_e_sum,
            }
        };

        Ok(acc_prime)
    }

    fn select_accumulator(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        condition: &AssignedValue<C::Scalar>,
        when_true: &AssignedProtostarAccumulatorInstance<
            AssignedValue<C::Scalar>,
            EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
        >,
        when_false: &AssignedProtostarAccumulatorInstance<
            AssignedValue<C::Scalar>,
            EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
        >,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<AssignedValue<C::Scalar>, EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>,
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let instances = izip_eq!(&when_true.instances, &when_false.instances)
            .map(|(when_true, when_false)| {
                izip_eq!(when_true, when_false)
                    .map(|(when_true, when_false)| {
                        tcc_chip.select_gatechip(builder, condition, when_true, when_false)
                    })
                    .try_collect()
            })
            .try_collect()?;
        let witness_comms = izip_eq!(&when_true.witness_comms, &when_false.witness_comms)
            .map(|(when_true, when_false)| {
                tcc_chip.select_primary_non_native(builder, condition, when_true, when_false)
            })
            .try_collect()?;
        let challenges = izip_eq!(&when_true.challenges, &when_false.challenges)
            .map(|(when_true, when_false)| {
                tcc_chip.select_gatechip(builder, condition, when_true, when_false)
            })
            .try_collect()?;
        let u = tcc_chip.select_gatechip(builder, condition, &when_true.u, &when_false.u)?;
        let e_comm = tcc_chip.select_primary_non_native(
            builder,
            condition,
            &when_true.e_comm,
            &when_false.e_comm,
        )?;
        let compressed_e_sum = match self.avp.strategy {
            NoCompressing => None,
            Compressing => Some(tcc_chip.select_gatechip(
                builder,
                condition,
                when_true.compressed_e_sum.as_ref().unwrap(),
                when_false.compressed_e_sum.as_ref().unwrap(),
            )?),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }

    fn select_accumulator_ec(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        condition: &AssignedValue<C::Scalar>,
        when_true: &AssignedProtostarAccumulatorInstance<
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        >,
        when_false: &AssignedProtostarAccumulatorInstance<
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        >,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let instances = izip_eq!(&when_true.instances, &when_false.instances)
            .map(|(when_true, when_false)| {
                izip_eq!(when_true, when_false)
                    .map(|(when_true, when_false)| {
                        tcc_chip.select_base(builder, condition, when_true, when_false)
                    })
                    .try_collect()
            })
            .try_collect()?;
        let witness_comms = izip_eq!(&when_true.witness_comms, &when_false.witness_comms)
            .map(|(when_true, when_false)| {
                tcc_chip.select_primary(builder, condition, when_true, when_false)
            })
            .try_collect()?;
        let challenges = izip_eq!(&when_true.challenges, &when_false.challenges)
            .map(|(when_true, when_false)| {
                tcc_chip.select_base(builder, condition, when_true, when_false)
            })
            .try_collect()?;
        let u = tcc_chip.select_base(builder, condition, &when_true.u, &when_false.u)?;
        let e_comm = tcc_chip.select_primary(
            builder,
            condition,
            &when_true.e_comm,
            &when_false.e_comm,
        )?;
        let compressed_e_sum = match self.avp.strategy {
            NoCompressing => None,
            Compressing => Some(tcc_chip.select_base(
                builder,
                condition,
                when_true.compressed_e_sum.as_ref().unwrap(),
                when_false.compressed_e_sum.as_ref().unwrap(),
            )?),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }
}


#[derive(Debug)]
pub struct RecursiveCircuit<C, Sc>
where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    is_primary: bool,
    step_circuit: RefCell<Sc>,
    tcc_chip: Chip<C>,
    hash_chip: Chip<C>,
    hash_config: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    hash_config_base: OptimizedPoseidonSpec<C::Base, T, RATE>,
    transcript_config: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    primary_avp: ProtostarAccumulationVerifierParam<C::Scalar>,
    cyclefold_avp: ProtostarAccumulationVerifierParam<C::Scalar>,
    h_prime: Value<C::Scalar>,
    cyclefold_inputs_hash: Value<C::Base>,
    acc: Value<ProtostarAccumulatorInstance<C::Scalar, C>>,
    acc_prime: Value<ProtostarAccumulatorInstance<C::Scalar, C>>,
    primary_instances: [Value<C::Scalar>; NUM_INSTANCES],
    primary_proof: Value<Vec<u8>>,
    cyclefold_instances: [Value<C::Base>; CF_IO_LEN],
    cyclefold_proof: Value<Vec<u8>>,
    acc_ec: Value<ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
    acc_prime_ec: Value<ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
    inner: RefCell<BaseCircuitBuilder<C::Scalar>>,
}

impl<C, Sc> RecursiveCircuit<C, Sc>
where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    pub const DUMMY_SCALAR: C::Scalar = C::Scalar::ZERO;

    pub fn new(
        is_primary: bool,
        step_circuit: Sc,
        primary_avp: Option<ProtostarAccumulationVerifierParam<C::Scalar>>,
        cyclefold_avp: Option<ProtostarAccumulationVerifierParam<C::Scalar>>,
        circuit_params: BaseCircuitParams,
    ) -> Self {
        let poseidon_spec = OptimizedPoseidonSpec::<C::Scalar, T, RATE>::new::<R_F, R_P, SECURE_MDS>();
        let hash_config = poseidon_spec.clone();
        let poseidon_spec_base = OptimizedPoseidonSpec::<C::Base, T, RATE>::new::<R_F, R_P, SECURE_MDS>();
        let hash_config_base = poseidon_spec_base.clone();
        let transcript_config = poseidon_spec.clone();
        
        let step_circuit = RefCell::new(step_circuit);
        let inner = RefCell::new(BaseCircuitBuilder::<C::Scalar>::from_stage(CircuitBuilderStage::Mock).use_params(circuit_params.clone()));
        let range_chip = inner.borrow().range_chip();
        let chip = Chip::<C>::create(range_chip);
        let hash_chip = Chip::<C>::new(hash_config.clone(), chip.clone());

        Self {
                is_primary,
                step_circuit,
                tcc_chip: chip,
                hash_chip,
                hash_config,
                hash_config_base,
                transcript_config,
                primary_avp: primary_avp.clone().unwrap_or_default(),
                cyclefold_avp: cyclefold_avp.clone().unwrap_or_default(),
                h_prime: Value::known(C::Scalar::ZERO),
                cyclefold_inputs_hash: Value::known(C::Base::ZERO),
                acc: Value::known(primary_avp.clone().unwrap_or_default().init_accumulator()),
                acc_prime: Value::known(primary_avp.clone().unwrap_or_default().init_accumulator()),
                primary_instances: [Value::known(C::Scalar::ZERO); NUM_INSTANCES],
                primary_proof: Value::known(PoseidonNativeTranscriptChip::<C>::dummy_proof(&primary_avp.clone().unwrap_or_default())),
                cyclefold_instances: [Value::known(C::Base::ZERO); CF_IO_LEN],
                cyclefold_proof: Value::known(PoseidonTranscriptChip::<C>::dummy_proof(&cyclefold_avp.clone().unwrap_or_default())),
                acc_ec: Value::known(cyclefold_avp.clone().unwrap_or_default().init_accumulator()),
                acc_prime_ec: Value::known(cyclefold_avp.clone().unwrap_or_default().init_accumulator()),
                inner,
            }
    }

    pub fn update_from_cyclefold<
        Comm_ec: AsRef<C::Secondary>
    >(
        &mut self,
        cyclefold_proof: Vec<u8>,
        cyclefold_instances: [C::Base; CF_IO_LEN],
        acc_ec: ProtostarAccumulatorInstance<C::Base, Comm_ec>,
        acc_prime_ec: ProtostarAccumulatorInstance<C::Base, Comm_ec>,
    ) {
        // self.h_prime_ec = Value::known(Chip::<C>::hash_state_ec(
        //     self.hash_config.borrow(),
        //     self.primary_avp.vp_digest,
        //     &acc_prime_ec,
        // ));
        self.cyclefold_proof = Value::known(cyclefold_proof);
        self.cyclefold_instances = cyclefold_instances.map(Value::known);
        self.acc_ec = Value::known(acc_ec.unwrap_comm());
        self.acc_prime_ec = Value::known(acc_prime_ec.unwrap_comm());
    }

    pub fn update_both_running_instances<
        Comm: AsRef<C>, 
        Comm_ec: AsRef<C::Secondary>
    >(
        &mut self,
        r_le_bits: Vec<C::Scalar>,
        primary_nark_witness_comm: Vec<Comm>,
        cross_term_comms: Vec<Comm>,
        acc: ProtostarAccumulatorInstance<C::Scalar, Comm>,
        acc_prime: ProtostarAccumulatorInstance<C::Scalar, Comm>,
        primary_instances: [C::Scalar; NUM_INSTANCES],
        primary_proof: Vec<u8>,
        acc_ec: ProtostarAccumulatorInstance<C::Base, Comm_ec>,
        acc_prime_ec: ProtostarAccumulatorInstance<C::Base, Comm_ec>,
    ) {
        if (self.is_primary && acc_prime.u != C::Scalar::ZERO)
            || (!self.is_primary && acc.u != C::Scalar::ZERO)
            {
                self.step_circuit.borrow_mut().next();
            }
            self.cyclefold_inputs_hash = Value::known(Chip::<C>::hash_cyclefold_inputs(
                self.hash_config_base.borrow(),
                self.primary_avp.vp_digest,
                r_le_bits,
                primary_nark_witness_comm,
                cross_term_comms,
                &acc,
            ));
            self.h_prime = Value::known(Chip::<C>::hash_state(
                self.hash_config.borrow(),
                self.primary_avp.vp_digest,
                self.step_circuit.borrow().step_idx() + 1,
                self.step_circuit.borrow().initial_input(),
                self.step_circuit.borrow().next_output(),
                &acc_prime,
            ));
            self.acc = Value::known(acc.unwrap_comm());
            self.acc_ec = Value::known(acc_ec.unwrap_comm());
            self.acc_prime = Value::known(acc_prime.unwrap_comm());
            self.acc_prime_ec = Value::known(acc_prime_ec.unwrap_comm());
            self.primary_instances = primary_instances.map(Value::known);
            self.primary_proof = Value::known(primary_proof);
    }

    fn init(&mut self, vp_digest: C::Scalar) {
        assert_eq!(&self.primary_avp.num_instances, &[NUM_INSTANCES]);
        self.primary_avp.vp_digest = vp_digest;
    }

    fn update_acc(&mut self) {
        self.acc = Value::known(self.primary_avp.init_accumulator());
        self.acc_prime = Value::known(self.primary_avp.init_accumulator());
        self.acc_ec = Value::known(self.cyclefold_avp.init_accumulator());
        self.acc_prime_ec = Value::known(self.cyclefold_avp.init_accumulator());
    }

    fn check_initial_condition(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        is_base_case: &AssignedValue<C::Scalar>,
        initial_input: &[AssignedValue<C::Scalar>],
        input: &[AssignedValue<C::Scalar>],
    ) -> Result<(), Error> {
        let tcc_chip = &self.tcc_chip;
        let zero = builder.main().load_zero();
        for (lhs, rhs) in input.iter().zip(initial_input.iter()) {
            let lhs = tcc_chip.select_gatechip(builder, is_base_case, lhs, &zero)?;
            let rhs = tcc_chip.select_gatechip(builder, is_base_case, rhs, &zero)?;
            tcc_chip.constrain_equal(builder, &lhs, &rhs)?;
        }

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    fn check_state_hash(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        is_base_case: Option<&AssignedValue<C::Scalar>>,
        h: &AssignedValue<C::Scalar>,
        vp_digest: &AssignedValue<C::Scalar>,
        step_idx: &AssignedValue<C::Scalar>,
        initial_input: &[AssignedValue<C::Scalar>],
        output: &[AssignedValue<C::Scalar>],
        acc: &AssignedProtostarAccumulatorInstance<
            AssignedValue<C::Scalar>,
            EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
        >,
    ) -> Result<(), Error> {
        let tcc_chip = &self.tcc_chip;
        let hash_chip = &self.hash_chip;
        let lhs = h;
        let rhs = hash_chip.hash_assigned_state(
            builder,
            vp_digest,
            step_idx,
            initial_input,
            output,
            acc,
        )?;
        let rhs = if let Some(is_base_case) = is_base_case {
            let zero = builder.main().load_zero();
            tcc_chip.select_gatechip(builder, is_base_case, &zero, &rhs)?
        } else {
            rhs
        };
        // lhs = h == 0 initalised 
        let zero = builder.main().load_zero();
        let lhs_is_zero = tcc_chip.is_equal(builder, lhs, &zero)?;
        let rhs = tcc_chip.select_gatechip(builder, &lhs_is_zero, &zero, &rhs)?;
        tcc_chip.constrain_equal(builder, lhs, &rhs)?;

        Ok(())
    }


    fn check_folding_ec(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc_prime: &AssignedProtostarAccumulatorInstance<
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>
        >,
        acc_prime_result: &AssignedProtostarAccumulatorInstance<
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>
        >
    ) -> Result<(), Error> {
        let tcc_chip = &self.tcc_chip;
        let default_compressed_e_sum = tcc_chip.assign_constant_base(builder, C::Base::ZERO)?;
        izip_eq!(&acc_prime.instances[0], &acc_prime_result.instances[0])
            .map(|(lhs, rhs)| {
                tcc_chip.constrain_equal_base(builder, lhs, rhs);
            }).collect_vec();
        izip_eq!(&acc_prime.witness_comms, &acc_prime_result.witness_comms)
            .map(|(lhs, rhs)| {
                tcc_chip.constrain_equal_primary(builder, lhs, rhs);
            }).collect_vec();
        izip_eq!(&acc_prime.challenges, &acc_prime_result.challenges)
            .map(|(lhs, rhs)| {
                tcc_chip.constrain_equal_base(builder, lhs, rhs);
            }).collect_vec();
        tcc_chip.constrain_equal_base(builder, &acc_prime.u, &acc_prime_result.u)?;
        tcc_chip.constrain_equal_primary(builder, &acc_prime.e_comm, &acc_prime_result.e_comm)?;
        tcc_chip.constrain_equal_base(builder, &acc_prime.compressed_e_sum.as_ref().unwrap_or(&default_compressed_e_sum), &acc_prime_result.compressed_e_sum.as_ref().unwrap_or(&default_compressed_e_sum))?;

        Ok(())
    }

    fn synthesize_accumulation_verifier(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        config: <RecursiveCircuit<C, Sc> as Circuit<C::Scalar>>::Config,
        input: &[AssignedValue<C::Scalar>],
        output: &[AssignedValue<C::Scalar>],
        circuit_builder: &mut BaseCircuitBuilder<C::Scalar>,
    ) -> Result<(), Error> {
        let Self {
            tcc_chip,
            transcript_config,
            primary_avp,
            cyclefold_avp,
            ..
        } = &self;

        let builder = circuit_builder.pool(0);  
        let acc_verifier = ProtostarAccumulationVerifier::new(primary_avp.clone(), tcc_chip.clone());

        let zero = builder.main().load_zero();
        let one = tcc_chip.assign_constant(builder, C::Scalar::ONE)?;
        let vp_digest = tcc_chip.assign_witness(builder, primary_avp.vp_digest)?;
        let step_idx = tcc_chip.assign_witness(
            builder,
            C::Scalar::from(self.step_circuit.borrow().step_idx() as u64))?;
        let step_idx_plus_one = tcc_chip.add(builder, &step_idx, &one)?;
        let h_prime = tcc_chip.assign_witness(builder, self.h_prime.assign().unwrap())?;
        let initial_input = self
            .step_circuit
            .borrow()
            .initial_input()
            .iter()
            .map(|value| tcc_chip.assign_witness(builder, *value))
            .try_collect::<_, Vec<_>, _>()?;

        let is_base_case = tcc_chip.is_equal(builder, &step_idx, &zero)?;
        self.check_initial_condition(builder, &is_base_case, &initial_input, input)?;

        let cyclefold_instances = self.cyclefold_instances
            .iter()
            .map(|instance| Value::as_ref(&instance))
            .collect_vec();  

        let cyclefold_inputs_hash = tcc_chip.assign_witness_base(builder, self.cyclefold_inputs_hash.assign().unwrap())?;
        let cyclefold_inputs_hash_from_instances = tcc_chip.assign_witness_base(builder, *cyclefold_instances[0].assign().unwrap())?;
        let cyclefold_inputs_hash_from_instances_select = tcc_chip.select_base(builder, &is_base_case, &cyclefold_inputs_hash, &cyclefold_inputs_hash_from_instances)?;
        tcc_chip.constrain_equal_base(builder, &cyclefold_inputs_hash, &cyclefold_inputs_hash_from_instances_select)?;

        let acc = acc_verifier.assign_accumulator(builder, self.acc.as_ref())?;
        let assigned_acc_prime_comms_checked = acc_verifier.assign_comm_outputs_from_accumulator(builder, self.acc_prime.as_ref())?;
        let (nark, acc_prime) = {
            let instances =
                [&self.primary_instances[0]].map(Value::as_ref);  
            let proof = self.primary_proof.clone();
            let transcript =
                &mut PoseidonNativeTranscriptChip::new(builder.main(), transcript_config.clone(), tcc_chip.clone(), proof);
            acc_verifier.verify_accumulation_from_nark(builder, &acc, instances, transcript, assigned_acc_prime_comms_checked)?
        };

        let acc_prime = {
            let acc_default = acc_verifier.assign_default_accumulator(builder)?;
            acc_verifier.select_accumulator(builder, &is_base_case, &acc_default, &acc_prime)?
        };

        // check if nark.instances[0][0] = Hash(inputs, acc)
        self.check_state_hash(
            builder,
            Some(&is_base_case),
            &nark.instances[0][0],
            &vp_digest,
            &step_idx,
            &initial_input,
            &input,
            &acc,
        )?;

        // checks if folding was done correctly
        // h_prime = Hash(inputs, acc_prime)
        self.check_state_hash(
            builder,
            None,
            &h_prime,
            &vp_digest,
            &step_idx_plus_one,
            &initial_input,
            output,
            &acc_prime,
        )?;

        let acc_verifier_ec = ProtostarAccumulationVerifier::new(cyclefold_avp.clone(), tcc_chip.clone());
        let acc_ec = acc_verifier_ec.assign_accumulator_ec(builder, self.acc_ec.as_ref())?;
        let acc_ec_prime_result = acc_verifier_ec.assign_accumulator_ec(builder, self.acc_prime_ec.as_ref())?;
        let (nark_ec, acc_ec_prime) = {     
            let proof = self.cyclefold_proof.clone();
            let transcript =
                &mut PoseidonTranscriptChip::new(builder.main(), transcript_config.clone(), tcc_chip.clone(), proof);
            acc_verifier_ec.verify_accumulation_from_nark_ec(builder, &acc_ec, cyclefold_instances.try_into().unwrap(), transcript)?
        };

        let (acc_ec_prime, acc_ec_prime_result) = {
            let acc_ec_default = acc_verifier_ec.assign_default_accumulator_ec(builder)?;
            let acc_ec_prime = acc_verifier_ec.select_accumulator_ec(builder, &is_base_case, &acc_ec_default, &acc_ec_prime)?;
            let acc_ec_prime_result = acc_verifier_ec.select_accumulator_ec(builder, &is_base_case, &acc_ec_default, &acc_ec_prime_result)?;
            (acc_ec_prime, acc_ec_prime_result)
        };

        self.check_folding_ec(
            builder,
            &acc_ec_prime,
            &acc_ec_prime_result,
        )?; 

        let assigned_instances = &mut circuit_builder.assigned_instances;
        assert_eq!(
            assigned_instances.len(),
            1,
            "Circuit must have exactly 1 instance column"
        );
        assert!(assigned_instances[0].is_empty());
        assigned_instances[0].push(h_prime);


        // let instances = self.instances();
        // MockProver::run(19, &*binding, instances.clone()).unwrap().assert_satisfied();

        circuit_builder.synthesize(config.clone(), layouter.namespace(|| ""));

        let copy_manager = circuit_builder.pool(0).copy_manager.lock().unwrap();
        println!("copy_manager.advice_equalities {:?}", copy_manager.advice_equalities.len());
        println!("copy_manager.constant_equalities {:?}", copy_manager.constant_equalities.len());
        println!("copy_manager.assigned_advices {:?}", copy_manager.assigned_advices.len());
        drop(copy_manager);

        circuit_builder.clear();
        drop(circuit_builder);

        Ok(())
    }
}

impl<C, Sc> Circuit<C::Scalar> for RecursiveCircuit<C, Sc>
where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    type Config = BaseConfig<C::Scalar>;
    type FloorPlanner = Sc::FloorPlanner;
    type Params = BaseCircuitParams;

    fn without_witnesses(&self) -> Self {
        Self {
            is_primary: self.is_primary,
            step_circuit: self.step_circuit.borrow().without_witnesses().into(),
            tcc_chip: self.tcc_chip.clone(),
            hash_chip: self.hash_chip.clone(),
            hash_config: self.hash_config.clone(),
            hash_config_base: self.hash_config_base.clone(),
            transcript_config: self.transcript_config.clone(),
            primary_avp: self.primary_avp.clone(),
            cyclefold_avp: self.cyclefold_avp.clone(),
            h_prime: Value::unknown(),
            cyclefold_inputs_hash: Value::unknown(),
            acc: Value::unknown(),
            acc_prime: Value::unknown(),
            primary_instances: [Value::unknown(); NUM_INSTANCES],
            primary_proof: Value::unknown(),
            cyclefold_instances: [Value::unknown(); CF_IO_LEN],
            cyclefold_proof: Value::unknown(),
            acc_ec: Value::unknown(),
            acc_prime_ec: Value::unknown(),
            inner: self.inner.clone(),
        }
    }

    fn configure_with_params(meta: &mut ConstraintSystem<C::Scalar>, params: BaseCircuitParams) -> Self::Config {
        BaseCircuitBuilder::configure_with_params(meta, params)
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        unreachable!()
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {
        let mut step_circuit = self.step_circuit.borrow_mut();
        let mut builder = self.inner.borrow_mut();
        let (input, output) =
            StepCircuit::<C>::synthesize(&mut *step_circuit, config.clone(), layouter.namespace(|| ""), &mut builder)?;
        drop(step_circuit);
        
        let synthesize_accumulation_verifier_time = Instant::now();
        self.synthesize_accumulation_verifier(layouter.namespace(|| ""),config.clone(),  &input, &output, &mut builder)?;
        let duration_synthesize_accumulation_verifier = synthesize_accumulation_verifier_time.elapsed();
        println!("Time for synthesize_accumulation_verifier: {:?}", duration_synthesize_accumulation_verifier);

        Ok(())
    }
}

impl<C, Sc> CircuitExt<C::Scalar> for RecursiveCircuit<C, Sc>
where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    fn instances(&self) -> Vec<Vec<C::Scalar>> {
        let mut instances = vec![vec![C::Scalar::ZERO; NUM_INSTANCES]];
        self.h_prime.map(|h_prime| instances[0][0] = h_prime);
        instances
    }

    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}

#[derive(Debug)]
pub struct ProtostarIvcProverParam<C, P1, P2, AT1, AT2>
where
    C: TwoChainCurve,
    HyperPlonk<P1>: PlonkishBackend<C::Scalar>,
    HyperPlonk<P2>: PlonkishBackend<C::Base>,
    AT1: InMemoryTranscript,
    AT2: InMemoryTranscript,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    primary_pp: ProtostarProverParam<C::Scalar, HyperPlonk<P1>>,
    primary_atp: AT1::Param,
    cyclefold_pp: ProtostarProverParam<C::Base, HyperPlonk<P2>>,
    cyclefold_atp: AT2::Param,
    _marker: PhantomData<(C, AT1, AT2)>,
}

#[derive(Debug)]
pub struct ProtostarIvcVerifierParam<C, P1, P2>
where
    C: TwoChainCurve,
    HyperPlonk<P1>: PlonkishBackend<C::Scalar>,
    HyperPlonk<P2>: PlonkishBackend<C::Base>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    vp_digest: C::Scalar,
    primary_vp: ProtostarVerifierParam<C::Scalar, HyperPlonk<P1>>,
    primary_hp: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    primary_arity: usize,
    cyclefold_vp: ProtostarVerifierParam<C::Base, HyperPlonk<P2>>,
    cyclefold_hp: OptimizedPoseidonSpec<C::Base, T, RATE>,
    cyclefold_arity: usize,
    _marker: PhantomData<C>,
}

impl<C, P1, P2> ProtostarIvcVerifierParam<C, P1, P2>
where
    C: TwoChainCurve,
    HyperPlonk<P1>: PlonkishBackend<C::Scalar>,
    HyperPlonk<P2>: PlonkishBackend<C::Base>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    pub fn primary_arity(&self) -> usize {
        self.primary_arity
    }

    pub fn cyclefold_arity(&self) -> usize {
        self.cyclefold_arity
    }
}

#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn preprocess<C, P1, P2, S1, AT1, AT2>(
    primary_num_vars: usize,
    primary_atp: AT1::Param,
    primary_step_circuit: S1,
    cyclefold_num_vars: usize,
    cyclefold_atp: AT2::Param,
    primary_circuit_params: BaseCircuitParams,
    cyclefold_circuit_params: BaseCircuitParams,
    mut rng: impl RngCore,
) -> Result<
    (
        Halo2Circuit<C::Scalar, RecursiveCircuit<C, S1>>,
        Halo2Circuit<C::Base, CycleFoldCircuit<C::Secondary>>,
        ProtostarIvcProverParam<C, P1, P2, AT1, AT2>,
        ProtostarIvcVerifierParam<
            C,
            P1,
            P2,
        >,
    ),
    Error,
>
where
    C: TwoChainCurve,
    C::Scalar: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    P1: PolynomialCommitmentScheme<
        C::ScalarExt,
        Polynomial = MultilinearPolynomial<C::Scalar>,
        CommitmentChunk = C,
    >,
    P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
    P2: PolynomialCommitmentScheme<
        C::Base,
        Polynomial = MultilinearPolynomial<C::Base>,
        CommitmentChunk = C::Secondary,
    >,
    P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
    S1: StepCircuit<C>,
    AT1: InMemoryTranscript,
    AT2: InMemoryTranscript,
{
    assert_eq!(Chip::<C>::NUM_HASH_BITS, Chip::<C::Secondary>::NUM_HASH_BITS);

    let primary_param = P1::setup(1 << primary_num_vars, 0, &mut rng).unwrap();
    let cyclefold_param = P2::setup(1 << cyclefold_num_vars, 0, &mut rng).unwrap();
    
    let primary_circuit = RecursiveCircuit::new(true, primary_step_circuit, None, None, primary_circuit_params.clone());
    let mut primary_circuit =
        Halo2Circuit::new::<HyperPlonk<P1>>(primary_num_vars, primary_circuit, primary_circuit_params.clone());

    let (_, primary_vp_without_preprocess) = {
        let primary_circuit_info = primary_circuit.circuit_info_without_preprocess().unwrap();
            Protostar::<HyperPlonk<P1>>::preprocess(&primary_param, &primary_circuit_info).unwrap()
        };

        let cyclefold_circuit = CycleFoldCircuit::new(
        Some(ProtostarAccumulationVerifierParam::from(&primary_vp_without_preprocess)),
        cyclefold_circuit_params.clone());
    let mut cyclefold_circuit =
            Halo2Circuit::new::<HyperPlonk<P2>>(cyclefold_num_vars, cyclefold_circuit, cyclefold_circuit_params.clone());
        
    let (cyclefold_pp, cyclefold_vp) = {
            let cyclefold_circuit_info = cyclefold_circuit.circuit_info().unwrap();
            Protostar::<HyperPlonk<P2>>::preprocess(&cyclefold_param, &cyclefold_circuit_info).unwrap()
    };

    primary_circuit.update_witness(|circuit| {
            circuit.primary_avp = ProtostarAccumulationVerifierParam::from(&primary_vp_without_preprocess);
            circuit.cyclefold_avp = ProtostarAccumulationVerifierParam::from(&cyclefold_vp);
            circuit.update_acc();
    });

    let primary_circuit_info = primary_circuit.circuit_info().unwrap();
    let (primary_pp, primary_vp) =
        Protostar::<HyperPlonk<P1>>::preprocess(&primary_param, &primary_circuit_info).unwrap();

    let vp_digest = fe_truncated_from_le_bytes(
        Keccak256::digest(bincode::serialize(&(&primary_vp, &cyclefold_vp)).unwrap()),
        Chip::<C>::NUM_HASH_BITS,
    );
    primary_circuit.update_witness(|circuit| circuit.init(vp_digest));
    cyclefold_circuit.update_witness(|circuit| circuit.init(fe_to_fe(vp_digest)));

    let ivc_pp = ProtostarIvcProverParam {
        primary_pp,
        primary_atp,
        cyclefold_pp,
        cyclefold_atp,
        _marker: PhantomData,
    };
    let ivc_vp = {
        ProtostarIvcVerifierParam {
            vp_digest,
            primary_vp,
            primary_hp: primary_circuit.circuit().hash_config.borrow().clone(),
            primary_arity: S1::arity(),
            cyclefold_vp,
            cyclefold_hp: cyclefold_circuit.circuit().hash_config.borrow().clone(),
            cyclefold_arity: CF_IO_LEN,
            _marker: PhantomData,
        }
    };

    Ok((primary_circuit, cyclefold_circuit, ivc_pp, ivc_vp))
}

#[allow(clippy::type_complexity)]
pub fn prove_steps<C, P1, P2, S1, AT1, AT2>(
    ivc_pp: &ProtostarIvcProverParam<C, P1, P2, AT1, AT2>,
    primary_circuit: &mut Halo2Circuit<C::Scalar, RecursiveCircuit<C, S1>>,
    cyclefold_circuit: &mut Halo2Circuit<C::Base, CycleFoldCircuit<C::Secondary>>,
    num_steps: usize,
    mut rng: impl RngCore,
) -> Result<
    (
        ProtostarAccumulator<C::Scalar, P1>,
        ProtostarAccumulator<C::Base, P2>,
    ),
    crate::Error,
>
where
    C: TwoChainCurve,
    C::Scalar: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    P1: PolynomialCommitmentScheme<
        C::ScalarExt,
        Polynomial = MultilinearPolynomial<C::Scalar>,
        CommitmentChunk = C,
    >,
    P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
    P2: PolynomialCommitmentScheme<
        C::Base,
        Polynomial = MultilinearPolynomial<C::Base>,
        CommitmentChunk = C::Secondary,
    >,
    P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
    S1: StepCircuit<C>,
    AT1: TranscriptRead<P1::CommitmentChunk, C::Scalar>
        + TranscriptWrite<P1::CommitmentChunk, C::Scalar>
        + InMemoryTranscript,
    AT2: TranscriptRead<P2::CommitmentChunk, C::Base>
        + TranscriptWrite<P2::CommitmentChunk, C::Base>
        + InMemoryTranscript,

{
    let mut primary_acc = Protostar::<HyperPlonk<P1>>::init_accumulator(&ivc_pp.primary_pp)?;
    let mut primary_acc_ec = Protostar::<HyperPlonk<P2>>::init_accumulator(&ivc_pp.cyclefold_pp)?;

    for step_idx in 0..num_steps {
        let primary_acc_ec_x = primary_acc_ec.instance.clone();        
        let primary_acc_x = primary_acc.instance.clone();

        let timer = start_timer(|| {
            format!(
                "prove_accumulation_from_nark-primary-{}",
                ivc_pp.primary_pp.pp.num_vars
            )
        });

        let (r_le_bits, primary_nark_x, cross_term_comms, primary_proof) = {
            let mut primary_transcript = AT1::new(ivc_pp.primary_atp.clone());
            let (r_le_bits, primary_nark_as_acc, cross_term_comms) = Protostar::<HyperPlonk<P1>>::prove_accumulation_from_nark(
                    &ivc_pp.primary_pp,
                    &mut primary_acc,
                    primary_circuit as &_,
                    &mut primary_transcript,
                    &mut rng,
                )?;
                (r_le_bits, primary_nark_as_acc.instance, cross_term_comms, primary_transcript.into_proof())
            };
        end_timer(timer);

        let primary_instances = primary_circuit.instances()[0].clone().try_into().unwrap();

            primary_circuit.update_witness(|circuit| {
                circuit.update_both_running_instances(
                    r_le_bits.clone(), 
                    primary_nark_x.witness_comms.clone(), 
                    cross_term_comms.clone(),
                    primary_acc_x.clone(),
                    primary_acc.instance.clone(),
                    primary_instances,
                    primary_proof.clone(),
                    primary_acc_ec_x.clone(),
                    primary_acc_ec.instance.clone(),
                );
            });

            cyclefold_circuit.update_witness(|circuit| {
                circuit.update_cyclefold_inputs(
                    r_le_bits.iter().map(|b| fe_to_fe(*b)).collect_vec(),
                    cross_term_comms,
                    primary_nark_x,
                    primary_acc_x,
                    primary_acc.instance.clone(),
                );
            });

        if step_idx != num_steps - 1 {
            let timer = start_timer(|| {
                    format!(
                        "prove_accumulation_from_nark_ec-primary-{}",
                        ivc_pp.cyclefold_pp.pp.num_vars
                    )
            });
    
            let cyclefold_proof = {
                let mut cyclefold_transcript = AT2::new(ivc_pp.cyclefold_atp.clone());
                    Protostar::<HyperPlonk<P2>>::prove_accumulation_from_nark_ec(
                        &ivc_pp.cyclefold_pp,
                        &mut primary_acc_ec,
                        cyclefold_circuit as &_,
                        &mut cyclefold_transcript,
                        &mut rng,
                    )?;
                    cyclefold_transcript.into_proof()
                };

            end_timer(timer);

            primary_circuit.update_witness(|circuit| {
                circuit.update_from_cyclefold(
                    cyclefold_proof,
                    cyclefold_circuit.instances()[0].clone().try_into().unwrap(),
                    primary_acc_ec_x,
                    primary_acc_ec.instance.clone(),
                );
            });

        } else {
            return Ok((
                primary_acc,
                primary_acc_ec,
            ))
        }
    }
    unreachable!()
}

pub fn prove_decider<C, P1, P2, AT1, AT2>(
    ivc_pp: &ProtostarIvcProverParam<C, P1, P2, AT1, AT2>,
    primary_acc: &ProtostarAccumulator<C::Scalar, P1>,
    cyclefold_acc: &ProtostarAccumulator<C::Base, P2>,
    primary_transcript: &mut impl TranscriptWrite<P1::CommitmentChunk, C::Scalar>,
    cyclefold_transcript: &mut impl TranscriptWrite<P2::CommitmentChunk, C::Base>,
    mut rng: impl RngCore,
) -> Result<(), crate::Error>
where
    C: TwoChainCurve,
    C::Scalar: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    P1: PolynomialCommitmentScheme<
        C::ScalarExt,
        Polynomial = MultilinearPolynomial<C::Scalar>,
        CommitmentChunk = C,
    >,
    P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
    P2: PolynomialCommitmentScheme<
        C::Base,
        Polynomial = MultilinearPolynomial<C::Base>,
        CommitmentChunk = C::Secondary,
    >,
    P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
    AT1: InMemoryTranscript,
    AT2: InMemoryTranscript,
{
    let timer = start_timer(|| format!("prove_decider-primary-{}", ivc_pp.primary_pp.pp.num_vars));
    Protostar::<HyperPlonk<P1>>::prove_decider(
        &ivc_pp.primary_pp,
        primary_acc,
        primary_transcript,
        &mut rng,
    )?;
    end_timer(timer);
    let timer = start_timer(|| {
        format!(
            "prove_decider-cyclefold-{}",
            ivc_pp.cyclefold_pp.pp.num_vars
        )
    });
    Protostar::<HyperPlonk<P2>>::prove_decider(
        &ivc_pp.cyclefold_pp,
        cyclefold_acc,
        cyclefold_transcript,
        &mut rng,
    )?;
    end_timer(timer);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn verify_decider<C, P1, P2>(
    ivc_vp: &ProtostarIvcVerifierParam<C, P1, P2>,
    primary_acc: &ProtostarAccumulatorInstance<C::Scalar, P1::Commitment>,
    cyclefold_acc: &ProtostarAccumulatorInstance<C::Base, P2::Commitment>,
    primary_transcript: &mut impl TranscriptRead<P1::CommitmentChunk, C::Scalar>,
    cyclefold_transcript: &mut impl TranscriptRead<P2::CommitmentChunk, C::Base>,
    mut rng: impl RngCore,
) -> Result<(), crate::Error>
where
    C: TwoChainCurve,
    C::Scalar: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    P1: PolynomialCommitmentScheme<
        C::ScalarExt,
        Polynomial = MultilinearPolynomial<C::Scalar>,
        CommitmentChunk = C,
    >,
    P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
    P2: PolynomialCommitmentScheme<
        C::Base,
        Polynomial = MultilinearPolynomial<C::Base>,
        CommitmentChunk = C::Secondary,
    >,
    P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
{

    Protostar::<HyperPlonk<P1>>::verify_decider(
        &ivc_vp.primary_vp,
        primary_acc,
        primary_transcript,
        &mut rng,
    )?;

    Protostar::<HyperPlonk<P2>>::verify_decider(
        &ivc_vp.cyclefold_vp,
        cyclefold_acc,
        cyclefold_transcript,
        &mut rng,
    )?;
    Ok(())
}