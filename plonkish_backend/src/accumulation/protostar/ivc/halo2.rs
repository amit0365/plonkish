use crate::{
    accumulation::{
        protostar::{
            ivc::{ProtostarAccumulationVerifierParam, halo2::test::strawman::PoseidonTranscriptChip},
            PlonkishNarkInstance, Protostar, ProtostarAccumulator, ProtostarAccumulatorInstance,
            ProtostarProverParam,
            ProtostarStrategy::{Compressing, NoCompressing},
            ProtostarVerifierParam,
        },
        AccumulationScheme,
    },
    backend::{
        hyperplonk::{verifier::point_offset, HyperPlonk, HyperPlonkVerifierParam},
        PlonkishBackend, PlonkishCircuit,
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
            barycentric_weights, fe_to_fe, fe_truncated_from_le_bytes, powers, steps,
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
    poseidon::hasher::{PoseidonSponge, PoseidonHasher, spec::OptimizedPoseidonSpec, PoseidonHash}, halo2_proofs::dev::MockProver, virtual_region::copy_constraints::SharedCopyConstraintManager,
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
    Coordinates, CurveAffine, CurveExt,
};

pub mod test;
use test::strawman::{self, T, RANGE_BITS, RATE, NUM_CHALLENGE_BITS, NUM_LIMBS, NUM_LIMB_BITS, R_F, R_P, SECURE_MDS, Chip};


pub type AssignedPlonkishNarkInstance<AssignedBase, AssignedSecondary> =
    PlonkishNarkInstance<AssignedBase, AssignedSecondary>;

pub type AssignedProtostarAccumulatorInstance<AssignedBase, AssignedSecondary> =
    ProtostarAccumulatorInstance<AssignedBase, AssignedSecondary>;


pub trait StepCircuit<C: TwoChainCurve>: Clone + Debug + CircuitExt<C::Scalar> 
where
    C::Scalar: BigPrimeField,
    C::Base: BigPrimeField,
{   

    fn arity() -> usize;

    fn initial_input(&self) -> &[C::Scalar];

    fn input(&self) -> &[C::Scalar];

    fn output(&self) -> &[C::Scalar];

    fn step_idx(&self) -> usize;

    fn next(&mut self);

    //todo fix this with other synthesizes
    #[allow(clippy::type_complexity)]
    fn synthesize(
        &self,
        config: BaseConfig<C::Scalar>,
        layouter: impl Layouter<C::Scalar>,
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
        AssignedProtostarAccumulatorInstance<ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
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
            tcc_chip.assign_constant_secondary(builder, C::Secondary::identity())
        })
        .take(self.avp.num_folding_witness_polys())
        .try_collect::<_, Vec<_>, _>()?;
        let challenges =
            iter::repeat_with(|| tcc_chip.assign_constant_base(builder, C::Base::ZERO))
                .take(self.avp.num_folding_challenges())
                .try_collect::<_, Vec<_>, _>()?;
        let u = tcc_chip.assign_constant_base(builder, C::Base::ZERO)?;
        let e_comm = tcc_chip.assign_constant_secondary(builder, C::Secondary::identity())?;
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

    pub fn assign_accumulator(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: Value<&ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
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
            .map(|witness_comm| tcc_chip.assign_witness_secondary(builder, witness_comm.copied().assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;

        let challenges = acc
            .map(|acc| &acc.challenges)
            .transpose_vec(avp.num_folding_challenges())
            .into_iter()
            .map(|challenge| tcc_chip.assign_witness_base(builder, challenge.copied().assign().unwrap()))
            .try_collect::<_, Vec<_>, _>()?;

        let u = tcc_chip.assign_witness_base(builder, acc.map(|acc| &acc.u).copied().assign().unwrap())?;
        let e_comm = tcc_chip.assign_witness_secondary(builder, acc.map(|acc| acc.e_comm).assign().unwrap())?;
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

    fn assign_accumulator_from_r_nark(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        r: &ProperCrtUint<C::Scalar>,
        r_nark: AssignedPlonkishNarkInstance<ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        Error,
    > {
        let tcc_chip = &self.tcc_chip;
        let AssignedPlonkishNarkInstance {
            instances,
            challenges,
            witness_comms,
        } = r_nark;
        let u = r.clone();
        let e_comm = tcc_chip.assign_constant_secondary(builder, C::Secondary::identity())?;
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

    #[allow(clippy::type_complexity)]
    pub fn verify_accumulation_from_nark(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        >,
        instances: [Value<&C::Base>; 2],
        transcript: &mut PoseidonTranscriptChip<C>,
    ) -> Result<
        (
            AssignedPlonkishNarkInstance<ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
            AssignedProtostarAccumulatorInstance<ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
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
        let instances = instances
            .into_iter()
            .map(|instance| tcc_chip.assign_witness_base(builder, instance.copied().assign().unwrap()))
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
                    tcc_chip.powers_base(builder, challenge.as_ref(), *num_powers + 1)?;
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
        let r_le_bits = r.le_bits.clone();
        let (r_nark, acc_prime) = self.fold_accumulator_from_nark(
            builder,
            acc,
            &nark,
            &cross_term_comms,
            compressed_cross_term_sums.as_deref(),
            r.as_ref(),
            &r_le_bits,
        )?;
        let acc_r_nark = self.assign_accumulator_from_r_nark(builder, r.as_ref(), r_nark)?;

        Ok((nark, acc_r_nark, acc_prime))
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    fn fold_accumulator_from_nark(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        >,
        nark: &AssignedPlonkishNarkInstance<ProperCrtUint<C::Scalar>, EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        cross_term_comms: &[EcPoint<C::Scalar, AssignedValue<C::Scalar>>],
        compressed_cross_term_sums: Option<&[ProperCrtUint<C::Scalar>]>,
        r: &ProperCrtUint<C::Scalar>,
        r_le_bits: &[AssignedValue<C::Scalar>],
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
                .map(|comm| tcc_chip.scalar_mul_secondary(builder, comm, r_le_bits))
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
                .map(|(lhs, rhs)| tcc_chip.add_secondary(builder, lhs, rhs))
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
                    e_comm = tcc_chip.scalar_mul_secondary(builder, &e_comm, r_le_bits)?;
                    e_comm = tcc_chip.add_secondary(builder, &e_comm, item)?;
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

        Ok((r_nark, acc_prime))
    }

    fn select_accumulator(
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
                tcc_chip.select_secondary(builder, condition, when_true, when_false)
            })
            .try_collect()?;
        let challenges = izip_eq!(&when_true.challenges, &when_false.challenges)
            .map(|(when_true, when_false)| {
                tcc_chip.select_base(builder, condition, when_true, when_false)
            })
            .try_collect()?;
        let u = tcc_chip.select_base(builder, condition, &when_true.u, &when_false.u)?;
        let e_comm = tcc_chip.select_secondary(
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

// todo remove value wrapper
#[derive(Debug)]
pub struct RecursiveCircuit<C, Sc>
where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    is_primary: bool,
    step_circuit: Sc,
    tcc_chip: Chip<C>,
    hash_chip: Chip<C>,
    hash_config: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    transcript_config: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    avp: ProtostarAccumulationVerifierParam<C::Scalar>,
    h_prime: Value<C::Scalar>,
    acc: Value<ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
    acc_prime: Value<ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
    incoming_instances: [Value<C::Base>; 2],
    incoming_proof: Value<Vec<u8>>,
    inner: RefCell<BaseCircuitBuilder<C::Scalar>>,
}

impl<C, Sc> RecursiveCircuit<C, Sc>
where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    pub const DUMMY_H: C::Scalar = C::Scalar::ZERO;

    pub fn new(
        is_primary: bool,
        step_circuit: Sc,
        avp: Option<ProtostarAccumulationVerifierParam<C::Scalar>>,
        circuit_params: BaseCircuitParams,
    ) -> Self {
        let poseidon_spec = OptimizedPoseidonSpec::new::<R_F, R_P, SECURE_MDS>();
        let hash_config = poseidon_spec.clone();
        let transcript_config = poseidon_spec.clone();

        // let inner = RefCell::new(BaseCircuitBuilder::<C::Scalar>::from_stage(CircuitBuilderStage::Prover).use_params(circuit_params.clone()).use_break_points(vec![vec![]]));
        let inner = RefCell::new(BaseCircuitBuilder::<C::Scalar>::from_stage(CircuitBuilderStage::Mock).use_params(circuit_params.clone()));
        let range_chip = inner.borrow().range_chip();
        let chip = Chip::<C>::create(range_chip);
        let hash_chip = Chip::<C>::new(hash_config.clone(), chip.clone());
        let circuit = Self {
                is_primary,
                step_circuit,
                tcc_chip: chip,
                hash_chip,
                hash_config,
                transcript_config,
                avp: avp.clone().unwrap_or_default(),
                h_prime: Value::known(C::Scalar::ZERO),
                acc: Value::known(avp.clone().unwrap_or_default().init_accumulator()),
                acc_prime: Value::known(avp.clone().unwrap_or_default().init_accumulator()),
                incoming_instances: [Value::known(C::Base::ZERO); 2],
                incoming_proof: Value::known(PoseidonTranscriptChip::<C>::dummy_proof(&avp.clone().unwrap_or_default())),
                inner,
            };
        circuit
    }

    pub fn update<Comm: AsRef<C::Secondary>>(
        &mut self,
        acc: ProtostarAccumulatorInstance<C::Base, Comm>,
        acc_prime: ProtostarAccumulatorInstance<C::Base, Comm>,
        incoming_instances: [C::Base; 2],
        incoming_proof: Vec<u8>,
    ) {
        if (self.is_primary && acc_prime.u != C::Base::ZERO)
            || (!self.is_primary && acc.u != C::Base::ZERO)
            {
                self.step_circuit.next();
            }
            self.h_prime = Value::known(Chip::<C>::hash_state(
                self.hash_config.borrow(),
                self.avp.vp_digest,
                self.step_circuit.step_idx() + 1,
                self.step_circuit.initial_input(),
                self.step_circuit.output(),
                &acc_prime,
            ));
            self.acc = Value::known(acc.unwrap_comm());
            self.acc_prime = Value::known(acc_prime.unwrap_comm());
            self.incoming_instances = incoming_instances.map(Value::known);
            self.incoming_proof = Value::known(incoming_proof);
        }

    fn init(&mut self, vp_digest: C::Scalar) {
        assert_eq!(&self.avp.num_instances, &[2]);
        self.avp.vp_digest = vp_digest;
        self.update::<Cow<C::Secondary>>(
            self.avp.init_accumulator(),
            self.avp.init_accumulator(),
            [Self::DUMMY_H; 2].map(fe_to_fe),
            PoseidonTranscriptChip::<C>::dummy_proof(&self.avp),
        );
    }

    fn update_acc(&mut self) {
        self.acc = Value::known(self.avp.init_accumulator());
        self.acc_prime = Value::known(self.avp.init_accumulator());
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
            ProperCrtUint<C::Scalar>,
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
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

    fn synthesize_accumulation_verifier(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        config: <RecursiveCircuit<C, Sc> as halo2_base::halo2_proofs::plonk::Circuit<C::Scalar>>::Config,
        input: &[AssignedValue<C::Scalar>],
        output: &[AssignedValue<C::Scalar>],
    ) -> Result<(), Error> {
        let Self {
            tcc_chip,
            transcript_config,
            avp,
            ..
        } = &self;

        let mut binding = self.inner.borrow_mut();
        let builder = binding.pool(0);  
        let acc_verifier = ProtostarAccumulationVerifier::new(avp.clone(), tcc_chip.clone());

        let zero = builder.main().load_zero();
        let one = builder.main().load_constant(C::Scalar::ONE);
        let vp_digest = tcc_chip.assign_witness(builder, avp.vp_digest)?;
        let step_idx = tcc_chip.assign_witness(
            builder,
            C::Scalar::from(self.step_circuit.step_idx() as u64),)?;
        let step_idx_plus_one = tcc_chip.add(builder, &step_idx, &one)?;
        let initial_input = self
            .step_circuit
            .initial_input()
            .iter()
            .map(|value| tcc_chip.assign_witness(builder, *value))
            .try_collect::<_, Vec<_>, _>()?;

        let is_base_case = tcc_chip.is_equal(builder, &step_idx, &zero)?;
        let h_prime = tcc_chip.assign_witness(builder, self.h_prime.assign().unwrap())?;
        self.check_initial_condition(builder, &is_base_case, &initial_input, input)?;

        let acc = acc_verifier.assign_accumulator(builder, self.acc.as_ref())?;
        let (nark, acc_r_nark, acc_prime) = {
            let instances =
                [&self.incoming_instances[0], &self.incoming_instances[1]].map(Value::as_ref);
            let proof = self.incoming_proof.clone();
            let transcript =
                &mut PoseidonTranscriptChip::new(builder.main(), transcript_config.clone(), tcc_chip.clone(), proof);
            acc_verifier.verify_accumulation_from_nark(builder, &acc, instances, transcript)?
        };

        let acc_prime = {
            let acc_default = if self.is_primary {
                acc_verifier.assign_default_accumulator(builder)?
            } else {
                acc_r_nark
            };
            acc_verifier.select_accumulator(builder, &is_base_case, &acc_default, &acc_prime)?
        };
        
        let h_from_incoming = tcc_chip.fit_base_in_scalar(builder, &nark.instances[0][0])?;
        let h_ohs_from_incoming = tcc_chip.fit_base_in_scalar(builder, &nark.instances[0][1])?;

        self.check_state_hash(
            builder,
            Some(&is_base_case),
            &h_from_incoming,
            &vp_digest,
            &step_idx,
            &initial_input,
            &input,
            &acc,
        )?;

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

        let assigned_instances = &mut binding.assigned_instances;
        assert_eq!(
            assigned_instances.len(),
            1,
            "Circuit must have exactly 1 instance column"
        );
        assert!(assigned_instances[0].is_empty());
        assigned_instances[0].push(h_ohs_from_incoming);
        assigned_instances[0].push(h_prime);

        // sanity check that the circuit is satisfied
        //let instances = self.instances();
        //MockProver::run(19, &*binding, instances.clone()).unwrap().assert_satisfied();

        binding.synthesize(config.clone(), layouter.namespace(|| ""));

        let copy_manager = binding.pool(0).copy_manager.lock().unwrap();
        // println!("copy_manager.advice_equalities {:?}", copy_manager.advice_equalities.len());
        // println!("copy_manager.constant_equalities {:?}", copy_manager.constant_equalities.len());
        // println!("copy_manager.assigned_constants {:?}", copy_manager.assigned_constants.len());
        // println!("copy_manager.assigned_advices {:?}", copy_manager.assigned_advices.len());
        drop(copy_manager);

        binding.clear();
        drop(binding);

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
            step_circuit: self.step_circuit.without_witnesses(),
            tcc_chip: self.tcc_chip.clone(),
            hash_chip: self.hash_chip.clone(),
            hash_config: self.hash_config.clone(),
            transcript_config: self.transcript_config.clone(),
            avp: self.avp.clone(),
            h_prime: Value::unknown(),
            acc: Value::unknown(),
            acc_prime: Value::unknown(),
            incoming_instances: [Value::unknown(), Value::unknown()],
            incoming_proof: Value::unknown(),
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
        let (input, output) =
            StepCircuit::synthesize(&self.step_circuit, config.clone(), layouter.namespace(|| ""))?;
        
        let synthesize_accumulation_verifier_time = Instant::now();
        self.synthesize_accumulation_verifier(layouter.namespace(|| ""),config.clone(),  &input, &output)?;
        let duration_synthesize_accumulation_verifier = synthesize_accumulation_verifier_time.elapsed();
        println!("Time for synthesize_accumulation_verifier: {:?}", duration_synthesize_accumulation_verifier);

        Ok(())
    }
}

impl<'a, C, Sc> CircuitExt<C::Scalar> for RecursiveCircuit<C, Sc>
where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    fn instances(&self) -> Vec<Vec<C::Scalar>> {
        let mut instances = vec![vec![C::Scalar::ZERO; 2]];
        self.incoming_instances[1].map(|h_ohs| instances[0][0] = fe_to_fe(h_ohs));
        self.h_prime.map(|h_prime| instances[0][1] = h_prime);
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
    secondary_pp: ProtostarProverParam<C::Base, HyperPlonk<P2>>,
    secondary_atp: AT2::Param,
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
    pub vp_digest: C::Scalar,
    pub primary_vp: ProtostarVerifierParam<C::Scalar, HyperPlonk<P1>>,
    pub primary_hp: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    pub primary_arity: usize,
    pub secondary_vp: ProtostarVerifierParam<C::Base, HyperPlonk<P2>>,
    pub secondary_hp: OptimizedPoseidonSpec<C::Base, T, RATE>,
    pub secondary_arity: usize,
    pub _marker: PhantomData<C>,
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

    pub fn secondary_arity(&self) -> usize {
        self.secondary_arity
    }
}

#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn preprocess<C, P1, P2, S1, S2, AT1, AT2>(
    primary_num_vars: usize,
    primary_atp: AT1::Param,
    primary_step_circuit: S1,
    secondary_num_vars: usize,
    secondary_atp: AT2::Param,
    secondary_step_circuit: S2,
    circuit_params: BaseCircuitParams,
    mut rng: impl RngCore,
) -> Result<
    (
        Halo2Circuit<C::Scalar, RecursiveCircuit<C, S1>>,
        Halo2Circuit<C::Base, RecursiveCircuit<C::Secondary, S2>>,
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
    S2: StepCircuit<C::Secondary>,
    AT1: InMemoryTranscript,
    AT2: InMemoryTranscript,
{
    assert_eq!(Chip::<C>::NUM_HASH_BITS, Chip::<C::Secondary>::NUM_HASH_BITS);

    let primary_param = P1::setup(1 << primary_num_vars, 0, &mut rng).unwrap();
    let secondary_param = P2::setup(1 << secondary_num_vars, 0, &mut rng).unwrap();
    
    let primary_circuit = RecursiveCircuit::new(true, primary_step_circuit, None, circuit_params.clone());
    let mut primary_circuit =
        Halo2Circuit::new::<HyperPlonk<P1>>(primary_num_vars, primary_circuit, circuit_params.clone());

    let (primary_pp, primary_vp) = {
        let primary_circuit_info = primary_circuit.circuit_info_without_preprocess().unwrap();
        Protostar::<HyperPlonk<P1>>::preprocess(&primary_param, &primary_circuit_info).unwrap()
    };

    let secondary_circuit = RecursiveCircuit::new(
        false,
        secondary_step_circuit,
        Some(ProtostarAccumulationVerifierParam::from(&primary_vp)),
        circuit_params.clone(),
    );

    let mut secondary_circuit =
        Halo2Circuit::new::<HyperPlonk<P2>>(secondary_num_vars, secondary_circuit, circuit_params.clone());

    let (secondary_pp, secondary_vp) = {
        let secondary_circuit_info = secondary_circuit.circuit_info().unwrap();
        Protostar::<HyperPlonk<P2>>::preprocess(&secondary_param, &secondary_circuit_info).unwrap()
    };

    primary_circuit.update_witness(|circuit| {
        circuit.avp = ProtostarAccumulationVerifierParam::from(&secondary_vp);
        circuit.update_acc();
    });
    let primary_circuit_info = primary_circuit.circuit_info().unwrap();
    let (primary_pp, primary_vp) =
        Protostar::<HyperPlonk<P1>>::preprocess(&primary_param, &primary_circuit_info).unwrap();

    let vp_digest = fe_truncated_from_le_bytes(
        Keccak256::digest(bincode::serialize(&(&primary_vp, &secondary_vp)).unwrap()),
        Chip::<C>::NUM_HASH_BITS,
    );
    primary_circuit.update_witness(|circuit| circuit.init(vp_digest));
    secondary_circuit.update_witness(|circuit| circuit.init(fe_to_fe(vp_digest)));

    let ivc_pp = ProtostarIvcProverParam {
        primary_pp,
        primary_atp,
        secondary_pp,
        secondary_atp,
        _marker: PhantomData,
    };
    let ivc_vp = {
        ProtostarIvcVerifierParam {
            vp_digest,
            primary_vp,
            primary_hp: primary_circuit.circuit().hash_config.borrow().clone(),
            primary_arity: S1::arity(),
            secondary_vp,
            secondary_hp: secondary_circuit.circuit().hash_config.borrow().clone(),
            secondary_arity: S2::arity(),
            _marker: PhantomData,
        }
    };

    Ok((primary_circuit, secondary_circuit, ivc_pp, ivc_vp))
}

#[allow(clippy::type_complexity)]
pub fn prove_steps<'a, C, P1, P2, S1, S2, AT1, AT2>(
    ivc_pp: &ProtostarIvcProverParam<C, P1, P2, AT1, AT2>,
    primary_circuit: &mut Halo2Circuit<C::Scalar, RecursiveCircuit<C, S1>>,
    secondary_circuit: &mut Halo2Circuit<C::Base, RecursiveCircuit<C::Secondary, S2>>,
    num_steps: usize,
    mut rng: impl RngCore,
) -> Result<
    (
        ProtostarAccumulator<C::Scalar, P1>,
        ProtostarAccumulator<C::Base, P2>,
        Vec<C::Base>,
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
    S2: StepCircuit<C::Secondary>,
    AT1: TranscriptRead<P1::CommitmentChunk, C::Scalar>
        + TranscriptWrite<P1::CommitmentChunk, C::Scalar>
        + InMemoryTranscript,
    AT2: TranscriptRead<P2::CommitmentChunk, C::Base>
        + TranscriptWrite<P2::CommitmentChunk, C::Base>
        + InMemoryTranscript,

{
    let mut primary_acc = Protostar::<HyperPlonk<P1>>::init_accumulator(&ivc_pp.primary_pp)?;
    let mut secondary_acc = Protostar::<HyperPlonk<P2>>::init_accumulator(&ivc_pp.secondary_pp)?;

    for step_idx in 0..num_steps {
        let primary_acc_x = primary_acc.instance.clone();

        let timer = start_timer(|| {
            format!(
                "prove_accumulation_from_nark-primary-{}",
                ivc_pp.primary_pp.pp.num_vars
            )
        });
        let proof = {
            let mut transcript = AT1::new(ivc_pp.primary_atp.clone());
            Protostar::<HyperPlonk<P1>>::prove_accumulation_from_nark(
                &ivc_pp.primary_pp,
                &mut primary_acc,
                primary_circuit as &_,
                &mut transcript,
                &mut rng,
            )?;
            transcript.into_proof()
        };
        end_timer(timer);

        secondary_circuit.update_witness(|circuit| {
            circuit.update(
                primary_acc_x,
                primary_acc.instance.clone(),
                primary_circuit.instances()[0].clone().try_into().unwrap(),
                proof,
            );
        });

        if step_idx != num_steps - 1 {
            let secondary_acc_x = secondary_acc.instance.clone();

            let timer = start_timer(|| {
                format!(
                    "prove_accumulation_from_nark-secondary-{}",
                    ivc_pp.secondary_pp.pp.num_vars
                )
            });
            let proof = {
                let mut transcript = AT2::new(ivc_pp.secondary_atp.clone());
                Protostar::<HyperPlonk<P2>>::prove_accumulation_from_nark(
                    &ivc_pp.secondary_pp,
                    &mut secondary_acc,
                    secondary_circuit as &_,
                    &mut transcript,
                    &mut rng,
                )?;
                transcript.into_proof()
            };
            end_timer(timer);

            primary_circuit.update_witness(|circuit| {
                circuit.update(
                    secondary_acc_x,
                    secondary_acc.instance.clone(),
                    secondary_circuit.instances()[0].clone().try_into().unwrap(),
                    proof,
                );
            });
        } else {
            return Ok((
                primary_acc,
                secondary_acc,
                secondary_circuit.instances()[0].to_vec(),
            ));
        }
    }

    unreachable!()
}

pub fn prove_decider<C, P1, P2, AT1, AT2>(
    ivc_pp: &ProtostarIvcProverParam<C, P1, P2, AT1, AT2>,
    primary_acc: &ProtostarAccumulator<C::Scalar, P1>,
    primary_transcript: &mut impl TranscriptWrite<P1::CommitmentChunk, C::Scalar>,
    secondary_acc: &mut ProtostarAccumulator<C::Base, P2>,
    secondary_circuit: &impl PlonkishCircuit<C::Base>,
    secondary_transcript: &mut impl TranscriptWrite<P2::CommitmentChunk, C::Base>,
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
            "prove_decider_with_last_nark-secondary-{}",
            ivc_pp.secondary_pp.pp.num_vars
        )
    });
    Protostar::<HyperPlonk<P2>>::prove_decider_with_last_nark(
        &ivc_pp.secondary_pp,
        secondary_acc,
        secondary_circuit,
        secondary_transcript,
        &mut rng,
    )?;
    end_timer(timer);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn verify_decider<C, P1, P2>(
    ivc_vp: &ProtostarIvcVerifierParam<C, P1, P2>,
    num_steps: usize,
    primary_initial_input: &[C::Scalar],
    primary_output: &[C::Scalar],
    primary_acc: &ProtostarAccumulatorInstance<C::Scalar, P1::Commitment>,
    primary_transcript: &mut impl TranscriptRead<P1::CommitmentChunk, C::Scalar>,
    secondary_initial_input: &[C::Base],
    secondary_output: &[C::Base],
    secondary_acc_before_last: impl BorrowMut<ProtostarAccumulatorInstance<C::Base, P2::Commitment>>,
    secondary_last_instances: &[Vec<C::Base>],
    secondary_transcript: &mut impl TranscriptRead<P2::CommitmentChunk, C::Base>,
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
    if Chip::<C>::hash_state(
        &ivc_vp.primary_hp,
        ivc_vp.vp_digest,
        num_steps,
        primary_initial_input,
        primary_output,
        secondary_acc_before_last.borrow(),
    ) != fe_to_fe(secondary_last_instances[0][0])
    {
        return Err(crate::Error::InvalidSnark(
            "Invalid primary state hash".to_string(),
        ));
    }
    if Chip::<C::Secondary>::hash_state(
        &ivc_vp.secondary_hp,
        fe_to_fe(ivc_vp.vp_digest),
        num_steps,
        secondary_initial_input,
        secondary_output,
        primary_acc,
    ) != secondary_last_instances[0][1]
    {
        return Err(crate::Error::InvalidSnark(
            "Invalid secondary state hash".to_string(),
        ));
    }
    Protostar::<HyperPlonk<P1>>::verify_decider(
        &ivc_vp.primary_vp,
        primary_acc,
        primary_transcript,
        &mut rng,
    )?;
    Protostar::<HyperPlonk<P2>>::verify_decider_with_last_nark(
        &ivc_vp.secondary_vp,
        secondary_acc_before_last,
        secondary_last_instances,
        secondary_transcript,
        &mut rng,
    )?;
    Ok(())
}