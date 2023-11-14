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
    iter,
    marker::PhantomData,
    mem,
    rc::Rc,
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
    poseidon::hasher::{PoseidonSponge, PoseidonHasher, spec::OptimizedPoseidonSpec, PoseidonHash}, halo2_proofs::dev::MockProver,
};

use halo2_ecc::{
    fields::native_fp::NativeFieldChip,
    fields::fp::FpChip,
    ecc::{EccChip, EcPoint}, bigint::ProperCrtUint,
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

pub const NUM_LIMBS: usize = 4;
pub const NUM_LIMB_BITS: usize = 65;
pub const T: usize = 5;
pub const RATE: usize = 4;
pub const R_F: usize = 8;
pub const R_P: usize = 60;
pub const SECURE_MDS: usize = 0;


mod test;
use test::strawman::{self, Chip};


type AssignedPlonkishNarkInstance<AssignedBase, AssignedSecondary> =
    PlonkishNarkInstance<AssignedBase, AssignedSecondary>;

type AssignedProtostarAccumulatorInstance<AssignedBase, AssignedSecondary> =
    ProtostarAccumulatorInstance<AssignedBase, AssignedSecondary>;


pub trait StepCircuit<C: TwoChainCurve>: Clone + Debug + CircuitExt<C::Scalar> 
where
    C::Scalar: BigPrimeField,
    C::Base: BigPrimeField,
{   

    // #[allow(clippy::type_complexity)]
    // fn configs(
    //     config: strawman::Config<C::Scalar>,
    // ) -> (
    //     //Chip<C>::Config,
    //     OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    //     OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    // );

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
        let r_le_bits = transcript.challenge_to_le_bits(&r)?;

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
                let timer = start_timer(|| format!("fold_accumulator_from_nark e_comm"));
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
        let poseidon_spec = OptimizedPoseidonSpec::new::<R_F, R_P,SECURE_MDS>();
        let hash_config = poseidon_spec.clone();
        let transcript_config = poseidon_spec.clone();

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
        let zero = tcc_chip.assign_constant(builder, C::Scalar::ZERO)?;
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
            let dummy_h = tcc_chip.assign_constant(builder, Self::DUMMY_H)?;
            tcc_chip.select_gatechip(builder, is_base_case, &dummy_h, &rhs)?
        } else {
            rhs
        };
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

        let zero = tcc_chip.assign_constant(builder, C::Scalar::ZERO)?;
        let one = tcc_chip.assign_constant(builder, C::Scalar::ONE)?;
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

        let h_from_incoming = tcc_chip.fit_base_in_scalar(&nark.instances[0][0])?;
        let h_ohs_from_incoming = tcc_chip.fit_base_in_scalar(&nark.instances[0][1])?;

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

        // todo check impl constrain instance these 
        // tcc_chip.constrain_instance(builder, &mut layouter, &h_ohs_from_incoming, 0)?;
        let assigned_instances = &mut binding.assigned_instances;
        assigned_instances[0].push(h_ohs_from_incoming);
        assigned_instances[0].push(h_from_incoming);

        binding.synthesize(config.clone(), layouter.namespace(|| ""));
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
        self.synthesize_accumulation_verifier(layouter.namespace(|| ""),config.clone(),  &input, &output)?;

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
        let mut instances = vec![vec![Self::DUMMY_H; 2]];
        self.incoming_instances[1].map(|h_ohs| instances[0][0] = fe_to_fe(h_ohs));
        self.h_prime.map(|h_prime| instances[0][1] = h_prime);
        instances
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
    vp_digest: C::Scalar,
    primary_vp: ProtostarVerifierParam<C::Scalar, HyperPlonk<P1>>,
    primary_hp: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    primary_arity: usize,
    secondary_vp: ProtostarVerifierParam<C::Base, HyperPlonk<P2>>,
    secondary_hp: OptimizedPoseidonSpec<C::Base, T, RATE>,
    secondary_arity: usize,
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

    fn barycentric_weights(
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

    fn barycentric_interpolate(
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
    fn verify_sum_check_and_query(
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
    fn multilinear_pcs_batch_verify<'a, Comm>(
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

    fn verify_ipa<'a>(
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
            //todo fix these for agg
            scalars.extend(chain![&xi_invs, &xis, [&h_scalar, &neg_c]].map(|scalar| scalar.clone()));
            // .map(|&scalar| scalar.clone()).collect()
            // let mut all_scalars = Vec::new();
            // all_scalars.push(scalars.iter().map(|&x| x.clone()).collect());
            // all_scalars.push(chain![&xi_invs, &xis, [&h_scalar, &neg_c]].map(|&scalar| scalar.clone()).collect());            

            bases.extend(chain![&ls, &rs, [&h, &g_k]]);
            let deref_bases: Vec<_> = bases.iter().map(|&x| x.clone()).collect();
            //let slice_bases: &[EcPoint<C::Scalar, AssignedValue<C::Scalar>>] = &deref_bases;            

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

    fn verify_hyrax(
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

    fn verify_hyrax_hyperplonk(
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

        let h_from_last_nark = tcc_chip.fit_base_in_scalar(&last_nark.instances[0][0])?;
        let h_ohs_from_last_nark =
            tcc_chip.fit_base_in_scalar(&last_nark.instances[0][1])?;
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

        // let mut all_scalars = Vec::new();
        // all_scalars.push(scalars.iter().map(|&x| x.clone()).collect());
        // all_scalars.push(chain![comm_scalars.into_iter().skip(1),[q_scalar, pi_scalar, g_scalar]].map(|scalar| scalar.clone()).collect());            

        bases.extend(chain![&fs, [&q, &pi, &g]]);
        let deref_bases: Vec<_> = bases.iter().map(|&x| x.clone()).collect();

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
