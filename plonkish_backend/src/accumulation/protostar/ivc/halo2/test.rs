use crate::{
    accumulation::protostar::{
        ivc::halo2::{
            preprocess, prove_decider, prove_steps, verify_decider, HashInstruction,
            ProtostarHyperPlonkUtil, ProtostarIvcAggregator, ProtostarIvcVerifierParam,
            StepCircuit, TranscriptInstruction, TwoChainCurveInstruction,
        },
        ProtostarAccumulatorInstance, ProtostarVerifierParam,
    },
    backend::{
        hyperplonk::{HyperPlonk, HyperPlonkVerifierParam},
        PlonkishBackend, PlonkishCircuit,
    },
    frontend::halo2::{layouter::InstanceExtractor, CircuitExt, Halo2Circuit},
    pcs::{
        multilinear::{Gemini, MultilinearHyrax, MultilinearIpa},
        univariate::UnivariateKzg,
        AdditiveCommitment, PolynomialCommitmentScheme,
    },
    poly::multilinear::MultilinearPolynomial,
    util::{
        arithmetic::{
            fe_to_fe, CurveAffine, Field, FromUniformBytes, PrimeFieldBits,
            TwoChainCurve, MultiMillerLoop,
        },
        chain,
        test::seeded_std_rng,
        transcript::InMemoryTranscript,
        DeserializeOwned, Itertools, Serialize,
    },
};
use halo2_base::halo2_proofs::
    halo2curves::{bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta},
};
//use pairing::{Engine, MillerLoopResult, MultiMillerLoop, PairingCurveAffine};
use halo2_base::{Context,
    gates::{circuit::{builder::RangeCircuitBuilder, CircuitBuilderStage}, 
            flex_gate::{GateChip, GateInstructions}},
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error},
};
//use halo2_ecc::bn254::pairing;
use std::{fmt::Debug, hash::Hash, marker::PhantomData, convert::From};

#[derive(Clone, Debug, Default)]
struct TrivialCircuit<C> {
    step_idx: usize,
    _marker: PhantomData<C>,
}

impl<C> Circuit<C::Scalar> for TrivialCircuit<C>
where
    C: CurveAffine,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
    type Config = strawman::Config<C::Scalar>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        strawman::Config::configure::<C>(meta)
    }

    fn synthesize(&self, _: Self::Config, _: impl Layouter<C::Scalar>) -> Result<(), Error> {
        Ok(())
    }
}

impl<C> CircuitExt<C::Scalar> for TrivialCircuit<C>
where
    C: CurveAffine,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
    fn instances(&self) -> Vec<Vec<C::Scalar>> {
        Vec::new()
    }
}

impl<C: TwoChainCurve> StepCircuit<C> for TrivialCircuit<C>
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    type TccChip = strawman::Chip<C>;
    type HashChip = strawman::Chip<C>;
    type TranscriptChip = strawman::PoseidonTranscriptChip<C>;

    fn configs(
        config: Self::Config,
    ) -> (
        <Self::TccChip as TwoChainCurveInstruction<C>>::Config,
        <Self::HashChip as HashInstruction<C>>::Config,
        <Self::TranscriptChip as TranscriptInstruction<C>>::Config,
    ) {
        (
            config.clone(),
            config.poseidon_spec.clone(),
            config.poseidon_spec,
        )
    }

    fn arity() -> usize {
        0
    }

    fn initial_input(&self) -> &[C::Scalar] {
        &[]
    }

    fn input(&self) -> &[C::Scalar] {
        &[]
    }

    fn output(&self) -> &[C::Scalar] {
        &[]
    }

    fn step_idx(&self) -> usize {
        self.step_idx
    }

    fn next(&mut self) {
        self.step_idx += 1;
    }

    fn synthesize(
        &self,
        _: Self::Config,
        _: impl Layouter<C::Scalar>,
    ) -> Result<
        (
            Vec<AssignedCell<C::Scalar, C::Scalar>>,
            Vec<AssignedCell<C::Scalar, C::Scalar>>,
        ),
        Error,
    > {
        Ok((Vec::new(), Vec::new()))
    }
}

#[derive(Clone)]
struct SecondaryAggregationCircuit {
    vp_digest: grumpkin::Fr,
    vp: ProtostarVerifierParam<bn256::Fr, HyperPlonk<Gemini<UnivariateKzg<Bn256>>>>,
    arity: usize,
    instances: Vec<grumpkin::Fr>,
    num_steps: Value<usize>,
    initial_input: Value<Vec<grumpkin::Fr>>,
    output: Value<Vec<grumpkin::Fr>>,
    acc: Value<ProtostarAccumulatorInstance<bn256::Fr, bn256::G1Affine>>,
    proof: Value<Vec<u8>>,
}

impl Circuit<grumpkin::Fr> for SecondaryAggregationCircuit {
    type Config = strawman::Config<grumpkin::Fr>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(meta: &mut ConstraintSystem<grumpkin::Fr>) -> Self::Config {
        strawman::Config::configure::<grumpkin::G1Affine>(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<grumpkin::Fr>,
    ) -> Result<(), Error> {

        let chip = <strawman::Chip<grumpkin::G1Affine> as TwoChainCurveInstruction<
            grumpkin::G1Affine,
        >>::new(config);

        let mut builder = RangeCircuitBuilder::from_stage(CircuitBuilderStage::Keygen)
        .use_k(8)
        .use_lookup_bits(9);

        let aggregator = ProtostarIvcAggregator::new(
            self.vp_digest,
            self.vp.clone(),
            self.arity,
            chip.clone(),
            chip.clone(),
        );

        let mut transcript = strawman::PoseidonTranscriptChip::new(
            strawman::decider_transcript_param(),
            chip.clone(),
            self.proof.clone(),
        );

        let (num_steps, initial_input, output, h, lhs, rhs) = aggregator.aggregate_gemini_kzg_ivc(
            &mut layouter,
            builder.main(0),
            self.num_steps,
            self.initial_input.clone(),
            self.output.clone(),
            self.acc.clone(),
            &mut transcript,
        )?;

        let zero = chip.assign_constant(&mut layouter, grumpkin::Fr::ZERO)?;
        chip.constrain_equal(&mut layouter, lhs.is_identity(), &zero)?;
        chip.constrain_equal(&mut layouter, rhs.is_identity(), &zero)?;

        let cell_map = chip.layout_and_clear(&mut layouter)?;
        for (idx, witness) in chain![
            [num_steps],
            initial_input,
            output,
            [h, *lhs.x(), *lhs.y(), *rhs.x(), *rhs.y()]
        ]
        .enumerate()
        {
            layouter.constrain_instance(cell_map[&witness.id()].cell(), chip.instance, idx)?;
        }

        Ok(())
    }
}

impl CircuitExt<grumpkin::Fr> for SecondaryAggregationCircuit {
    fn instances(&self) -> Vec<Vec<grumpkin::Fr>> {
        vec![self.instances.clone()]
    }
}

#[derive(Clone)]
struct PrimaryAggregationCircuit {
    vp_digest: bn256::Fr,
    vp: ProtostarVerifierParam<grumpkin::Fr, HyperPlonk<MultilinearIpa<grumpkin::G1Affine>>>,
    primary_arity: usize,
    secondary_arity: usize,
    instances: Vec<bn256::Fr>,
    num_steps: Value<usize>,
    initial_input: Value<Vec<bn256::Fr>>,
    output: Value<Vec<bn256::Fr>>,
    acc_before_last: Value<ProtostarAccumulatorInstance<grumpkin::Fr, grumpkin::G1Affine>>,
    last_instance: Value<[grumpkin::Fr; 2]>,
    proof: Value<Vec<u8>>,
    secondary_aggregation_vp: HyperPlonkVerifierParam<grumpkin::Fr, MultilinearHyrax<grumpkin::G1Affine>>,
    secondary_aggregation_instances: Value<Vec<grumpkin::Fr>>,
    secondary_aggregation_proof: Value<Vec<u8>>,
}

impl Circuit<bn256::Fr> for PrimaryAggregationCircuit {
    type Config = strawman::Config<bn256::Fr>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(meta: &mut ConstraintSystem<bn256::Fr>) -> Self::Config {
        strawman::Config::configure::<bn256::G1Affine>(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<bn256::Fr>,
    ) -> Result<(), Error> {
        let chip =
            <strawman::Chip<bn256::G1Affine> as TwoChainCurveInstruction<bn256::G1Affine>>::new(
                config,
            );

        let mut builder = RangeCircuitBuilder::from_stage(CircuitBuilderStage::Keygen)
            .use_k(8)
            .use_lookup_bits(9);

        let aggregator = ProtostarIvcAggregator::new(
            self.vp_digest,
            self.vp.clone(),
            self.primary_arity,
            chip.clone(),
            chip.clone(),
        );

        let mut transcript = strawman::PoseidonTranscriptChip::new(
            strawman::decider_transcript_param(),
            chip.clone(),
            self.proof.clone(),
        );

        let (primary_num_steps, primary_initial_input, primary_output, h_ohs_from_last_nark) =
            aggregator.verify_ipa_grumpkin_ivc_with_last_nark(
                &mut layouter,
                builder.main(0),
                self.num_steps,
                self.initial_input.clone(),
                self.output.clone(),
                self.acc_before_last.clone(),
                self.last_instance,
                &mut transcript,
            )?;

        let (secondary_initial_input, secondary_output, pairing_acc) = {
            let mut transcript = strawman::PoseidonTranscriptChip::new(
                strawman::decider_transcript_param(),
                chip.clone(),
                self.secondary_aggregation_proof.clone(),
            );
            let secondary_aggregation_instance = chip.verify_hyrax_hyperplonk(
                &mut layouter,
                builder.main(0),
                &self.secondary_aggregation_vp,
                self.secondary_aggregation_instances
                    .as_ref()
                    .map(Vec::as_slice),
                &mut transcript,
            )?;

            let secondary_num_steps =
                chip.fit_base_in_scalar(&mut layouter, &secondary_aggregation_instance[0])?;
            chip.constrain_equal(&mut layouter, &primary_num_steps, &secondary_num_steps)?;

            let h = chip.fit_base_in_scalar(
                &mut layouter,
                &secondary_aggregation_instance[1 + 2 * self.secondary_arity],
            )?;
            chip.constrain_equal(&mut layouter, &h_ohs_from_last_nark, &h)?;

            let iter = &mut secondary_aggregation_instance.iter();
            let mut instances = |skip: usize, take: usize| {
                iter.skip(skip)
                    .take(take)
                    .map(|base| chip.to_repr_base(&mut layouter, base))
                    .try_collect::<_, Vec<_>, _>()
            };
            (
                instances(1, self.secondary_arity)?,
                instances(0, self.secondary_arity)?,
                instances(1, 4 * strawman::NUM_LIMBS)?,
            )
        };

        let cell_map = chip.layout_and_clear(&mut layouter)?;
        for (idx, witness) in chain![
            [primary_num_steps],
            primary_initial_input,
            primary_output,
            secondary_initial_input.into_iter().flatten(),
            secondary_output.into_iter().flatten(),
            pairing_acc.into_iter().flatten(),
        ]
        .enumerate()
        {
            layouter.constrain_instance(cell_map[&witness.id()].cell(), chip.instance, idx)?;
        }

        Ok(())
    }
}

impl CircuitExt<bn256::Fr> for PrimaryAggregationCircuit {
    fn instances(&self) -> Vec<Vec<bn256::Fr>> {
        vec![self.instances.clone()]
    }
}

#[allow(clippy::type_complexity)]
fn run_protostar_hyperplonk_ivc<C, P1, P2>(
    num_vars: usize,
    num_steps: usize,
) -> (
    ProtostarIvcVerifierParam<
        C,
        P1,
        P2,
        <strawman::Chip<C> as HashInstruction<C>>::Param,
        <strawman::Chip<C::Secondary> as HashInstruction<C::Secondary>>::Param,
    >,
    usize,
    Vec<C::Scalar>,
    Vec<C::Scalar>,
    ProtostarAccumulatorInstance<C::Scalar, P1::Commitment>,
    Vec<u8>,
    Vec<C::Base>,
    Vec<C::Base>,
    ProtostarAccumulatorInstance<C::Base, P2::Commitment>,
    Vec<C::Base>,
    Vec<u8>,
)
where
    C: TwoChainCurve,
    C::Base: BigPrimeField + PrimeFieldBits + Serialize + DeserializeOwned,
    C::Scalar: BigPrimeField + PrimeFieldBits + Serialize + DeserializeOwned,
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
    let primary_num_vars = num_vars;
    let primary_atp = strawman::accumulation_transcript_param();
    let secondary_num_vars = num_vars;
    let secondary_atp = strawman::accumulation_transcript_param();

    let (mut primary_circuit, mut secondary_circuit, ivc_pp, ivc_vp) = preprocess::<
        C,
        P1,
        P2,
        _,
        _,
        strawman::PoseidonTranscript<_, _>,
        strawman::PoseidonTranscript<_, _>,
    >(
        primary_num_vars,
        primary_atp,
        TrivialCircuit::default(),
        secondary_num_vars,
        secondary_atp,
        TrivialCircuit::default(),
        seeded_std_rng(),
    )
    .unwrap();

    let (primary_acc, mut secondary_acc, secondary_last_instances) = prove_steps(
        &ivc_pp,
        &mut primary_circuit,
        &mut secondary_circuit,
        num_steps,
        seeded_std_rng(),
    )
    .unwrap();

    let primary_dtp = strawman::decider_transcript_param();
    let secondary_dtp = strawman::decider_transcript_param();

    let (
        primary_acc,
        primary_initial_input,
        primary_output,
        primary_proof,
        secondary_acc_before_last,
        secondary_initial_input,
        secondary_output,
        secondary_proof,
    ) = {
        let secondary_acc_before_last = secondary_acc.instance.clone();
        let mut primary_transcript = strawman::PoseidonTranscript::new(primary_dtp.clone());
        let mut secondary_transcript = strawman::PoseidonTranscript::new(secondary_dtp.clone());
        prove_decider(
            &ivc_pp,
            &primary_acc,
            &mut primary_transcript,
            &mut secondary_acc,
            &secondary_circuit,
            &mut secondary_transcript,
            seeded_std_rng(),
        )
        .unwrap();

        (
            primary_acc.instance,
            StepCircuit::<C>::initial_input(&primary_circuit.circuit().step_circuit),
            StepCircuit::<C>::output(&primary_circuit.circuit().step_circuit),
            primary_transcript.into_proof(),
            secondary_acc_before_last,
            StepCircuit::<C::Secondary>::initial_input(&secondary_circuit.circuit().step_circuit),
            StepCircuit::<C::Secondary>::output(&secondary_circuit.circuit().step_circuit),
            secondary_transcript.into_proof(),
        )
    };

    let result = {
        let mut primary_transcript =
            strawman::PoseidonTranscript::from_proof(primary_dtp, primary_proof.as_slice());
        let mut secondary_transcript =
            strawman::PoseidonTranscript::from_proof(secondary_dtp, secondary_proof.as_slice());
        verify_decider::<_, _, _, strawman::Chip<_>, strawman::Chip<_>>(
            &ivc_vp,
            num_steps,
            primary_initial_input,
            primary_output,
            &primary_acc,
            &mut primary_transcript,
            secondary_initial_input,
            secondary_output,
            secondary_acc_before_last.clone(),
            &[secondary_last_instances.clone()],
            &mut secondary_transcript,
            seeded_std_rng(),
        )
    };
    assert_eq!(result, Ok(()));

    (
        ivc_vp,
        num_steps,
        primary_initial_input.to_vec(),
        primary_output.to_vec(),
        primary_acc,
        primary_proof,
        secondary_initial_input.to_vec(),
        secondary_output.to_vec(),
        secondary_acc_before_last,
        secondary_last_instances,
        secondary_proof,
    )
}

#[test]
fn gemini_kzg_ipa_protostar_hyperplonk_ivc() {
    const NUM_VARS: usize = 14;
    const NUM_STEPS: usize = 3;
    run_protostar_hyperplonk_ivc::<
        bn256::G1Affine,
        Gemini<UnivariateKzg<Bn256>>,
        MultilinearIpa<grumpkin::G1Affine>,
    >(NUM_VARS, NUM_STEPS);
}

// #[test]
// fn gemini_kzg_ipa_protostar_hyperplonk_ivc_ipa() {
//     const NUM_VARS: usize = 14;
//     const NUM_STEPS: usize = 3;
//     run_protostar_hyperplonk_ivc::<
//         bn256::G1Affine,
//         MultilinearIpa<Bn256::G1Affine>,
//         MultilinearIpa<grumpkin::G1Affine>,
//     >(NUM_VARS, NUM_STEPS);
// }

#[test]
fn gemini_kzg_ipa_protostar_hyperplonk_ivc_with_aggregation() {
    const NUM_VARS: usize = 14;
    const NUM_STEPS: usize = 3;
    let (
        ivc_vp,
        num_steps,
        primary_initial_input,
        primary_output,
        primary_acc,
        primary_proof,
        secondary_initial_input,
        secondary_output,
        secondary_acc_before_last,
        secondary_last_instances,
        secondary_proof,
    ) = run_protostar_hyperplonk_ivc::<
        bn256::G1Affine,
        Gemini<UnivariateKzg<Bn256>>,
        MultilinearIpa<grumpkin::G1Affine>,
    >(NUM_VARS, NUM_STEPS);

    let (secondary_aggregation_vp, secondary_aggregation_instances, secondary_aggregation_proof) = {
        let mut circuit = SecondaryAggregationCircuit {
            vp_digest: fe_to_fe(ivc_vp.vp_digest),
            vp: ivc_vp.primary_vp.clone(),
            arity: ivc_vp.secondary_arity,
            instances: Vec::new(),
            num_steps: Value::known(num_steps),
            initial_input: Value::known(secondary_initial_input),
            output: Value::known(secondary_output),
            acc: Value::known(primary_acc.unwrap_comm()),
            proof: Value::known(primary_proof),
        };
        circuit.instances = InstanceExtractor::extract(&circuit)
            .unwrap()
            .into_iter()
            .next()
            .unwrap();
        assert_eq!(
            circuit.instances[1 + 2 * ivc_vp.secondary_arity],
            secondary_last_instances[1]
        );

        type HyraxHyperPlonk = HyperPlonk<MultilinearHyrax<grumpkin::G1Affine>>;
        let circuit = Halo2Circuit::new::<HyraxHyperPlonk>(17, circuit);
        let circuit_info = circuit.circuit_info().unwrap();

        let param = HyraxHyperPlonk::setup(&circuit_info, seeded_std_rng()).unwrap();
        let (pp, vp) = HyraxHyperPlonk::preprocess(&param, &circuit_info).unwrap();
        let dtp = strawman::decider_transcript_param();
        let proof = {
            let mut transcript = strawman::PoseidonTranscript::new(dtp.clone());
            HyraxHyperPlonk::prove(&pp, &circuit, &mut transcript, seeded_std_rng()).unwrap();
            transcript.into_proof()
        };
        let result = {
            let mut transcript = strawman::PoseidonTranscript::from_proof(dtp, proof.as_slice());
            HyraxHyperPlonk::verify(&vp, circuit.instances(), &mut transcript, seeded_std_rng())
        };
        assert_eq!(result, Ok(()));

        (vp, circuit.instances().to_vec(), proof)
    };

    {
        let mut circuit = PrimaryAggregationCircuit {
            vp_digest: fe_to_fe(ivc_vp.vp_digest),
            vp: ivc_vp.secondary_vp.clone(),
            primary_arity: ivc_vp.primary_arity,
            secondary_arity: ivc_vp.secondary_arity,
            instances: Vec::new(),
            num_steps: Value::known(num_steps),
            initial_input: Value::known(primary_initial_input),
            output: Value::known(primary_output),
            acc_before_last: Value::known(secondary_acc_before_last.unwrap_comm()),
            last_instance: Value::known([secondary_last_instances[0], secondary_last_instances[1]]),
            proof: Value::known(secondary_proof),
            secondary_aggregation_vp,
            secondary_aggregation_instances: Value::known(
            secondary_aggregation_instances[0].clone(),
            ),
            secondary_aggregation_proof: Value::known(secondary_aggregation_proof),
        };
        circuit.instances = InstanceExtractor::extract(&circuit)
            .unwrap()
            .into_iter()
            .next()
            .unwrap();

        type GeminiHyperPlonk = HyperPlonk<Gemini<UnivariateKzg<Bn256>>>;
        let circuit = Halo2Circuit::new::<GeminiHyperPlonk>(21, circuit);
        let circuit_info = circuit.circuit_info().unwrap();

        let param = GeminiHyperPlonk::setup(&circuit_info, seeded_std_rng()).unwrap();
        let (pp, vp) = GeminiHyperPlonk::preprocess(&param, &circuit_info).unwrap();
        let dtp = strawman::decider_transcript_param();
        let proof = {
            let mut transcript = strawman::PoseidonTranscript::new(dtp.clone());
            GeminiHyperPlonk::prove(&pp, &circuit, &mut transcript, seeded_std_rng()).unwrap();
            transcript.into_proof()
        };
        let result = {
            let mut transcript = strawman::PoseidonTranscript::from_proof(dtp, proof.as_slice());
            GeminiHyperPlonk::verify(&vp, circuit.instances(), &mut transcript, seeded_std_rng())
        };
        assert_eq!(result, Ok(()));

        let pairing_acc =
            &circuit.instances()[0][circuit.instances()[0].len() - 4 * strawman::NUM_LIMBS..];
        let [lhs_x, lhs_y, rhs_x, rhs_y] = [0, 1, 2, 3].map(|idx| {
            let offset = idx * strawman::NUM_LIMBS;
            strawman::fe_from_limbs(
                &pairing_acc[offset..offset + strawman::NUM_LIMBS],
                strawman::NUM_LIMB_BITS,
            )
        });
        let lhs = bn256::G1Affine::from_xy(lhs_x, lhs_y).unwrap();
        let rhs = bn256::G1Affine::from_xy(rhs_x, rhs_y).unwrap();
        // assert!(Bn256::pairings_product_is_identity(&[
        //     (&lhs, &(-ivc_vp.primary_vp.vp.pcs.g2()).into()),
        //     (&rhs, &ivc_vp.primary_vp.vp.pcs.s_g2().into()),
        // ]));
    }
}

mod strawman {
    use crate::{
        accumulation::protostar::{
            ivc::halo2::{
                AssignedProtostarAccumulatorInstance, HashInstruction, TranscriptInstruction,
                TwoChainCurveInstruction,
            },
            ProtostarAccumulatorInstance,
        },
        frontend::halo2::chip::halo2_wrong::{
            from_le_bits, integer_to_native, sum_with_coeff, to_le_bits_strict, PoseidonChip,
        },
        util::{
            arithmetic::{
                fe_from_bool, fe_from_le_bytes, fe_to_fe, fe_truncated, BitField, CurveAffine,
                Field, FromUniformBytes, Group, PrimeCurveAffine, PrimeField, PrimeFieldBits,
                TwoChainCurve, OverridenCurveAffine,
            },
            hash::{poseidon::Spec, Poseidon},
            izip_eq,
            transcript::{
                FieldTranscript, FieldTranscriptRead, FieldTranscriptWrite, InMemoryTranscript,
                Transcript, TranscriptRead, TranscriptWrite,
            },
            Itertools,
        },
    };
    use halo2_base::{Context, utils::{BigPrimeField, ScalarField}, 
        halo2_proofs::plonk::Assigned};

    use halo2_proofs::{
        circuit::{AssignedCell, Layouter, Value},
        plonk::{Column, ConstraintSystem, Error, Instance},
    };

    use halo2_ecc::{
        fields::{fp::FpChip, FieldChip, native_fp::NativeFieldChip, Selectable},
        bigint::{CRTInteger, FixedCRTInteger, ProperCrtUint},
        ecc::{fixed_base, scalar_multiply, EcPoint, EccChip},
    };
    use halo2_base::gates::flex_gate::threads::SinglePhaseCoreManager;
    use halo2_base::gates::{circuit::builder::BaseCircuitBuilder, RangeChip,flex_gate::{GateChip, GateInstructions}};

    use std::{
        cell::RefCell,
        collections::BTreeMap,
        fmt::{self, Debug},
        io::{self, Cursor, Read},
        iter,
        marker::PhantomData,
        ops::DerefMut,
        rc::Rc,
        hash::Hash,
    };

    pub const NUM_LIMBS: usize = 4;
    pub const NUM_LIMB_BITS: usize = 65;
    const NUM_SUBLIMBS: usize = 5;
    const NUM_LOOKUPS: usize = 1;
    pub const LOOKUP_BITS: usize = 8;

    const T: usize = 5;
    const RATE: usize = 4;
    const R_F: usize = 8;
    const R_P: usize = 60;

    const NUM_CHALLENGE_BITS: usize = 128;
    const NUM_CHALLENGE_BYTES: usize = NUM_CHALLENGE_BITS / 8;

    const NUM_HASH_BITS: usize = 250;

    fn fe_to_limbs<F1: PrimeFieldBits, F2: PrimeField>(fe: F1, num_limb_bits: usize) -> Vec<F2> {
        fe.to_le_bits()
            .chunks(num_limb_bits)
            .into_iter()
            .map(|bits| match bits.len() {
                1..=64 => F2::from(bits.load_le()),
                65..=128 => {
                    let lo = bits[..64].load_le::<u64>();
                    let hi = bits[64..].load_le::<u64>();
                    F2::from(hi) * F2::from(2).pow_vartime([64]) + F2::from(lo)
                }
                _ => unimplemented!(),
            })
            .take(NUM_LIMBS)
            .collect()
    }

    pub fn fe_from_limbs<F1: PrimeFieldBits, F2: PrimeField>(
        limbs: &[F1],
        num_limb_bits: usize,
    ) -> F2 {
        limbs.iter().rev().fold(F2::ZERO, |acc, limb| {
            acc * F2::from_u128(1 << num_limb_bits) + fe_to_fe::<F1, F2>(*limb)
        })
    }

    fn x_y_is_identity<C: CurveAffine>(ec_point: &C) -> [C::Base; 3] {
        let coords = ec_point.coordinates().unwrap();
        let is_identity = (coords.x().is_zero() & coords.y().is_zero()).into();
        [*coords.x(), *coords.y(), fe_from_bool(is_identity)]
    }

    pub fn accumulation_transcript_param<F: FromUniformBytes<64>>() -> Spec<F, T, RATE> {
        Spec::new(R_F, R_P)
    }

    pub fn decider_transcript_param<F: FromUniformBytes<64>>() -> Spec<F, T, RATE> {
        Spec::new(R_F, R_P)
    }

    #[derive(Debug)]
    pub struct PoseidonTranscript<F: PrimeField, S> {
        state: Poseidon<F, T, RATE>,
        stream: S,
    }

    impl<F: FromUniformBytes<64>> InMemoryTranscript for PoseidonTranscript<F, Cursor<Vec<u8>>> {
        type Param = Spec<F, T, RATE>;

        fn new(spec: Self::Param) -> Self {
            Self {
                state: Poseidon::new_with_spec(spec),
                stream: Default::default(),
            }
        }

        fn into_proof(self) -> Vec<u8> {
            self.stream.into_inner()
        }

        fn from_proof(spec: Self::Param, proof: &[u8]) -> Self {
            Self {
                state: Poseidon::new_with_spec(spec),
                stream: Cursor::new(proof.to_vec()),
            }
        }
    }

    impl<F: PrimeFieldBits, N: FromUniformBytes<64>, S> FieldTranscript<F>
        for PoseidonTranscript<N, S>
    {
        fn squeeze_challenge(&mut self) -> F {
            let hash = self.state.squeeze();
            self.state.update(&[hash]);

            fe_from_le_bytes(&hash.to_repr().as_ref()[..NUM_CHALLENGE_BYTES])
        }

        fn common_field_element(&mut self, fe: &F) -> Result<(), crate::Error> {
            self.state.update(&fe_to_limbs(*fe, NUM_LIMB_BITS));

            Ok(())
        }
    }

    impl<F: PrimeFieldBits, N: FromUniformBytes<64>, R: io::Read> FieldTranscriptRead<F>
        for PoseidonTranscript<N, R>
    {
        fn read_field_element(&mut self) -> Result<F, crate::Error> {
            let mut repr = <F as PrimeField>::Repr::default();
            self.stream
                .read_exact(repr.as_mut())
                .map_err(|err| crate::Error::Transcript(err.kind(), err.to_string()))?;
            let fe = F::from_repr_vartime(repr).ok_or_else(|| {
                crate::Error::Transcript(
                    io::ErrorKind::Other,
                    "Invalid field element encoding in proof".to_string(),
                )
            })?;
            self.common_field_element(&fe)?;
            Ok(fe)
        }
    }

    impl<F: PrimeFieldBits, N: FromUniformBytes<64>, W: io::Write> FieldTranscriptWrite<F>
        for PoseidonTranscript<N, W>
    {
        fn write_field_element(&mut self, fe: &F) -> Result<(), crate::Error> {
            self.common_field_element(fe)?;
            let repr = fe.to_repr();
            self.stream
                .write_all(repr.as_ref())
                .map_err(|err| crate::Error::Transcript(err.kind(), err.to_string()))
        }
    }

    impl<C: CurveAffine, S> Transcript<C, C::Scalar> for PoseidonTranscript<C::Base, S>
    where
        C::Base: FromUniformBytes<64>,
        C::Scalar: PrimeFieldBits,
    {
        fn common_commitment(&mut self, ec_point: &C) -> Result<(), crate::Error> {
            self.state.update(&x_y_is_identity(ec_point));
            Ok(())
        }
    }

    impl<C: CurveAffine, R: io::Read> TranscriptRead<C, C::Scalar> for PoseidonTranscript<C::Base, R>
    where
        C::Base: FromUniformBytes<64>,
        C::Scalar: PrimeFieldBits,
    {
        fn read_commitment(&mut self) -> Result<C, crate::Error> {
            let mut reprs = [<C::Base as PrimeField>::Repr::default(); 2];
            for repr in &mut reprs {
                self.stream
                    .read_exact(repr.as_mut())
                    .map_err(|err| crate::Error::Transcript(err.kind(), err.to_string()))?;
            }
            let [x, y] = reprs.map(<C::Base as PrimeField>::from_repr_vartime);
            let ec_point = x
                .zip(y)
                .and_then(|(x, y)| CurveAffine::from_xy(x, y).into())
                .ok_or_else(|| {
                    crate::Error::Transcript(
                        io::ErrorKind::Other,
                        "Invalid elliptic curve point encoding in proof".to_string(),
                    )
                })?;
            self.common_commitment(&ec_point)?;
            Ok(ec_point)
        }
    }

    impl<C: CurveAffine, W: io::Write> TranscriptWrite<C, C::Scalar> for PoseidonTranscript<C::Base, W>
    where
        C::Base: FromUniformBytes<64>,
        C::Scalar: PrimeFieldBits,
    {
        fn write_commitment(&mut self, ec_point: &C) -> Result<(), crate::Error> {
            self.common_commitment(ec_point)?;
            let coordinates = ec_point.coordinates().unwrap();
            for coordinate in [coordinates.x(), coordinates.y()] {
                let repr = coordinate.to_repr();
                self.stream
                    .write_all(repr.as_ref())
                    .map_err(|err| crate::Error::Transcript(err.kind(), err.to_string()))?;
            }
            Ok(())
        }
    }

    #[derive(Clone, Debug)]
    pub struct Config<F: ScalarField> {
        pub main_gate: MainGate<F, NUM_LOOKUPS>,
        pub instance: Column<Instance>,
        pub poseidon_spec: Spec<F, T, RATE>,
        pub range: RangeChip<F>,
    }

    impl<F: FromUniformBytes<64> + Ord + From<bool> + Hash> Config<F> {
        pub fn configure<C: CurveAffine<ScalarExt = F>>(meta: &mut ConstraintSystem<F>) -> Self {
            // let rns =
            //     Rns::<C::Base, C::Scalar, NUM_LIMBS, NUM_LIMB_BITS, NUM_SUBLIMBS>::construct();
            // let overflow_bit_lens = rns.overflow_lengths();
            // let composition_bit_len = IntegerChip::<
            //     C::Base,
            //     C::Scalar,
            //     NUM_LIMBS,
            //     NUM_LIMB_BITS,
            //     NUM_SUBLIMBS,
            // >::sublimb_bit_len();
            // let main_gate = MainGate::<_, NUM_LOOKUPS>::configure(
            //     meta,
            //     vec![composition_bit_len],
            //     overflow_bit_lens,
            // );
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            let poseidon_spec = Spec::new(R_F, R_P);
            let range = BaseCircuitBuilder::new(true).use_lookup_bits(8).range_chip();
            Self {
                main_gate,
                instance,
                poseidon_spec,
                range,
            }
        }
    }

    #[allow(clippy::type_complexity)]
    #[derive(Clone, Debug)]
    pub struct Chip<C: OverridenCurveAffine> 
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,
    {
        // rns: Rns<C::Base, C::Scalar, NUM_LIMBS, NUM_LIMB_BITS, NUM_SUBLIMBS>,
        // pub main_gate: MainGate<C::Scalar, NUM_LOOKUPS>,
        pub gate_chip: GateChip<C::Scalar>,
        pub base_chip: FpChip<C::Scalar, C::Base>,
        pub ecc_chip: EccChip<C::Scalar, FpChip<C::Scalar, C::Base>>,
        // pub collector: Rc<RefCell<Collector<C::Scalar>>>,
        // pub cell_map: Rc<RefCell<BTreeMap<u32, AssignedCell<C::Scalar, C::Scalar>>>>,
        pub instance: Column<Instance>,
        poseidon_spec: Spec<C::Scalar, T, RATE>,
        _marker: PhantomData<C>,
    }

    impl<C: TwoChainCurve> Chip<C> 
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,
    {
        // #[allow(clippy::type_complexity)]
        // pub fn layout_and_clear(
        //     &self,
        //     layouter: &mut impl Layouter<C::Scalar>,
        // ) -> Result<BTreeMap<u32, AssignedCell<C::Scalar, C::Scalar>>, Error> {
        //     let cell_map = self.main_gate.layout(layouter, &self.collector.borrow())?;
        //     *self.collector.borrow_mut() = Default::default();
        //     Ok(cell_map)
        // }

        // fn double_ec_point_incomplete(
        //     &self,
        //     value: &AssignedEcPoint<C::Secondary>,
        // ) -> AssignedEcPoint<C::Secondary> {
        //     let collector = &mut self.collector.borrow_mut();
        //     let two = C::Scalar::ONE.double();
        //     let three = two + C::Scalar::ONE;
        //     let lambda_numer =
        //         collector.mul_add_constant_scaled(three, value.x(), value.x(), C::Secondary::a());
        //     let y_doubled = collector.add(value.y(), value.y());
        //     let (lambda_denom_inv, _) = collector.inv(&y_doubled);
        //     let lambda = collector.mul(&lambda_numer, &lambda_denom_inv);
        //     let lambda_square = collector.mul(&lambda, &lambda);
        //     let out_x = collector.add_scaled(
        //         &Scaled::new(&lambda_square, C::Scalar::ONE),
        //         &Scaled::new(value.x(), -two),
        //     );
        //     let out_y = {
        //         let x_diff = collector.sub(value.x(), &out_x);
        //         let lambda_x_diff = collector.mul(&lambda, &x_diff);
        //         collector.sub(&lambda_x_diff, value.y())
        //     };
        //     AssignedEcPoint {
        //         ec_point: (value.ec_point + value.ec_point).map(Into::into),
        //         x: out_x,
        //         y: out_y,
        //         is_identity: *value.is_identity(),
        //     }
        // }

        // #[allow(clippy::type_complexity)]
        // fn add_ec_point_inner(
        //     &self,
        //     lhs: &AssignedEcPoint<C::Secondary>,
        //     rhs: &AssignedEcPoint<C::Secondary>,
        // ) -> (
        //     AssignedEcPoint<C::Secondary>,
        //     Witness<C::Scalar>,
        //     Witness<C::Scalar>,
        // ) {
        //     let collector = &mut self.collector.borrow_mut();
        //     let x_diff = collector.sub(rhs.x(), lhs.x());
        //     let y_diff = collector.sub(rhs.y(), lhs.y());
        //     let (x_diff_inv, is_x_equal) = collector.inv(&x_diff);
        //     let (_, is_y_equal) = collector.inv(&y_diff);
        //     let lambda = collector.mul(&y_diff, &x_diff_inv);
        //     let lambda_square = collector.mul(&lambda, &lambda);
        //     let out_x = sum_with_coeff(
        //         collector,
        //         [
        //             (&lambda_square, C::Scalar::ONE),
        //             (lhs.x(), -C::Scalar::ONE),
        //             (rhs.x(), -C::Scalar::ONE),
        //         ],
        //     );
        //     let out_y = {
        //         let x_diff = collector.sub(lhs.x(), &out_x);
        //         let lambda_x_diff = collector.mul(&lambda, &x_diff);
        //         collector.sub(&lambda_x_diff, lhs.y())
        //     };
        //     let out_x = collector.select(rhs.is_identity(), lhs.x(), &out_x);
        //     let out_x = collector.select(lhs.is_identity(), rhs.x(), &out_x);
        //     let out_y = collector.select(rhs.is_identity(), lhs.y(), &out_y);
        //     let out_y = collector.select(lhs.is_identity(), rhs.y(), &out_y);
        //     let out_is_identity = collector.mul(lhs.is_identity(), rhs.is_identity());

        //     let out = AssignedEcPoint {
        //         ec_point: (lhs.ec_point + rhs.ec_point).map(Into::into),
        //         x: out_x,
        //         y: out_y,
        //         is_identity: out_is_identity,
        //     };
        //     (out, is_x_equal, is_y_equal)
        // }

        // fn double_ec_point(
        //     &self,
        //     value: &AssignedEcPoint<C::Secondary>,
        // ) -> AssignedEcPoint<C::Secondary> {
        //     let doubled = self.double_ec_point_incomplete(value);
        //     let collector = &mut self.collector.borrow_mut();
        //     let zero = collector.register_constant(C::Scalar::ZERO);
        //     let out_x = collector.select(value.is_identity(), &zero, doubled.x());
        //     let out_y = collector.select(value.is_identity(), &zero, doubled.y());
        //     AssignedEcPoint {
        //         ec_point: (value.ec_point + value.ec_point).map(Into::into),
        //         x: out_x,
        //         y: out_y,
        //         is_identity: *value.is_identity(),
        //     }
        // }
    }

    // #[derive(Clone)]
    // pub struct AssignedBase<F: PrimeField, N: PrimeField> {
    //     scalar: Integer<F, N, NUM_LIMBS, NUM_LIMB_BITS>,
    //     limbs: Vec<Witness<N>>,
    // }

    // impl<F: PrimeField, N: PrimeField> AssignedBase<F, N> {
    //     fn assigned_cells(&self) -> impl Iterator<Item = &Witness<N>> {
    //         self.limbs.iter()
    //     }
    // }

    // impl<F: PrimeField, N: PrimeField> Debug for AssignedBase<F, N> {
    //     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //         let mut s = f.debug_struct("AssignedBase");
    //         let mut value = None;
    //         self.scalar.value().map(|scalar| value = Some(scalar));
    //         if let Some(value) = value {
    //             s.field("scalar", &value).finish()
    //         } else {
    //             s.finish()
    //         }
    //     }
    // }

    // #[derive(Clone)]
    // pub struct AssignedEcPoint<C: CurveAffine> {
    //     ec_point: Value<C>,
    //     x: Witness<C::Base>,
    //     y: Witness<C::Base>,
    //     is_identity: Witness<C::Base>,
    // }

    // impl<C: CurveAffine> AssignedEcPoint<C> 
    // where
    //     C::Scalar: BigPrimeField,
    //     C::Base: BigPrimeField,
    // {
    //     pub fn x(&self) -> &Witness<C::Base> {
    //         &self.x
    //     }

    //     pub fn y(&self) -> &Witness<C::Base> {
    //         &self.y
    //     }

    //     pub fn is_identity(&self) -> &Witness<C::Base> {
    //         &self.is_identity
    //     }

    //     fn assigned_cells(&self) -> impl Iterator<Item = &Witness<C::Base>> {
    //         [self.x(), self.y(), self.is_identity()].into_iter()
    //     }
    // }

    // impl<C: CurveAffine> Debug for AssignedEcPoint<C> {
    //     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //         let mut s = f.debug_struct("AssignedEcPoint");
    //         let mut value = None;
    //         self.ec_point.map(|ec_point| value = Some(ec_point));
    //         if let Some(value) = value {
    //             s.field("ec_point", &value).finish()
    //         } else {
    //             s.finish()
    //         }
    //     }
    // }

    impl<C: TwoChainCurve> TwoChainCurveInstruction<C> for Chip<C> 
    where
        C::Scalar: PrimeField<Repr = [u8; 32]> + From<bool> + FromUniformBytes<64> + Hash,
        C::Base: PrimeField<Repr = [u8; 32]> + From<bool> + FromUniformBytes<64> + Hash,
    {
        type Config = Config<C::Scalar>;
        type Assigned = Assigned<C::Scalar>;
        type AssignedBase = ProperCrtUint<C::Scalar>;
        type AssignedSecondary = EcPoint<C::Secondary::Scalar, <FpChip<C::Secondary::Scalar, C::Secondary::Base> as FieldChip<C::Secondary::Scalar>>::FieldPoint>;

        fn new(config: Self::Config) -> Self {
            Chip {
                // rns: Rns::construct(),
                // main_gate: config.main_gate,
                gate_chip: GateChip::default(),
                base_chip: FpChip::<C::Scalar,C::Base>::new(&config.range, NUM_LIMB_BITS, NUM_LIMBS),
                ecc_chip: EccChip::new(&FpChip::<C::Secondary::Scalar,C::Secondary::Base>::new(&config.range, NUM_LIMB_BITS, NUM_LIMBS)),
                // collector: Default::default(),
                // cell_map: Default::default(),
                instance: config.instance,
                poseidon_spec: config.poseidon_spec,
                _marker: PhantomData,
            }
        }

        fn constrain_equal(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &Self::Assigned,
            rhs: &Self::Assigned,
        ) -> Result<(), Error> {
            Ok(builder.main().constrain_equal(Existing(lhs), Existing(rhs)))
        }
    
        fn assign_constant(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            constant: C::Scalar,
        ) -> Result<(), Error> {
            Ok(builder.main().load_constant(constant))
        }
    
        fn assign_witness(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: C::Scalar,
        ) -> Result<(), Error> {
            Ok(builder.main().load_witness(witness))
        }
    
        fn select(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            condition: &Self::Assigned,
            when_true: &Self::Assigned,
            when_false: &Self::Assigned,
        ) -> Result<Self::Assigned, Error> {
            Ok(self.gate_chip.select(builder.main(), Existing(when_true), Existing(when_false), Existing(condition)))
        }
    
        fn is_equal(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &Self::Assigned,
            rhs: &Self::Assigned,
        ) -> Result<Self::Assigned, Error> {
            Ok(self.gate_chip.is_equal(builder.main(), Existing(lhs), Existing(rhs)))
        }
    
        fn add(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &Self::Assigned,
            rhs: &Self::Assigned,
        ) -> Result<Self::Assigned, Error> {
            Ok(self.gate_chip.add(builder.main(), Existing(a), Existing(b)))
        }
    
        fn sub(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &Self::Assigned,
            rhs: &Self::Assigned,
        ) -> Result<Self::Assigned, Error> {
            Ok(self.gate_chip.sub(builder.main(), Existing(a), Existing(b)))
        }  
    
        fn mul(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &Self::Assigned,
            rhs: &Self::Assigned,
        ) -> Result<Self::Assigned, Error> {
            Ok(self.gate_chip.mul(builder.main(), Existing(a), Existing(b)))
        }

        fn constrain_equal_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &Self::AssignedBase,
            rhs: &Self::AssignedBase,
        ) -> Result<(), Error> {
            self.base_chip.assert_equal(builder.main(),lhs,rhs);
            Ok(())
        }
    
        fn assign_constant_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            constant: C::Base,
        ) -> Result<Self::AssignedBase, Error> {
            Ok(self.base_chip.load_constant(builder.main(),constant))
        }
    
        fn assign_witness_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: C::Base,
        ) -> Result<Self::AssignedBase, Error> {
            Ok(self.base_chip.load_private(builder.main(),witness))
        }    
    
        fn select_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            condition: Assigned<F>,
            when_true: &Self::AssignedBase,
            when_false: &Self::AssignedBase,
        ) -> Result<Self::AssignedBase, Error> {
            Ok(self.base_chip.select(builder.main(),when_true,when_false,condition))
        }
    
        fn fit_base_in_scalar(
            &self,
            value: &Self::AssignedBase,
        ) -> Result<Self::Assigned, Error> {
            Ok(value.native().clone())
        }
    
        fn to_repr_base(
            &self,
            value: &Self::AssignedBase,
        ) -> Result<Vec<Self::Assigned>, Error> {
            Ok(value.limbs().clone())
        }
    
        fn add_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            a: &Self::AssignedBase,
            b: &Self::AssignedBase,
        ) -> Result<Self::AssignedBase, Error> {
            let add = self.base_chip.add_no_carry(builder.main(), a, b);
                Ok(FixedCRTInteger::from_native(add.value.to_biguint().unwrap(), 
                    self.base_chip.num_limbs, self.base_chip.limb_bits).assign(
                    builder.main(),
                    self.base_chip.limb_bits,
                    self.base_chip.native_modulus(),
                ))
        }
    
        fn sub_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            a: &Self::AssignedBase,
            b: &Self::AssignedBase,
        ) -> Result<Self::AssignedBase, Error> {
            let sub = self.base_chip.sub_no_carry(builder.main(), a, b);
                Ok(FixedCRTInteger::from_native(sub.value.to_biguint().unwrap(), 
                    self.base_chip.num_limbs, self.base_chip.limb_bits).assign(
                    builder.main(),
                    self.base_chip.limb_bits,
                    self.base_chip.native_modulus(),
                ))
        }
    
        fn mul_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &Self::AssignedBase,
            rhs: &Self::AssignedBase,
        ) -> Result<Self::AssignedBase, Error> {
            Ok(self.base_chip.mul(builder.main(), lhs, rhs))
        }
    
        fn div_incomplete_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &Self::AssignedBase,
            rhs: &Self::AssignedBase,
        ) -> Result<Self::AssignedBase, Error> {
            Ok(self.base_chip.divide_unsafe(builder.main(), lhs, rhs))
        }

        fn constrain_equal_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &Self::AssignedSecondary,
            rhs: &Self::AssignedSecondary,
        ) -> Result<(), Error> {
            self.ecc_chip.assert_equal(builder.main(), lhs, rhs);
            Ok(())
        }

        // todo can we replace with unchecked versions
        fn assign_constant_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            constant: C::Secondary,
        ) -> Result<Self::AssignedSecondary, Error> {
            Ok(self.ecc_chip.assign_constant_point(builder.main(), constant))
        }

        fn assign_witness_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: C::Secondary,
        ) -> Result<Self::AssignedSecondary, Error> {
            Ok(self.ecc_chip.assign_point(builder.main(), witness))
        }

        fn select_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            condition: &Self::Assigned,
            when_true: &Self::AssignedSecondary,
            when_false: &Self::AssignedSecondary,
        ) -> Result<Self::AssignedSecondary, Error> {
            Ok(self.ecc_chip.select(builder.main(), lhs, rhs, false))
        }

        fn add_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &Self::AssignedSecondary,
            rhs: &Self::AssignedSecondary,
        ) -> Result<Self::AssignedSecondary, Error> {
            Ok(self.ecc_chip.add_unequal(builder.main(), lhs, rhs, false))
        }

        // todo SET MAX_BITS, WINDOW_BITS
        fn scalar_mul_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            base: &Self::AssignedSecondary,
            le_bits: &[Self::Assigned],
        ) -> Result<Self::AssignedSecondary, Error> {
            Ok(self.ecc_chip.scalar_mult(builder.main(), base, le_bits.to_vec(), 8,8))
        }

        // todo change the inputs where this is used
        fn fixed_base_msm_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            bases: &[C::Secondary],
            scalars: Vec<Vec<Self::AssignedBase>>,
        ) -> Result<Self::AssignedSecondary, Error>{
            Ok(self.ecc_chip.fixed_base_msm(builder, bases, scalars, 8))
        }

        fn variable_base_msm_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            bases: &[C::Secondary],
            scalars: Vec<Vec<Self::AssignedBase>>,
        ) -> Result<Self::AssignedSecondary, Error>{
            Ok(self.ecc_chip.variable_base_msm(builder, bases, scalars, 8))
        }

    }

    impl<C: TwoChainCurve> HashInstruction<C> for Chip<C>
    where
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {
        const NUM_HASH_BITS: usize = NUM_HASH_BITS;

        type Param = Spec<C::Scalar, T, RATE>;
        type Config = Spec<C::Scalar, T, RATE>;
        type TccChip = Chip<C>;

        fn new(_: Self::Config, chip: Self::TccChip) -> Self {
            chip
        }

        // fn hash_state<Comm: AsRef<C::Secondary>>(
        //     spec: &Self::Param,
        //     vp_digest: C::Scalar,
        //     step_idx: usize,
        //     initial_input: &[C::Scalar],
        //     output: &[C::Scalar],
        //     acc: &ProtostarAccumulatorInstance<C::Base, Comm>,
        // ) -> C::Scalar {
        //     let mut poseidon = Poseidon::new_with_spec(spec.clone());
        //     let fe_to_limbs = |fe| fe_to_limbs(fe, NUM_LIMB_BITS);
        //     let inputs = iter::empty()
        //         .chain([vp_digest, C::Scalar::from(step_idx as u64)])
        //         .chain(initial_input.iter().copied())
        //         .chain(output.iter().copied())
        //         .chain(fe_to_limbs(acc.instances[0][0]))
        //         .chain(fe_to_limbs(acc.instances[0][1]))
        //         .chain(
        //             acc.witness_comms
        //                 .iter()
        //                 .map(AsRef::as_ref)
        //                 .flat_map(x_y_is_identity),
        //         )
        //         .chain(acc.challenges.iter().copied().flat_map(fe_to_limbs))
        //         .chain(fe_to_limbs(acc.u))
        //         .chain(x_y_is_identity(acc.e_comm.as_ref()))
        //         .chain(acc.compressed_e_sum.map(fe_to_limbs).into_iter().flatten())
        //         .collect_vec();
        //     poseidon.update(&inputs);
        //     fe_truncated(poseidon.squeeze(), NUM_HASH_BITS)
        // }

        // fn hash_assigned_state(
        //     &self,
        //     vp_digest: &<Self::TccChip as TwoChainCurveInstruction<C>>::Assigned,
        //     step_idx: &<Self::TccChip as TwoChainCurveInstruction<C>>::Assigned,
        //     initial_input: &[<Self::TccChip as TwoChainCurveInstruction<C>>::Assigned],
        //     output: &[<Self::TccChip as TwoChainCurveInstruction<C>>::Assigned],
        //     acc: &AssignedProtostarAccumulatorInstance<
        //         <Self::TccChip as TwoChainCurveInstruction<C>>::AssignedBase,
        //         <Self::TccChip as TwoChainCurveInstruction<C>>::AssignedSecondary,
        //     >,
        // ) -> Result<<Self::TccChip as TwoChainCurveInstruction<C>>::Assigned, Error> {
        //     let collector = &mut self.collector.borrow_mut();
        //     let inputs = iter::empty()
        //         .chain([vp_digest, step_idx])
        //         .chain(initial_input)
        //         .chain(output)
        //         .chain(acc.instances[0][0].assigned_cells())
        //         .chain(acc.instances[0][1].assigned_cells())
        //         .chain(
        //             acc.witness_comms
        //                 .iter()
        //                 .flat_map(AssignedEcPoint::assigned_cells),
        //         )
        //         .chain(acc.challenges.iter().flat_map(AssignedBase::assigned_cells))
        //         .chain(acc.u.assigned_cells())
        //         .chain(acc.e_comm.assigned_cells())
        //         .chain(
        //             acc.compressed_e_sum
        //                 .as_ref()
        //                 .map(AssignedBase::assigned_cells)
        //                 .into_iter()
        //                 .flatten(),
        //         )
        //         .copied()
        //         .collect_vec();
        //     let mut poseidon_chip = PoseidonChip::from_spec(collector, self.poseidon_spec.clone());
        //     poseidon_chip.update(&inputs);
        //     let hash = poseidon_chip.squeeze(collector);
        //     let hash_le_bits = to_le_bits_strict(collector, &hash);
        //     Ok(from_le_bits(collector, &hash_le_bits[..NUM_HASH_BITS]))
        // }
    }

    #[derive(Clone, Debug)]
    pub struct PoseidonTranscriptChip<C: OverridenCurveAffine> 
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,
    {
        poseidon_chip: PoseidonChip<C::Scalar, T, RATE>,
        chip: Chip<C>,
        proof: Value<Cursor<Vec<u8>>>,
    }

    #[derive(Clone)]
    pub struct Challenge<F: PrimeField, N: PrimeField> {
        le_bits: Vec<Witness<N>>,
        scalar: AssignedBase<F, N>,
    }

    impl<F: PrimeField, N: PrimeField> Debug for Challenge<F, N> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let mut f = f.debug_struct("Challenge");
            self.scalar
                .scalar
                .value()
                .map(|scalar| f.field("scalar", &scalar));
            f.finish()
        }
    }

    impl<F: PrimeField, N: PrimeField> AsRef<AssignedBase<F, N>> for Challenge<F, N> {
        fn as_ref(&self) -> &AssignedBase<F, N> {
            &self.scalar
        }
    }

    impl<C> TranscriptInstruction<C> for PoseidonTranscriptChip<C>
    where
        C: TwoChainCurve,
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {
        type Config = Spec<C::Scalar, T, RATE>;
        type TccChip = Chip<C>;
        type Challenge = Challenge<C::Base, C::Scalar>;

        fn new(spec: Self::Config, chip: Self::TccChip, proof: Value<Vec<u8>>) -> Self {
            let poseidon_chip = PoseidonChip::from_spec(&mut chip.collector.borrow_mut(), spec);
            PoseidonTranscriptChip {
                poseidon_chip,
                chip,
                proof: proof.map(Cursor::new),
            }
        }

        fn challenge_to_le_bits(
            &self,
            challenge: &Self::Challenge,
        ) -> Result<Vec<Witness<C::Scalar>>, Error> {
            Ok(challenge.le_bits.clone())
        }

        fn common_field_element(
            &mut self,
            value: &AssignedBase<C::Base, C::Scalar>,
        ) -> Result<(), Error> {
            value
                .assigned_cells()
                .for_each(|value| self.poseidon_chip.update(&[*value]));
            Ok(())
        }

        fn common_commitment(
            &mut self,
            value: &AssignedEcPoint<C::Secondary>,
        ) -> Result<(), Error> {
            value
                .assigned_cells()
                .for_each(|value| self.poseidon_chip.update(&[*value]));
            Ok(())
        }

        fn read_field_element(
            &mut self,
            layouter: &mut impl Layouter<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            let fe = self.proof.as_mut().and_then(|proof| {
                let mut repr = <C::Base as PrimeField>::Repr::default();
                if proof.read_exact(repr.as_mut()).is_err() {
                    return Value::unknown();
                }
                C::Base::from_repr_vartime(repr)
                    .map(Value::known)
                    .unwrap_or_else(Value::unknown)
            });
            let fe = self.chip.assign_witness_base(layouter, fe)?;
            self.common_field_element(&fe)?;
            Ok(fe)
        }

        fn read_commitment(
            &mut self,
            layouter: &mut impl Layouter<C::Scalar>,
        ) -> Result<AssignedEcPoint<C::Secondary>, Error> {
            let comm = self.proof.as_mut().and_then(|proof| {
                let mut reprs = [<C::Scalar as PrimeField>::Repr::default(); 2];
                for repr in &mut reprs {
                    if proof.read_exact(repr.as_mut()).is_err() {
                        return Value::unknown();
                    }
                }
                let [x, y] = reprs.map(|repr| {
                    C::Scalar::from_repr_vartime(repr)
                        .map(Value::known)
                        .unwrap_or_else(Value::unknown)
                });
                x.zip(y).and_then(|(x, y)| {
                    Option::from(C::Secondary::from_xy(x, y))
                        .map(Value::known)
                        .unwrap_or_else(Value::unknown)
                })
            });
            let comm = self.chip.assign_witness_secondary(layouter, comm)?;
            self.common_commitment(&comm)?;
            Ok(comm)
        }

        fn squeeze_challenge(
            &mut self,
        ) -> Result<Challenge<C::Base, C::Scalar>, Error> {
            let collector = &mut self.chip.collector.borrow_mut();
            let (challenge_le_bits, challenge) = {
                let hash = self.poseidon_chip.squeeze(collector);
                self.poseidon_chip.update(&[hash]);

                let challenge_le_bits = to_le_bits_strict(collector, &hash)
                    .into_iter()
                    .take(NUM_CHALLENGE_BITS)
                    .collect_vec();
                let challenge = from_le_bits(collector, &challenge_le_bits);

                (challenge_le_bits, challenge)
            };

            let mut integer_chip = IntegerChip::new(collector, &self.chip.rns);
            let limbs = self.chip.rns.from_fe(challenge.value().map(fe_to_fe));
            let scalar = integer_chip.range(limbs, Range::Remainder);
            let limbs = scalar.limbs().iter().map(AsRef::as_ref).copied().collect();

            let scalar_in_base =
                integer_to_native(&self.chip.rns, collector, &scalar, NUM_CHALLENGE_BITS);
            collector.equal(&challenge, &scalar_in_base);

            Ok(Challenge {
                le_bits: challenge_le_bits,
                scalar: AssignedBase { scalar, limbs },
            })
        }
    }
}
