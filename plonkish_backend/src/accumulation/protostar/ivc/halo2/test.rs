use crate::{
    accumulation::protostar::{
        ivc::halo2::{
            preprocess, prove_decider, prove_steps, verify_decider,
            ProtostarIvcAggregator, ProtostarIvcVerifierParam,
            StepCircuit, CircuitExt
        },
        ProtostarAccumulatorInstance, ProtostarVerifierParam,
    },
    backend::{
        hyperplonk::{HyperPlonk, HyperPlonkVerifierParam},
        PlonkishBackend, PlonkishCircuit,
    },
    frontend::halo2::{layouter::InstanceExtractor, Halo2Circuit},
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
use halo2_base::{halo2_proofs::
    halo2curves::{bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta},
}, AssignedValue};
//use pairing::{Engine, MillerLoopResult, MultiMillerLoop, PairingCurveAffine};
use halo2_base::{Context,
    gates::{circuit::{builder::RangeCircuitBuilder, CircuitBuilderStage}, 
            flex_gate::{GateChip, GateInstructions}},
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
    poseidon::hasher::{PoseidonSponge, PoseidonHasher, spec::OptimizedPoseidonSpec, PoseidonHash},
};
use halo2_ecc::{fields::{fp::FpChip, native_fp::NativeFieldChip}, ecc::EccChip};
use halo2_base::halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value, SimpleFloorPlanner},
    plonk::{Circuit, Selector, ConstraintSystem, Error},
};//halo2_base::
//use halo2_ecc::bn254::pairing;
use std::{fmt::Debug, hash::Hash, marker::PhantomData, convert::From};
use std::{mem, rc::Rc};

use self::strawman::{NUM_LIMB_BITS, NUM_LIMBS, T, RATE, R_F, R_P, SECURE_MDS, Chip};


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
    type Params = ();

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

impl<'a, C: TwoChainCurve> StepCircuit<'a, C> for TrivialCircuit<C>
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    //type TccChip = strawman::Chip<'a, C>;
    //type HashChip = strawman::Chip<'a, C>;
    //type TranscriptChip = strawman::PoseidonTranscriptChip<'a, C>;

    fn configs(
        config: Self::Config,
    ) -> (
            OptimizedPoseidonSpec<C::Scalar, T, RATE>,
            OptimizedPoseidonSpec<C::Scalar, T, RATE>,
        ) {
        (
            //config.clone(),
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

    //todo fix this with other synthesizes
    fn synthesize(
        &self,
        _: Self::Config,
        _: impl Layouter<C::Scalar>,
    ) -> Result<
        (
            Vec<AssignedValue<C::Scalar>>,
            Vec<AssignedValue<C::Scalar>>,
        ),
        Error,
    > {
        Ok((Vec::new(), Vec::new()))
    }
}

// #[derive(Clone)]
// struct SecondaryAggregationCircuit {
//     vp_digest: grumpkin::Fr,
//     vp: ProtostarVerifierParam<bn256::Fr, HyperPlonk<Gemini<UnivariateKzg<Bn256>>>>,
//     arity: usize,
//     instances: Vec<grumpkin::Fr>,
//     num_steps: Value<usize>,
//     initial_input: Value<Vec<grumpkin::Fr>>,
//     output: Value<Vec<grumpkin::Fr>>,
//     acc: Value<ProtostarAccumulatorInstance<bn256::Fr, bn256::G1Affine>>,
//     proof: Value<Vec<u8>>,
// }

// impl Circuit<grumpkin::Fr> for SecondaryAggregationCircuit {
//     type Config = strawman::Config<grumpkin::Fr>;
//     type FloorPlanner = SimpleFloorPlanner;

//     fn without_witnesses(&self) -> Self {
//         self.clone()
//     }

//     fn configure(meta: &mut ConstraintSystem<grumpkin::Fr>) -> Self::Config {
//         strawman::Config::configure::<grumpkin::G1Affine>(meta)
//     }

//     //todo fix this with other synthesizes
//     fn synthesize(
//         &self,
//         config: Self::Config,
//         mut layouter: impl Layouter<grumpkin::Fr>,
//     ) -> Result<(), Error> {

//         let mut builder = RangeCircuitBuilder::from_stage(CircuitBuilderStage::Keygen)
//         .use_k(8)
//         .use_lookup_bits(9);

//         let mut pool = mem::take(builder.pool(0));

//         let range = builder.range_chip();
//         let gate_chip = GateChip::<grumpkin::Fr>::new();
//         let base_chip = FpChip::<grumpkin::Fr, grumpkin::Fq>::new(&range, NUM_LIMB_BITS, NUM_LIMBS);
//         let native_chip = NativeFieldChip::new(&range);
//         let ecc_chip = EccChip::new(&native_chip);
//         let chip = strawman::Chip::<grumpkin::G1Affine>::create(gate_chip, &base_chip, &ecc_chip);

//         // let chip = <strawman::Chip<grumpkin::G1Affine> as TwoChainCurveInstruction<
//         //     grumpkin::G1Affine,
//         // >>::new(chip, config);

//         let aggregator = ProtostarIvcAggregator::new(
//             self.vp_digest,
//             self.vp.clone(),
//             self.arity,
//             chip.clone(),
//             chip.clone(),
//         );

//         let mut transcript = strawman::PoseidonTranscriptChip::new(
//             builder.main(0),
//             strawman::decider_transcript_param(),
//             chip.clone(),
//             self.proof.clone(),
//         );

//         let (num_steps, initial_input, output, h, lhs, rhs) = aggregator.aggregate_gemini_kzg_ivc(
//             &mut pool,
//             self.num_steps,
//             self.initial_input.clone(),
//             self.output.clone(),
//             self.acc.clone(),
//             &mut transcript,
//         )?;

//         // let zero = chip.assign_constant(&mut pool, grumpkin::Fr::ZERO)?;
//         // let coords = lhs.coordinates().unwrap();
//         // let lhs_is_identity = (lhs.x().is_zero() & lhs.y().is_zero()).into();
//         // chip.constrain_equal(&mut pool, lhs.is_identity(), &zero)?;
//         // chip.constrain_equal(&mut pool, rhs.is_identity(), &zero)?;

//         // let cell_map = chip.layout_and_clear(&mut layouter)?;
//         // for (idx, witness) in chain![
//         //     [num_steps],
//         //     initial_input,
//         //     output,
//         //     [h, *lhs.x(), *lhs.y(), *rhs.x(), *rhs.y()]
//         // ]
//         // .enumerate()
//         // {
//         //     layouter.constrain_instance(cell_map[&witness.id()].cell(), chip.instance, idx)?;
//         // }

//         Ok(())
//     }
// }

// impl CircuitExt<grumpkin::Fr> for SecondaryAggregationCircuit {
//     fn instances(&self) -> Vec<Vec<grumpkin::Fr>> {
//         vec![self.instances.clone()]
//     }
// }

// #[derive(Clone)]
// struct PrimaryAggregationCircuit {
//     vp_digest: bn256::Fr,
//     vp: ProtostarVerifierParam<grumpkin::Fr, HyperPlonk<MultilinearIpa<grumpkin::G1Affine>>>,
//     primary_arity: usize,
//     secondary_arity: usize,
//     instances: Vec<bn256::Fr>,
//     num_steps: Value<usize>,
//     initial_input: Value<Vec<bn256::Fr>>,
//     output: Value<Vec<bn256::Fr>>,
//     acc_before_last: Value<ProtostarAccumulatorInstance<grumpkin::Fr, grumpkin::G1Affine>>,
//     last_instance: Value<[grumpkin::Fr; 2]>,
//     proof: Value<Vec<u8>>,
//     secondary_aggregation_vp: HyperPlonkVerifierParam<grumpkin::Fr, MultilinearHyrax<grumpkin::G1Affine>>,
//     secondary_aggregation_instances: Value<Vec<grumpkin::Fr>>,
//     secondary_aggregation_proof: Value<Vec<u8>>,
// }

// impl Circuit<bn256::Fr> for PrimaryAggregationCircuit {
//     type Config = strawman::Config<bn256::Fr>;
//     type FloorPlanner = SimpleFloorPlanner;

//     fn without_witnesses(&self) -> Self {
//         self.clone()
//     }

//     fn configure(meta: &mut ConstraintSystem<bn256::Fr>) -> Self::Config {
//         strawman::Config::configure::<bn256::G1Affine>(meta)
//     }
    
//     //todo fix this with other synthesizes
//     fn synthesize(
//         &self,
//         config: Self::Config,
//         mut layouter: impl Layouter<bn256::Fr>,
//     ) -> Result<(), Error> {

//         let mut builder = RangeCircuitBuilder::from_stage(CircuitBuilderStage::Keygen)
//         .use_k(8)
//         .use_lookup_bits(9);

//         let range = builder.range_chip();
//         let gate_chip = GateChip::<bn256::Fr>::new();
//         let base_chip = FpChip::<bn256::Fr, bn256::Fq>::new(&range, NUM_LIMB_BITS, NUM_LIMBS);
//         let native_chip = NativeFieldChip::new(&range);
//         let ecc_chip = EccChip::new(&native_chip);

//         let mut pool = mem::take(builder.pool(0));
//         let chip = strawman::Chip::<bn256::G1Affine>::create(gate_chip, &base_chip, &ecc_chip);

//         // let chip =
//         //     <strawman::Chip<bn256::G1Affine> as TwoChainCurveInstruction<bn256::G1Affine>>::new(chip,
//         //         config,
//         //     );

//         let mut builder = RangeCircuitBuilder::from_stage(CircuitBuilderStage::Keygen)
//             .use_k(8)
//             .use_lookup_bits(9);

//         let mut pool = mem::take(builder.pool(0));


//         let aggregator = ProtostarIvcAggregator::new(
//             self.vp_digest,
//             self.vp.clone(),
//             self.primary_arity,
//             chip.clone(),
//             chip.clone(),
//         );

//         let mut transcript = strawman::PoseidonTranscriptChip::new(
//             builder.main(0),
//             strawman::decider_transcript_param(),
//             chip.clone(),
//             self.proof.clone(),
//         );

//         let (primary_num_steps, primary_initial_input, primary_output, h_ohs_from_last_nark) =
//             aggregator.verify_ipa_grumpkin_ivc_with_last_nark(
//                 &mut pool,
//                 self.num_steps,
//                 self.initial_input.clone(),
//                 self.output.clone(),
//                 self.acc_before_last.clone(),
//                 self.last_instance,
//                 &mut transcript,
//             )?;

//         let (secondary_initial_input, secondary_output, pairing_acc) = {
//             let mut transcript = strawman::PoseidonTranscriptChip::new(
//                 builder.main(0),
//                 strawman::decider_transcript_param(),
//                 chip.clone(),
//                 self.secondary_aggregation_proof.clone(),
//             );
//             let secondary_aggregation_instance = chip.verify_hyrax_hyperplonk(
//                 &mut pool,
//                 &self.secondary_aggregation_vp,
//                 self.secondary_aggregation_instances
//                     .as_ref()
//                     .map(Vec::as_slice),
//                 &mut transcript,
//             )?;

//             let secondary_num_steps =
//                 chip.fit_base_in_scalar(&secondary_aggregation_instance[0])?;
//             chip.constrain_equal(&mut pool, &primary_num_steps, &secondary_num_steps)?;

//             let h = chip.fit_base_in_scalar(
//                 &secondary_aggregation_instance[1 + 2 * self.secondary_arity],
//             )?;
//             chip.constrain_equal(&mut pool, &h_ohs_from_last_nark, &h)?;

//             let iter = &mut secondary_aggregation_instance.iter();
//             let mut instances = |skip: usize, take: usize| {
//                 iter.skip(skip)
//                     .take(take)
//                     .map(|base| chip.to_repr_base(base))
//                     .try_collect::<_, Vec<_>, _>()
//             };
//             (
//                 instances(1, self.secondary_arity)?,
//                 instances(0, self.secondary_arity)?,
//                 instances(1, 4 * strawman::NUM_LIMBS)?,
//             )
//         };

//         // let cell_map = chip.layout_and_clear(&mut layouter)?;
//         // for (idx, witness) in chain![
//         //     [primary_num_steps],
//         //     primary_initial_input,
//         //     primary_output,
//         //     secondary_initial_input.into_iter().flatten(),
//         //     secondary_output.into_iter().flatten(),
//         //     pairing_acc.into_iter().flatten(),
//         // ]
//         // .enumerate()
//         // {
//         //     layouter.constrain_instance(cell_map[&witness.id()].cell(), chip.instance, idx)?;
//         // }

//         Ok(())
//     }
// }

// impl CircuitExt<bn256::Fr> for PrimaryAggregationCircuit {
//     fn instances(&self) -> Vec<Vec<bn256::Fr>> {
//         vec![self.instances.clone()]
//     }
// }

#[allow(clippy::type_complexity)]
fn run_protostar_hyperplonk_ivc<C, P1, P2>(
    num_vars: usize,
    num_steps: usize,
    chip_primary: Chip<C>,
    chip_secondary: Chip<<C as TwoChainCurve>::Secondary>,
) -> (
    ProtostarIvcVerifierParam<
        C,
        P1,
        P2,
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
        chip_primary,
        chip_secondary,
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
        verify_decider::<_, _, _>(
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

    let mut builder_primary = RangeCircuitBuilder::<bn256::Fr>::from_stage(CircuitBuilderStage::Keygen)
    .use_k(10)
    .use_lookup_bits(8);

    let range_primary = builder_primary.range_chip();
    let gate_chip_primary = GateChip::<bn256::Fr>::new();
    let base_chip_primary = FpChip::<bn256::Fr, bn256::Fq>::new(&range_primary, NUM_LIMB_BITS, NUM_LIMBS);
    let native_chip_primary = NativeFieldChip::new(&range_primary);
    let ecc_chip_primary = EccChip::new(&native_chip_primary);
    let chip_primary = strawman::Chip::<bn256::G1Affine>::create(gate_chip_primary, &base_chip_primary, &ecc_chip_primary);

    let mut builder_secondary = RangeCircuitBuilder::<grumpkin::Fr>::from_stage(CircuitBuilderStage::Keygen)
    .use_k(10)
    .use_lookup_bits(8);

    let range_secondary = builder_secondary.range_chip();
    let gate_chip_secondary = GateChip::<grumpkin::Fr>::new();
    let base_chip_secondary = FpChip::<grumpkin::Fr, grumpkin::Fq>::new(&range_secondary, NUM_LIMB_BITS, NUM_LIMBS);
    let native_chip_secondary = NativeFieldChip::new(&range_secondary);
    let ecc_chip_secondary = EccChip::new(&native_chip_secondary);
    let chip_secondary = strawman::Chip::<grumpkin::G1Affine>::create(gate_chip_secondary, &base_chip_secondary, &ecc_chip_secondary);

    run_protostar_hyperplonk_ivc::<
        bn256::G1Affine,
        Gemini<UnivariateKzg<Bn256>>,
        MultilinearIpa<grumpkin::G1Affine>,
    >(NUM_VARS, NUM_STEPS,chip_primary, chip_secondary);
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

// #[test]
// fn gemini_kzg_ipa_protostar_hyperplonk_ivc_with_aggregation() {
//     const NUM_VARS: usize = 14;
//     const NUM_STEPS: usize = 3;
//     let (
//         ivc_vp,
//         num_steps,
//         primary_initial_input,
//         primary_output,
//         primary_acc,
//         primary_proof,
//         secondary_initial_input,
//         secondary_output,
//         secondary_acc_before_last,
//         secondary_last_instances,
//         secondary_proof,
//     ) = run_protostar_hyperplonk_ivc::<
//         bn256::G1Affine,
//         Gemini<UnivariateKzg<Bn256>>,
//         MultilinearIpa<grumpkin::G1Affine>,
//     >(NUM_VARS, NUM_STEPS);

//     let (secondary_aggregation_vp, secondary_aggregation_instances, secondary_aggregation_proof) = {
//         let mut circuit = SecondaryAggregationCircuit {
//             vp_digest: fe_to_fe(ivc_vp.vp_digest),
//             vp: ivc_vp.primary_vp.clone(),
//             arity: ivc_vp.secondary_arity,
//             instances: Vec::new(),
//             num_steps: Value::known(num_steps),
//             initial_input: Value::known(secondary_initial_input),
//             output: Value::known(secondary_output),
//             acc: Value::known(primary_acc.unwrap_comm()),
//             proof: Value::known(primary_proof),
//         };
//         circuit.instances = InstanceExtractor::extract(&circuit)
//             .unwrap()
//             .into_iter()
//             .next()
//             .unwrap();
//         assert_eq!(
//             circuit.instances[1 + 2 * ivc_vp.secondary_arity],
//             secondary_last_instances[1]
//         );

//         type HyraxHyperPlonk = HyperPlonk<MultilinearHyrax<grumpkin::G1Affine>>;
//         let circuit = Halo2Circuit::new::<HyraxHyperPlonk>(17, circuit);
//         let circuit_info = circuit.circuit_info().unwrap();

//         let param = HyraxHyperPlonk::setup(&circuit_info, seeded_std_rng()).unwrap();
//         let (pp, vp) = HyraxHyperPlonk::preprocess(&param, &circuit_info).unwrap();
//         let dtp = strawman::decider_transcript_param();
//         let proof = {
//             let mut transcript = strawman::PoseidonTranscript::new(dtp.clone());
//             HyraxHyperPlonk::prove(&pp, &circuit, &mut transcript, seeded_std_rng()).unwrap();
//             transcript.into_proof()
//         };
//         let result = {
//             let mut transcript = strawman::PoseidonTranscript::from_proof(dtp, proof.as_slice());
//             HyraxHyperPlonk::verify(&vp, circuit.instances(), &mut transcript, seeded_std_rng())
//         };
//         assert_eq!(result, Ok(()));

//         (vp, circuit.instances().to_vec(), proof)
//     };

//     {
//         let mut circuit = PrimaryAggregationCircuit {
//             vp_digest: fe_to_fe(ivc_vp.vp_digest),
//             vp: ivc_vp.secondary_vp.clone(),
//             primary_arity: ivc_vp.primary_arity,
//             secondary_arity: ivc_vp.secondary_arity,
//             instances: Vec::new(),
//             num_steps: Value::known(num_steps),
//             initial_input: Value::known(primary_initial_input),
//             output: Value::known(primary_output),
//             acc_before_last: Value::known(secondary_acc_before_last.unwrap_comm()),
//             last_instance: Value::known([secondary_last_instances[0], secondary_last_instances[1]]),
//             proof: Value::known(secondary_proof),
//             secondary_aggregation_vp,
//             secondary_aggregation_instances: Value::known(
//             secondary_aggregation_instances[0].clone(),
//             ),
//             secondary_aggregation_proof: Value::known(secondary_aggregation_proof),
//         };
//         circuit.instances = InstanceExtractor::extract(&circuit)
//             .unwrap()
//             .into_iter()
//             .next()
//             .unwrap();

//         type GeminiHyperPlonk = HyperPlonk<Gemini<UnivariateKzg<Bn256>>>;
//         let circuit = Halo2Circuit::new::<GeminiHyperPlonk>(21, circuit);
//         let circuit_info = circuit.circuit_info().unwrap();

//         let param = GeminiHyperPlonk::setup(&circuit_info, seeded_std_rng()).unwrap();
//         let (pp, vp) = GeminiHyperPlonk::preprocess(&param, &circuit_info).unwrap();
//         let dtp = strawman::decider_transcript_param();
//         let proof = {
//             let mut transcript = strawman::PoseidonTranscript::new(dtp.clone());
//             GeminiHyperPlonk::prove(&pp, &circuit, &mut transcript, seeded_std_rng()).unwrap();
//             transcript.into_proof()
//         };
//         let result = {
//             let mut transcript = strawman::PoseidonTranscript::from_proof(dtp, proof.as_slice());
//             GeminiHyperPlonk::verify(&vp, circuit.instances(), &mut transcript, seeded_std_rng())
//         };
//         assert_eq!(result, Ok(()));

//         let pairing_acc =
//             &circuit.instances()[0][circuit.instances()[0].len() - 4 * strawman::NUM_LIMBS..];
//         let [lhs_x, lhs_y, rhs_x, rhs_y] = [0, 1, 2, 3].map(|idx| {
//             let offset = idx * strawman::NUM_LIMBS;
//             strawman::fe_from_limbs(
//                 &pairing_acc[offset..offset + strawman::NUM_LIMBS],
//                 strawman::NUM_LIMB_BITS,
//             )
//         });
//         let lhs = bn256::G1Affine::from_xy(lhs_x, lhs_y).unwrap();
//         let rhs = bn256::G1Affine::from_xy(rhs_x, rhs_y).unwrap();
//         // assert!(Bn256::pairings_product_is_identity(&[
//         //     (&lhs, &(-ivc_vp.primary_vp.vp.pcs.g2()).into()),
//         //     (&rhs, &ivc_vp.primary_vp.vp.pcs.s_g2().into()),
//         // ]));
//     }
// }

pub mod strawman {
    use crate::{
        accumulation::protostar::{
            ProtostarStrategy::{Compressing, NoCompressing},
            ivc::{ProtostarAccumulationVerifierParam, halo2::AssignedProtostarAccumulatorInstance},
            ProtostarAccumulatorInstance,
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

    use halo2_base::{
        Context,
        utils::{BigPrimeField, ScalarField, CurveAffineExt, decompose},
        QuantumCell::{Constant, Existing, Witness, WitnessFraction},
        halo2_proofs::plonk::Assigned,
        AssignedValue,
        gates::{
            circuit::builder::BaseCircuitBuilder,
            RangeChip,range::RangeConfig,
            flex_gate::{GateChip, GateInstructions, FlexGateConfig, FlexGateConfigParams},
        },
        gates::flex_gate::threads::SinglePhaseCoreManager, poseidon::hasher::{PoseidonSponge, PoseidonHasher, spec::OptimizedPoseidonSpec, PoseidonHash},
    };
    
    use halo2_base::halo2_proofs::{
        circuit::{AssignedCell, Layouter, Value},
        plonk::{Column, ConstraintSystem, Error, Instance},
    };
    
    use halo2_ecc::{
        fields::{fp::FpChip, FieldChip, native_fp::NativeFieldChip, Selectable},
        bigint::{CRTInteger, FixedCRTInteger, ProperCrtUint},
        ecc::{fixed_base, scalar_multiply, EcPoint, EccChip, BaseFieldEccChip},
    };
    
    //use super::range::RangeConfig;

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
    pub const NUM_SUBLIMBS: usize = 5;
    pub const NUM_LOOKUPS: usize = 1;
    pub const LOOKUP_BITS: usize = 8;

    pub const T: usize = 5;
    pub const RATE: usize = 4;
    pub const R_F: usize = 8;
    pub const R_P: usize = 60;
    pub const SECURE_MDS: usize = 0;

    pub const NUM_CHALLENGE_BITS: usize = 128;
    pub const NUM_CHALLENGE_BYTES: usize = NUM_CHALLENGE_BITS / 8;
    pub const NUM_HASH_BITS: usize = 250;

    // fn fe_to_limbs<F1: ScalarField, F2: ScalarField>(fe: F1, num_limb_bits: usize) -> Vec<F2> {
    //     fe.to_bytes_le()
    //         .chunks(num_limb_bits)
    //         .into_iter()
    //         .map(|bits| match bits.len() {
    //             1..=64 => F2::from(bits.load_le()),
    //             65..=128 => {
    //                 let lo = bits[..64].load_le::<u64>();
    //                 let hi = bits[64..].load_le::<u64>();
    //                 F2::from(hi) * F2::from(2).pow_vartime([64]) + F2::from(lo)
    //             }
    //             _ => unimplemented!(),
    //         })
    //         .take(NUM_LIMBS)
    //         .collect()
    // }

    pub fn fe_from_limbs<F1: ScalarField, F2: ScalarField>(
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

    pub fn accumulation_transcript_param<F: ScalarField>() -> OptimizedPoseidonSpec<F, T, RATE> {
        OptimizedPoseidonSpec::new::<R_F, R_P,SECURE_MDS>()
    }

    pub fn decider_transcript_param<F: ScalarField>() -> OptimizedPoseidonSpec<F, T, RATE> {
        OptimizedPoseidonSpec::new::<R_F, R_P,SECURE_MDS>()
    }

    pub struct PoseidonTranscript<F: ScalarField, S> {
        state: PoseidonHash<F, T, RATE>,
        stream: S,
    }

    impl<F: ScalarField> InMemoryTranscript for PoseidonTranscript<F, Cursor<Vec<u8>>> {
        type Param = OptimizedPoseidonSpec<F, T, RATE>;

        fn new(spec: Self::Param) -> Self {
            Self {
                state: PoseidonHash::from_spec(spec),
                stream: Default::default(),
            }
        }

        fn into_proof(self) -> Vec<u8> {
            self.stream.into_inner()
        }

        fn from_proof(spec: Self::Param, proof: &[u8]) -> Self {
            Self {
                state: PoseidonHash::from_spec(spec),
                stream: Cursor::new(proof.to_vec()),
            }
        }
    }

    impl<F: ScalarField, N: ScalarField, S> FieldTranscript<F>
        for PoseidonTranscript<N, S>
    {
        fn squeeze_challenge(&mut self) -> F {
            let hash = self.state.squeeze();
            self.state.update(&[hash]);
            fe_from_le_bytes(&hash.to_repr().as_ref()[..NUM_CHALLENGE_BYTES])
        }

        //TODO FIX THIS
        fn common_field_element(&mut self, fe: &F) -> Result<(), crate::Error> {
            self.state.update(vec![N::ONE, N::ZERO].as_slice());//&fe_to_limbs(*fe, NUM_LIMB_BITS));

            Ok(())
        }
    }

    impl<F: ScalarField, N: ScalarField, R: io::Read> FieldTranscriptRead<F>
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

    impl<F: ScalarField, N: ScalarField, W: io::Write> FieldTranscriptWrite<F>
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
        C::Base: ScalarField,
        C::Scalar: ScalarField,
    {
        fn common_commitment(&mut self, ec_point: &C) -> Result<(), crate::Error> {
            self.state.update(&x_y_is_identity(ec_point));
            Ok(())
        }
    }

    impl<C: CurveAffine, R: io::Read> TranscriptRead<C, C::Scalar> for PoseidonTranscript<C::Base, R>
    where
        C::Base: ScalarField,
        C::Scalar: ScalarField,
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
        C::Base: ScalarField,
        C::Scalar: ScalarField,
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
        // pub range_config: RangeConfig<F>,
        pub flex_config: FlexGateConfig<F>,
        pub instance: Column<Instance>,
        pub poseidon_spec: OptimizedPoseidonSpec<F, T, RATE>,
    }

    impl<F: FromUniformBytes<64> + Ord + From<bool> + Hash> Config<F> {
        pub fn configure<C: CurveAffine<ScalarExt = F>>(meta: &mut ConstraintSystem<F>) -> Self {
            let params = FlexGateConfigParams {
                k: 10,
                num_advice_per_phase: vec![1],
                num_fixed: 1,
            };
            let flex_config = FlexGateConfig::configure(
                meta,
                params,
            );
            // let range_config = RangeConfig::configure(
            //     meta,
            //     params,
            //     &[NUM_LOOKUPS],
            //     LOOKUP_BITS,
            // );
            let instance = meta.instance_column();
            meta.enable_equality(instance);
            let poseidon_spec = OptimizedPoseidonSpec::new::<R_F, R_P, SECURE_MDS>();
            Self {
                //range_config,
                flex_config,
                instance,
                poseidon_spec,
            }
        }
    }

    #[allow(clippy::type_complexity)]
    #[derive(Clone, Debug)]
    pub struct Chip<'a, C: TwoChainCurve> 
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,
    {   
        pub gate_chip: GateChip<C::Scalar>,
        pub base_chip: &'a FpChip<'a, C::Scalar, C::Base>,
        pub ecc_chip: &'a EccChip<'a, C::Scalar, NativeFieldChip<'a, C::Scalar>>,
        //pub instance: Column<Instance>,
        _marker: PhantomData<C>,
    }

    impl<'a, C: TwoChainCurve> Chip<'a, C> 
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,  
    {

        pub fn create(gate_chip: GateChip<C::Scalar>, 
            base_chip: &'a FpChip<'a, C::Scalar, C::Base>, 
            ecc_chip: &'a EccChip<'a, C::Scalar, NativeFieldChip<'a, C::Scalar>>,
            ) -> Self {
                Self {
                    gate_chip,
                    base_chip,
                    ecc_chip,
                    //instance: config.instance, config: Config
                    _marker: PhantomData,
                }
            }

        pub fn constrain_equal(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &AssignedValue<C::Scalar>,
            rhs: &AssignedValue<C::Scalar>,
        ) -> Result<(), Error> {
            Ok(builder.main().constrain_equal(lhs, rhs))
        }
    
        pub fn assign_constant(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            constant: C::Scalar,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            Ok(builder.main().load_constant(constant))
        }
    
        pub fn assign_witness(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: C::Scalar,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            Ok(builder.main().load_witness(witness))
        }

        pub fn assign_privates(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: &[C::Scalar],
        ) -> Result<Vec<AssignedValue<C::Scalar>>, Error> {
            Ok(builder.main().assign_witnesses(witness.iter().cloned()))
        }
    
        pub fn select_gatechip(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            condition: &AssignedValue<C::Scalar>,
            when_true: &AssignedValue<C::Scalar>,
            when_false: &AssignedValue<C::Scalar>,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            Ok(GateInstructions::select(&self.gate_chip, builder.main(), Existing(when_true.into()), Existing(when_false.into()), Existing(condition.into())))
        }
    
        pub fn is_equal(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &AssignedValue<C::Scalar>,
            rhs: &AssignedValue<C::Scalar>,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            Ok(self.gate_chip.is_equal(builder.main(), Existing(lhs.into()), Existing(rhs.into())))
        }
    
        pub fn add(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &AssignedValue<C::Scalar>,
            rhs: &AssignedValue<C::Scalar>,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            Ok(self.gate_chip.add(builder.main(), Existing(lhs.into()), Existing(rhs.into())))
        }
    
        pub fn sub(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &AssignedValue<C::Scalar>,
            rhs: &AssignedValue<C::Scalar>,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            Ok(self.gate_chip.sub(builder.main(), Existing(lhs.into()), Existing(rhs.into())))
        }  
    
        pub fn mul(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &AssignedValue<C::Scalar>,
            rhs: &AssignedValue<C::Scalar>,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            Ok(self.gate_chip.mul(builder.main(), Existing(lhs.into()), Existing(rhs.into())))
        }

        pub fn constrain_equal_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &ProperCrtUint<C::Scalar>,
            rhs: &ProperCrtUint<C::Scalar>,
        ) -> Result<(), Error> {
            self.base_chip.assert_equal(builder.main(),lhs,rhs);
            Ok(())
        }
    
        pub fn assign_constant_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            constant: C::Base,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            Ok(self.base_chip.load_constant(builder.main(),constant))
        }
    
        pub fn assign_witness_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: C::Base,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            Ok(self.base_chip.load_private(builder.main(),witness))
        }    
    
        pub fn select_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            condition: &AssignedValue<C::Scalar>,
            when_true: &ProperCrtUint<C::Scalar>,
            when_false: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            Ok(self.base_chip.select(builder.main(),when_true.clone(),when_false.clone(),*condition))
        }
    
        pub fn fit_base_in_scalar(
            &self,
            value: &ProperCrtUint<C::Scalar>,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            Ok(value.native().clone())
        }
    
        pub fn to_repr_base(
            &self,
            value: &ProperCrtUint<C::Scalar>,
        ) -> Result<Vec<AssignedValue<C::Scalar>>, Error> {
            Ok(value.limbs().to_vec())
        }
    
        pub fn add_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            a: &ProperCrtUint<C::Scalar>,
            b: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            let add = self.base_chip.add_no_carry(builder.main(), a, b);
                Ok(FixedCRTInteger::from_native(add.value.to_biguint().unwrap(), 
                    self.base_chip.num_limbs, self.base_chip.limb_bits).assign(
                    builder.main(),
                    self.base_chip.limb_bits,
                    self.base_chip.native_modulus(),
                ))
        }
    
        pub fn sub_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            a: &ProperCrtUint<C::Scalar>,
            b: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            let sub = self.base_chip.sub_no_carry(builder.main(), a, b);
                Ok(FixedCRTInteger::from_native(sub.value.to_biguint().unwrap(), 
                    self.base_chip.num_limbs, self.base_chip.limb_bits).assign(
                    builder.main(),
                    self.base_chip.limb_bits,
                    self.base_chip.native_modulus(),
                ))
        }

        pub fn neg_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            value: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            let zero = self.assign_constant_base(builder, C::Base::ZERO)?;
            self.sub_base(builder, &zero, value)
        }

        pub fn sum_base<'b>(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            values: impl IntoIterator<Item = &'b ProperCrtUint<C::Scalar>>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error>
        where
            ProperCrtUint<C::Scalar>: 'b,
        {
            values.into_iter().fold(
                self.assign_constant_base(builder, C::Base::ZERO),
                |acc, value| self.add_base(builder, &acc?, value),
            )
        }

        pub fn product_base<'b>(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            values: impl IntoIterator<Item = &'b ProperCrtUint<C::Scalar>>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error>
        where
            ProperCrtUint<C::Scalar>: 'b,
        {
            values.into_iter().fold(
                self.assign_constant_base(builder, C::Base::ONE),
                |acc, value| self.mul_base(builder, &acc?, value),
            )
        }
    
        pub fn mul_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &ProperCrtUint<C::Scalar>,
            rhs: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            Ok(self.base_chip.mul(builder.main(), lhs, rhs))
        }
    
        pub fn div_incomplete_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &ProperCrtUint<C::Scalar>,
            rhs: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            Ok(self.base_chip.divide_unsafe(builder.main(), lhs, rhs))
        }

        pub fn invert_incomplete_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            value: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            let one = self.assign_constant_base(builder, C::Base::ONE)?;
            self.div_incomplete_base(builder, &one, value)
        }

        pub fn powers_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            base: &ProperCrtUint<C::Scalar>,
            n: usize,
        ) -> Result<Vec<ProperCrtUint<C::Scalar>>, Error> {
            Ok(match n {
                0 => Vec::new(),
                1 => vec![self.assign_constant_base(builder, C::Base::ONE)?],
                2 => vec![
                    self.assign_constant_base(builder, C::Base::ONE)?,
                    base.clone(),
                ],
                _ => {
                    let mut powers = Vec::with_capacity(n);
                    powers.push(self.assign_constant_base(builder, C::Base::ONE)?);
                    powers.push(base.clone());
                    for _ in 0..n - 2 {
                        powers.push(self.mul_base(builder, powers.last().unwrap(), base)?);
                    }
                    powers
                }
            })
        }

        pub fn squares_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            base: &ProperCrtUint<C::Scalar>,
            n: usize,
        ) -> Result<Vec<ProperCrtUint<C::Scalar>>, Error> {
            Ok(match n {
                0 => Vec::new(),
                1 => vec![base.clone()],
                _ => {
                    let mut squares = Vec::with_capacity(n);
                    squares.push(base.clone());
                    for _ in 0..n - 1 {
                        squares.push(self.mul_base(
                            builder,
                            squares.last().unwrap(),
                            squares.last().unwrap(),
                        )?);
                    }
                    squares
                }
            })
        }

        pub fn inner_product_base<'c, 'b>(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: impl IntoIterator<Item = &'c ProperCrtUint<C::Scalar>>,
            rhs: impl IntoIterator<Item = &'b ProperCrtUint<C::Scalar>>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error>
        where
            ProperCrtUint<C::Scalar>: 'c + 'b,
        {
            let products = izip_eq!(lhs, rhs)
                .map(|(lhs, rhs)| self.mul_base(builder, lhs, rhs))
                .collect_vec();
            products
                .into_iter()
                .reduce(|acc, output| self.add_base(builder, &acc?, &output?))
                .unwrap()
        }

        pub fn constrain_equal_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            rhs: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        ) -> Result<(), Error> {
            self.ecc_chip.assert_equal(builder.main(), lhs.clone(), rhs.clone());
            Ok(())
        }

        pub fn assign_constant_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            constant: C::Secondary,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            Ok(self.ecc_chip.assign_constant_point(builder.main(), constant))
        }

        pub fn assign_witness_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: C::Secondary,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            Ok(self.ecc_chip.assign_point(builder.main(), witness))
        }

        pub fn select_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            condition: &AssignedValue<C::Scalar>,
            when_true: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            when_false: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            Ok(self.ecc_chip.select(builder.main(), when_true.clone(), when_false.clone(), *condition))
        }

        pub fn add_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            rhs: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            Ok(self.ecc_chip.add_unequal(builder.main(), lhs, rhs, false))
        }

        // todo SET MAX_BITS, WINDOW_BITS
        pub fn scalar_mul_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            base: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            le_bits: &[AssignedValue<C::Scalar>],
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            Ok(self.ecc_chip.scalar_mult::<C::Secondary>(builder.main(), base.clone(), le_bits.to_vec(), 8,8))
        }

        // todo change the inputs where this is used
        pub fn fixed_base_msm_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            bases: &[C::Secondary],
            scalars: Vec<ProperCrtUint<C::Scalar>>,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error>{
            let scalar_limbs_vec = scalars.iter().map(|scalar| scalar.limbs().to_vec()).collect();
            let max_scalar_bits_per_cell = self.base_chip.limb_bits;
            Ok(self.ecc_chip.fixed_base_msm::<C::Secondary>(builder, bases, scalar_limbs_vec, max_scalar_bits_per_cell))
        }

        pub fn variable_base_msm_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            bases: &[EcPoint<C::Scalar, AssignedValue<C::Scalar>>],
            scalars: Vec<ProperCrtUint<C::Scalar>>,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error>{
            let scalar_limbs_vec = scalars.iter().map(|scalar| scalar.limbs().to_vec()).collect();
            let max_bits = self.base_chip.limb_bits;
            Ok(self.ecc_chip.variable_base_msm::<C::Secondary>(builder, bases, scalar_limbs_vec, max_bits))
        }

    }

    impl<'a, C: TwoChainCurve> Chip<'a, C>
    where
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {
        pub const NUM_HASH_BITS: usize = NUM_HASH_BITS;

        // type Param = OptimizedPoseidonSpec<C::Scalar, T, RATE>;
        // type Config = OptimizedPoseidonSpec<C::Scalar, T, RATE>;
        // type TccChip = Chip<'a, C>;

        pub fn new(_: OptimizedPoseidonSpec<C::Scalar, T, RATE>, chip: Chip<'a, C>) -> Self {
            chip
        }

        pub fn hash_state<Comm: AsRef<C::Secondary>>(
            spec: &OptimizedPoseidonSpec<C::Scalar, T, RATE>,
            vp_digest: C::Scalar,
            step_idx: usize,
            initial_input: &[C::Scalar],
            output: &[C::Scalar],
            acc: &ProtostarAccumulatorInstance<C::Base, Comm>,
        ) -> C::Scalar {
            let mut poseidon = PoseidonHash::from_spec(spec.clone());
            //let fe_to_limbs = |fe| decompose(fe, NUM_LIMB_BITS, NUM_LIMBS);
            let inputs = iter::empty()
                .chain([vp_digest, C::Scalar::from(step_idx as u64)])
                .chain(initial_input.iter().copied())
                .chain(output.iter().copied())
                //.chain(fe_to_limbs(acc.instances[0][0]))
                //.chain(fe_to_limbs(acc.instances[0][1]))
                .chain(
                    acc.witness_comms
                        .iter()
                        .map(AsRef::as_ref)
                        .flat_map(x_y_is_identity),
                )
                //.chain(acc.challenges.iter().copied().flat_map(fe_to_limbs))
                //.chain(fe_to_limbs(acc.u))
                .chain(x_y_is_identity(acc.e_comm.as_ref()))
                //.chain(acc.compressed_e_sum.map(fe_to_limbs).into_iter().flatten())
                .collect_vec();
            poseidon.update(inputs.as_slice());
            fe_truncated(poseidon.squeeze(), NUM_HASH_BITS)
        }

        pub fn hash_assigned_state(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            vp_digest: &AssignedValue<C::Scalar>,
            step_idx: &AssignedValue<C::Scalar>,
            initial_input: &[AssignedValue<C::Scalar>],
            output: &[AssignedValue<C::Scalar>],
            acc: &AssignedProtostarAccumulatorInstance<
                ProperCrtUint<C::Scalar>,
                EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            >,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            let inputs = iter::empty()
                .chain([vp_digest, step_idx])
                .chain(initial_input)
                .chain(output)
                .chain(acc.instances[0][0].limbs())
                .chain(acc.instances[0][1].limbs())
                //TODO FIX THIS
                // .chain(
                //     acc.witness_comms
                //         .iter()
                //         .flat_map(AssignedEcPoint::assigned_cells),
                // )
                .chain(acc.challenges.iter().flat_map(ProperCrtUint::limbs))
                .chain(acc.u.limbs())
                //.chain(acc.e_comm.limbs())
                .chain(
                    acc.compressed_e_sum
                        .as_ref()
                        .map(ProperCrtUint::limbs)
                        .into_iter()
                        .flatten(),
                )
                .copied()
                .collect_vec();
            let mut poseidon_chip = PoseidonSponge::<C::Scalar, T, RATE>::new::<R_F, R_P, SECURE_MDS>(builder.main()); //PoseidonSponge::from_spec(builder.main(), self.poseidon_spec.clone());
            poseidon_chip.update(&inputs);
            let hash = poseidon_chip.squeeze(builder.main(), &self.gate_chip);
            let hash_le_bits = self.gate_chip.num_to_bits(builder.main(), hash, 254);
            Ok(self.gate_chip.bits_to_num(builder.main(), (&hash_le_bits[..NUM_HASH_BITS]).to_vec()))
        }
    }

    // #[derive(Clone, Debug)]
    pub struct PoseidonTranscriptChip<'a, C: TwoChainCurve> 
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,
    {
        poseidon_chip: PoseidonSponge<C::Scalar, T, RATE>,
        chip: Chip<'a, C>,
        proof: Value<Cursor<Vec<u8>>>,
    }

    #[derive(Clone)]
    pub struct Challenge<F: BigPrimeField> {
        pub le_bits: Vec<AssignedValue<F>>,
        pub scalar: ProperCrtUint<F>,
    }

    // impl<F: BigPrimeField> Debug for Challenge<F> {
    //     // fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //     //     let mut f = f.debug_struct("Challenge");
    //     //     self.scalar
    //     //         .scalar
    //     //         .value()
    //     //         .map(|scalar| f.field("scalar", &scalar));
    //     //     f.finish()
    //     // }
    // }

    impl<F: BigPrimeField> AsRef<ProperCrtUint<F>> for Challenge<F> {
        fn as_ref(&self) -> &ProperCrtUint<F> {
            &self.scalar
        }
    }

    impl<'a, C: TwoChainCurve> PoseidonTranscriptChip<'a, C>
    where
        C: TwoChainCurve,
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {

        pub fn new(ctx: &mut Context<C::Scalar>, spec: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
            chip: Chip<'a, C>, proof: Value<Vec<u8>>) -> Self {
            let poseidon_chip = PoseidonSponge::from_spec(ctx, spec);
            PoseidonTranscriptChip {
                poseidon_chip,
                chip,
                proof: proof.map(Cursor::new),
            }
        }

        pub fn dummy_proof(avp: &ProtostarAccumulationVerifierParam<C::Scalar>) -> Vec<u8> {
            let uncompressed_comm_size = C::Scalar::ZERO.to_repr().as_ref().len() * 2;
            let scalar_size = C::Base::ZERO.to_repr().as_ref().len();
            let proof_size = avp.num_folding_witness_polys() * uncompressed_comm_size
                + match avp.strategy {
                    NoCompressing => avp.num_cross_terms * uncompressed_comm_size,
                    Compressing => uncompressed_comm_size + avp.num_cross_terms * scalar_size,
            };
            vec![0; proof_size]
        }

        pub fn challenge_to_le_bits(
            &self,
            challenge: &Challenge<C::Scalar>,
        ) -> Result<Vec<AssignedValue<C::Scalar>>, Error> {
            Ok(challenge.scalar.limbs().to_vec())
        }

        pub fn common_field_element(
            &mut self,
            value: &ProperCrtUint<C::Scalar>,
        ) -> Result<(), Error> {
            value.limbs().iter().for_each(|&limb| self.poseidon_chip.update(&[limb]));
            Ok(())
        }

        pub fn common_commitment(
            &mut self,
            value: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        ) -> Result<(), Error> {
            [value.x(), value.y()].iter().filter_map(|&opt| Some(opt)).for_each(|&v| self.poseidon_chip.update(&[v]));
            Ok(())
        }

        pub fn read_field_element(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
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
            let fe = self.chip.assign_witness_base(builder, fe.assign().unwrap_or_default())?;
            self.common_field_element(&fe)?;
            Ok(fe)
        }

        pub fn read_commitment(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
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
            let comm = self.chip.assign_witness_secondary(builder, comm.assign().unwrap_or_default())?;
            self.common_commitment(&comm)?;
            Ok(comm)
        }

        pub fn squeeze_challenges(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            n: usize,
        ) -> Result<Vec<Challenge<C::Scalar>>, Error> {
            (0..n).map(|_| self.squeeze_challenge(builder)).collect()
        }
    
        pub fn common_field_elements(
            &mut self,
            fes: &[ProperCrtUint<C::Scalar>],
        ) -> Result<(), Error> {
            fes.iter().try_for_each(|fe| self.common_field_element(fe))
        }
    
        pub fn read_field_elements(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            n: usize,
        ) -> Result<Vec<ProperCrtUint<C::Scalar>>, Error> {
            (0..n).map(|_| self.read_field_element(builder)).collect()
        }
    
        pub fn common_commitments(
            &mut self,
            comms: &[EcPoint<C::Scalar, AssignedValue<C::Scalar>>],
        ) -> Result<(), Error> {
            comms
                .iter()
                .try_for_each(|comm| self.common_commitment(comm))
        }
    
        pub fn read_commitments(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            n: usize,
        ) -> Result<Vec<EcPoint<C::Scalar, AssignedValue<C::Scalar>>>, Error> {
            let read_commitments = (0..n).map(|_| self.read_commitment(builder)).collect();
            read_commitments
        }
    
        pub fn absorb_accumulator(
            &mut self,
            acc: &AssignedProtostarAccumulatorInstance<
                ProperCrtUint<C::Scalar>,
                EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            >,
        ) -> Result<(), Error> {
            acc.instances
                .iter()
                .try_for_each(|instances| self.common_field_elements(instances))?;
            self.common_commitments(&acc.witness_comms)?;
            self.common_field_elements(&acc.challenges)?;
            self.common_field_element(&acc.u)?;
            self.common_commitment(&acc.e_comm)?;
            if let Some(compressed_e_sum) = acc.compressed_e_sum.as_ref() {
                self.common_field_element(compressed_e_sum)?;
            }
            Ok(())
        }
        
        //todo fix this
        pub fn squeeze_challenge(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
        ) -> Result<Challenge<C::Scalar>, Error> {
            // let (challenge_le_bits, challenge) = {
            //     let hash = self.poseidon_chip.squeeze(builder.main(), &self.chip.gate_chip);
            //     self.poseidon_chip.update(&[hash]);

            //     let challenge_le_bits = decompose(&hash, NUM_LIMBS, NUM_CHALLENGE_BITS)
            //         .into_iter()
            //         .take(NUM_CHALLENGE_BITS)
            //         .collect_vec();
            //     //let challenge = from_le_bits(collector, &challenge_le_bits);

            //     (challenge_le_bits, challenge)
            // };

            // let scalar = self.chip.assign_witness_base(builder, witness).unwrap();
            // let limbs = scalar.limbs().iter().map(AsRef::as_ref).copied().collect();

            // let scalar_in_base =
            //     integer_to_native(&self.chip.rns, collector, &scalar, NUM_CHALLENGE_BITS);
            // collector.equal(&challenge, &scalar_in_base);

            let scalar = self.chip.assign_constant_base(builder, C::Base::ONE).unwrap();
            let challenge_le_bits = vec![self.chip.assign_constant(builder, C::Scalar::ONE).unwrap()];
            Ok(Challenge {
                le_bits: challenge_le_bits,
                scalar: scalar,
            })
        }
    }
}