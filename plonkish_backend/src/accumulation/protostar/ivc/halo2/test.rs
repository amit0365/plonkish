use crate::{
    accumulation::protostar::{
        ivc::halo2::{chips::{minroot::MinRootCircuit, transcript::{accumulation_transcript_param, PoseidonNativeTranscript, PoseidonTranscript}}, cyclefold::{self, CycleFoldCircuit}, preprocess, prove_steps, CircuitExt, StepCircuit},
        ProtostarAccumulatorInstance, ProtostarVerifierParam,
    },
    backend::{
        hyperplonk::{HyperPlonk, HyperPlonkVerifierParam},
        PlonkishBackend, PlonkishCircuit,
    },
    frontend::halo2::{layouter::InstanceExtractor, Halo2Circuit},
    pcs::{
        multilinear::{Gemini, MultilinearHyrax, MultilinearIpa, MultilinearIpaParams},
        univariate::{UnivariateKzg, UnivariateKzgParam},
        AdditiveCommitment, PolynomialCommitmentScheme,
    },
    poly::multilinear::MultilinearPolynomial,
    util::{
        arithmetic::{
            fe_from_bits_le, fe_to_fe, CurveAffine, Field, FromUniformBytes, MultiMillerLoop, PrimeFieldBits, TwoChainCurve
        }, chain, end_timer, start_timer, test::seeded_std_rng, transcript::{InMemoryTranscript, TranscriptRead, TranscriptWrite}, DeserializeOwned, Itertools, Serialize
    },
};
use halo2_proofs::halo2curves::{bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta}};
use halo2_base::utils::{CurveAffineExt, ScalarField, BigPrimeField};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};

use core::num;
use rand::RngCore;
use std::{fs::File, io::Cursor, mem, rc::Rc, time::Duration};
use std::{fmt::Debug, hash::Hash, marker::PhantomData, convert::From, time::Instant};
use super::{chips::main_chip::{MainChipConfig, Number}, ivc_circuits::primary::{PrimaryCircuit, PrimaryCircuitConfig}, ProtostarIvcProverParam, ProtostarIvcVerifierParam};
use super::ivc_circuits::primary::{T, RATE};

// use self::strawman::{NUM_LIMB_BITS, NUM_LIMBS, T, RATE, R_F, R_P, SECURE_MDS, Chip};
// use super::RecursiveCircuit;

#[derive(Clone, Debug, Default)]
pub struct TrivialCircuit<C> {
    step_idx: usize,
    _marker: PhantomData<C>,
}

impl<C> Circuit<C::Scalar> for TrivialCircuit<C>
where
    C: CurveAffine,
    C::Scalar: BigPrimeField + FromUniformBytes<64>,
{
    type Config = MainChipConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(_: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        unreachable!()
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

    fn rand(k: usize, _: impl RngCore)-> TrivialCircuit<C> {
        unimplemented!()
    }
    
}

impl<C: TwoChainCurve> StepCircuit<C> for TrivialCircuit<C>
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{

    fn arity() -> usize {
        0
    }

    fn initial_input(&self) -> &[C::Scalar] {
        &[]
    }

    fn setup(&mut self) -> C::Scalar {
        C::Scalar::from(0u64)
    }

    fn input(&self) -> &[C::Scalar] {
        &[]
    }

    fn set_input(&mut self, input: &[C::Scalar]) {
    }

    fn output(&self) -> &[C::Scalar] {
        &[]
    }

    fn set_output(&mut self, output: &[C::Scalar]) {
    }

    fn next_output(&mut self) -> Vec<C::Scalar> {
        Vec::new()
    }

    fn step_idx(&self) -> usize {
        self.step_idx
    }

    fn next(&mut self) {
        self.step_idx += 1;
    }

    fn num_constraints(&self) -> usize {
        0
    }

    //todo fix this with other synthesizes
    fn synthesize(
        &mut self,
        _: PrimaryCircuitConfig<C>,
        _: impl Layouter<C::Scalar>,
    ) -> Result<
        (
            Vec<Number<C::Scalar>>,
            Vec<Number<C::Scalar>>,
        ),
        Error,
    > {
        Ok((Vec::new(), Vec::new()))
    }
}

#[allow(clippy::type_complexity)]
pub fn run_protostar_hyperplonk_ivc<C, P1, P2>(
    num_steps: usize,
    primary_circuit_k: usize,
    primary_param: P1::Param,
    cyclefold_num_vars: usize,
    cyclefold_param: P2::Param,
) -> (
    // ProtostarIvcVerifierParam<
    //     C,
    //     P1,
    //     P2
    // >,
    // ProtostarAccumulatorInstance<C::Scalar, P1::Commitment>,
    // Vec<u8>,
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
    let primary_num_vars = primary_circuit_k;
    let primary_atp = accumulation_transcript_param::<C::Scalar>();
    let cyclefold_atp = accumulation_transcript_param::<C::Scalar>();
    println!("primary_atp done");
    let preprocess_time = Instant::now();
    let (mut primary_circuit, mut cyclefold_circuit, ivc_pp, ivc_vp) = preprocess::<
        C,
        P1,
        P2,
        _,
        PoseidonNativeTranscript<C::Scalar, _>,
        PoseidonTranscript<C::Scalar, _>,
    >(  
        primary_num_vars,
        primary_param,
        primary_atp,
        TrivialCircuit::default(),
        cyclefold_num_vars,
        cyclefold_param,
        cyclefold_atp,
        seeded_std_rng(),
    )
    .unwrap();
    let duration_preprocess = preprocess_time.elapsed();
    println!("Time for preprocess: {:?}", duration_preprocess);

    let prove_steps_time = Instant::now();
    let (primary_acc, mut cyclefold_acc) = prove_steps(
        &ivc_pp, 
        &mut primary_circuit,
        &mut cyclefold_circuit,
        num_steps,
        seeded_std_rng(),
    )
    .unwrap();
    let duration_prove_steps = prove_steps_time.elapsed();
    println!("Time for prove_steps: {:?}", duration_prove_steps);

    // let primary_dtp = strawman::decider_transcript_param();
    // let prove_decider_time = Instant::now();
    // let (
    //     primary_acc,
    //     primary_proof,
    // ) = {
    //     let mut primary_transcript = strawman::PoseidonTranscript::new(primary_dtp.clone());
    //     prove_decider(
    //         &ivc_pp,
    //         &primary_acc,
    //         &mut primary_transcript,
    //         seeded_std_rng(),
    //     )
    //     .unwrap();

    //     (
    //         primary_acc.instance,
    //         primary_transcript.into_proof(),
    //     )
    // };
    // println!("primary_proof: {:?}", primary_proof.len());
    // let duration_prove_decider = prove_decider_time.elapsed();
    // println!("Time for prove_decider: {:?}", duration_prove_decider);

    // let verify_decider_time = Instant::now();
    // let result = {
    //     let mut primary_transcript =
    //         strawman::PoseidonTranscript::from_proof(primary_dtp, primary_proof.as_slice());
    //     verify_decider::<_, _, _>(
    //         &ivc_vp,
    //         &primary_acc,
    //         &mut primary_transcript,
    //         seeded_std_rng(),
    //     )
    // };
    // let duration_verify_decider = verify_decider_time.elapsed();
    // println!("Time for verify_decider: {:?}", duration_verify_decider);
    //assert_eq!(result, Ok(()));

    // (
    //     ivc_vp,
    //     primary_acc,
    //     primary_proof,
    // )

}

    // let primary_dtp = strawman::decider_transcript_param();
    // let secondary_dtp = strawman::decider_transcript_param();

    // let prove_decider_time = Instant::now();
    // let (
    //     primary_acc,
    //     primary_initial_input,
    //     primary_output,
    //     primary_proof,
    //     secondary_acc_before_last,
    //     secondary_initial_input,
    //     secondary_output,
    //     secondary_proof,
    // ) = {
    //     let secondary_acc_before_last = secondary_acc.instance.clone();
    //     let mut primary_transcript = strawman::PoseidonTranscript::new(primary_dtp.clone());
    //     let mut secondary_transcript = strawman::PoseidonTranscript::new(secondary_dtp.clone());
    //     prove_decider(
    //         &ivc_pp,
    //         &primary_acc,
    //         &mut primary_transcript,
    //         &mut secondary_acc,
    //         &secondary_circuit,
    //         &mut secondary_transcript,
    //         seeded_std_rng(),
    //     )
    //     .unwrap();

    //     (
    //         primary_acc.instance,
    //         StepCircuit::<C>::initial_input(&primary_circuit.circuit().step_circuit),
    //         StepCircuit::<C>::output(&primary_circuit.circuit().step_circuit),
    //         primary_transcript.into_proof(),
    //         secondary_acc_before_last,
    //         StepCircuit::<C::Secondary>::initial_input(&secondary_circuit.circuit().step_circuit),
    //         StepCircuit::<C::Secondary>::output(&secondary_circuit.circuit().step_circuit),
    //         secondary_transcript.into_proof(),
    //     )
    // };
    // let duration_prove_decider = prove_decider_time.elapsed();
    // println!("Time for prove_decider: {:?}", duration_prove_decider);

    // let verify_decider_time = Instant::now();
    // let result = {
    //     let mut primary_transcript =
    //         strawman::PoseidonTranscript::from_proof(primary_dtp, primary_proof.as_slice());
    //     let mut secondary_transcript =
    //         strawman::PoseidonTranscript::from_proof(secondary_dtp, secondary_proof.as_slice());
    //     verify_decider::<_, _, _>(
    //         &ivc_vp,
    //         num_steps,
    //         primary_initial_input,
    //         primary_output,
    //         &primary_acc,
    //         &mut primary_transcript,
    //         secondary_initial_input,
    //         secondary_output,
    //         secondary_acc_before_last.clone(),
    //         &[secondary_last_instances.clone()],
    //         &mut secondary_transcript,
    //         seeded_std_rng(),
    //     )
    // };
    // let duration_verify_decider = verify_decider_time.elapsed();
    // println!("Time for verify_decider: {:?}", duration_verify_decider);
    // assert_eq!(result, Ok(()));

    // (
    //     ivc_vp,
    //     num_steps,
    //     primary_initial_input.to_vec(),
    //     primary_output.to_vec(),
    //     primary_acc,
    //     primary_proof,
    //     secondary_initial_input.to_vec(),
    //     secondary_output.to_vec(),
    //     secondary_acc_before_last,
    //     secondary_last_instances,
    //     secondary_proof,
    // )

// #[allow(clippy::type_complexity)]
// pub fn run_protostar_hyperplonk_ivc_minroot_preprocess<C, P1, P2>(
//     num_steps: usize,
//     primary_circuit_k: usize,
//     primary_param: P1::Param,
//     cyclefold_num_vars: usize,
//     cyclefold_param: P2::Param,
// ) -> (
//     Halo2Circuit<C::Scalar, PrimaryCircuit<C, MinRootCircuit<C>>>,
//     Halo2Circuit<C::Base, CycleFoldCircuit<C::Secondary>>,
//     ProtostarIvcProverParam<
//         C,
//         P1,
//         P2,
//         PoseidonTranscript<C::Base, Cursor<Vec<u8>>>,
//         PoseidonTranscript<C::Scalar, Cursor<Vec<u8>>>,
//     >,
//     ProtostarIvcVerifierParam<
//         C,
//         P1,
//         P2,
//     >,
//     usize,
//     usize,
// )
// where
//     C: TwoChainCurve,
//     C::Base: BigPrimeField + PrimeFieldBits + Serialize + DeserializeOwned,
//     C::Scalar: BigPrimeField + PrimeFieldBits + Serialize + DeserializeOwned,
//     P1: PolynomialCommitmentScheme<
//     C::ScalarExt,
//     Polynomial = MultilinearPolynomial<C::Scalar>,
//     CommitmentChunk = C,
//     >,
//     P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
//     P2: PolynomialCommitmentScheme<
//     C::Base,
//     Polynomial = MultilinearPolynomial<C::Base>,
//     CommitmentChunk = C::Secondary,
//     >,
//     P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
// {
// //let rng = OsRng;
// let primary_atp = accumulation_transcript_param();
// let secondary_atp = accumulation_transcript_param();
// let minroot_circuit = MinRootCircuit::<C>::new(MinRootOutput{ i: C::Scalar::ZERO, pt_ai: C::Secondary::identity(), pt_bi: C::Secondary::identity()}, 1);    
    
// let preprocess_time = Instant::now();
// let (primary_circuit, secondary_circuit, ivc_pp, ivc_vp) = preprocess::<
//     C,
//     P1,
//     P2,
//     MinRootCircuit<C>,
//     PoseidonTranscript<_, _>,
//     PoseidonTranscript<_, _>,
// >(  
//     primary_num_vars
//     primary_param,
//     primary_atp,
//     minroot_circuit,
//     secondary_num_vars,
//     secondary_atp,
//     TrivialCircuit::default(),
//     circuit_params.clone(), 
//     seeded_std_rng(),
// )
// .unwrap();
// println!("Preprocess time: {:?}", preprocess_time.elapsed());

// let primary_witness_size = primary_circuit.circuit().witness_ref.clone().into_inner();
// let secondary_witness_size = secondary_circuit.circuit().witness_ref.clone().into_inner();

// (primary_circuit, secondary_circuit, ivc_pp, ivc_vp, primary_witness_size, secondary_witness_size)
// }

// #[allow(clippy::type_complexity)]
// pub fn run_protostar_hyperplonk_ivc_prove<C, Sc1, Sc2, P1, P2, AT1, AT2>(
//     mut primary_circuit: Halo2Circuit<C::Scalar, PrimaryCircuit<C, Sc1>>,
//     mut secondary_circuit: Halo2Circuit<C::Base, CycleFoldCircuit<C::Secondary>>,
//     ivc_pp: ProtostarIvcProverParam<C, P1, P2, AT1, AT2>,
//     ivc_vp: ProtostarIvcVerifierParam<C, P1, P2>,
//     num_steps: usize,
// ) -> Duration
// where
//     C: TwoChainCurve,
//     C::Base: BigPrimeField + PrimeFieldBits + Serialize + DeserializeOwned,
//     C::Scalar: BigPrimeField + PrimeFieldBits + Serialize + DeserializeOwned,
//     P1: PolynomialCommitmentScheme<
//         C::ScalarExt,
//         Polynomial = MultilinearPolynomial<C::Scalar>,
//         CommitmentChunk = C,
//     >,
//     P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
//     P2: PolynomialCommitmentScheme<
//         C::Base,
//         Polynomial = MultilinearPolynomial<C::Base>,
//         CommitmentChunk = C::Secondary,
//     >,
//     P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
//     Sc1: StepCircuit<C>,
//     Sc2: StepCircuit<C::Secondary>,
//     AT1: TranscriptRead<P1::CommitmentChunk, C::Scalar>
//     + TranscriptWrite<P1::CommitmentChunk, C::Scalar>
//     + InMemoryTranscript,
//     AT2: TranscriptRead<P2::CommitmentChunk, C::Base>
//         + TranscriptWrite<P2::CommitmentChunk, C::Base>
//         + InMemoryTranscript,
// {
//     let prove_time = Instant::now();
//     let (primary_acc, mut secondary_acc, secondary_last_instances) = prove_steps(
//         &ivc_pp, 
//         &mut primary_circuit,
//         &mut secondary_circuit,
//         num_steps,
//         seeded_std_rng(),
//     )
//     .unwrap();
//     prove_time.elapsed()
// }

#[test]
fn gemini_kzg_ipa_protostar_hyperplonk_ivc() {
    const NUM_STEPS: usize = 2;

    let primary_circuit_k = 13;
    let cyclefold_num_vars = 10;
    let time = Instant::now();
    let primary_params = UnivariateKzg::setup(1 << (primary_circuit_k + 4), 0, &mut seeded_std_rng()).unwrap();
    println!("primary_params done: {:?}", time.elapsed());
    //primary_params.save_to_file("kzg_param.bin").unwrap();
    //let primary_params = UnivariateKzgParam::load_from_file("kzg_param.bin").unwrap();
    let time = Instant::now();
    let cyclefold_params = MultilinearIpa::setup(1 << (cyclefold_num_vars + 4), 0, &mut seeded_std_rng()).unwrap();
    println!("cyclefold_params done: {:?}", time.elapsed());
    //cyclefold_params.save_to_file("ipa_param.bin").unwrap();
    //let cyclefold_params = MultilinearIpaParam::load_from_file("ipa_param.bin").unwrap();
    run_protostar_hyperplonk_ivc::<
        bn256::G1Affine,
        Gemini<UnivariateKzg<Bn256>>,
        MultilinearIpa<grumpkin::G1Affine>,
    >(NUM_STEPS, primary_circuit_k, primary_params, cyclefold_num_vars, cyclefold_params);
}