use crate::{
    accumulation::protostar::{
        ivc::{halo2::cyclefold::{self, CycleFoldCircuit}, halo2::{
            // preprocess, prove_steps, prove_decider, verify_decider, 
            // ProtostarIvcVerifierParam,
            chips::transcript::{accumulation_transcript_param, PoseidonTranscript}, preprocess, prove_steps, CircuitExt, StepCircuit
        }},
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
            fe_from_bits_le, fe_to_fe, CurveAffine, Field, FromUniformBytes, MultiMillerLoop, PrimeFieldBits, TwoChainCurve
        }, chain, end_timer, start_timer, test::seeded_std_rng, transcript::InMemoryTranscript, DeserializeOwned, Itertools, Serialize
    },
};
use halo2_base::{halo2_proofs::{
    halo2curves::{bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta},
}, plonk::{Advice, Column}, poly::Rotation, dev::MockProver}, AssignedValue, gates::circuit::{BaseConfig, builder::BaseCircuitBuilder, BaseCircuitParams, self}};

use halo2_base::{Context,
    gates::{range::RangeInstructions, circuit::{builder::RangeCircuitBuilder, CircuitBuilderStage}, 
            flex_gate::{GateChip, GateInstructions}},
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
    poseidon::hasher::{PoseidonSponge, PoseidonHasher, spec::OptimizedPoseidonSpec, PoseidonHash},
};
use halo2_ecc::{fields::{fp::FpChip, native_fp::NativeFieldChip}, ecc::EccChip};
use halo2_base::halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value, SimpleFloorPlanner},
    plonk::{Circuit, Selector, ConstraintSystem, Error},
};

use core::num;
use rand::RngCore;
use std::{mem, rc::Rc};
use std::{fmt::Debug, hash::Hash, marker::PhantomData, convert::From, time::Instant};
use super::{chips::main_chip::{MainChipConfig, Number}, ProtostarIvcVerifierParam};

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
    cyclefold_num_vars: usize,
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
    let cyclefold_atp = accumulation_transcript_param::<C::Base>();
    
    let preprocess_time = Instant::now();
    let (mut primary_circuit, mut cyclefold_circuit, ivc_pp, ivc_vp) = preprocess::<
        C,
        P1,
        P2,
        _,
        PoseidonTranscript<_, _>,
        PoseidonTranscript<_, _>,
    >(  
        primary_num_vars,
        primary_atp,
        TrivialCircuit::default(),
        cyclefold_num_vars,
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

// // #[test]
// // fn gemini_kzg_ipa_protostar_hyperplonk_cyclefold_mock() {
// //     let cyclefold_circuit_params = BaseCircuitParams {
// //         k: 16,
// //         num_advice_per_phase: vec![1],
// //         num_lookup_advice_per_phase: vec![1],
// //         num_fixed: 1,
// //         lookup_bits: Some(13),
// //         num_instance_columns: 1,
// //     };

// //     let cyclefold_circuit = CycleFoldCircuit::<bn256::G1Affine>::new(None, cyclefold_circuit_params.clone());
// //     // let instances = cyclefold_circuit.instances();
// //     // println!("instances: {:?}", instances.len());
// //     MockProver::run(16, &cyclefold_circuit, vec![]).unwrap().assert_satisfied();
// // }

// pub fn fn_gemini_kzg_ipa_protostar_hyperplonk_ivc(num_steps: usize) {
//     let primary_circuit_params = BaseCircuitParams {
//             k: 19,
//             num_advice_per_phase: vec![1],
//             num_lookup_advice_per_phase: vec![1],
//             num_fixed: 1,
//             lookup_bits: Some(13),
//             num_instance_columns: 1,
//         };

//     let cyclefold_num_vars = 8;
    
//     run_protostar_hyperplonk_ivc::<
//         bn256::G1Affine,
//         Gemini<UnivariateKzg<Bn256>>,
//         MultilinearIpa<grumpkin::G1Affine>,
//     >(num_steps, primary_circuit_params, cyclefold_num_vars);
// }

#[test]
fn gemini_kzg_ipa_protostar_hyperplonk_ivc() {
    const NUM_STEPS: usize = 5;

    let primary_circuit_k = 14;
    let cyclefold_num_vars = 10;
    
    run_protostar_hyperplonk_ivc::<
        bn256::G1Affine,
        Gemini<UnivariateKzg<Bn256>>,
        MultilinearIpa<grumpkin::G1Affine>,
    >(NUM_STEPS, primary_circuit_k, cyclefold_num_vars);
}