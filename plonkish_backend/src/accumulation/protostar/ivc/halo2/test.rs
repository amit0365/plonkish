use crate::{
    accumulation::protostar::{
        ivc::{halo2::{
            preprocess, prove_steps, prove_decider, verify_decider, 
            ProtostarIvcVerifierParam,
            StepCircuit, CircuitExt
        }, cyclefold::CycleFoldCircuit},
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
            TwoChainCurve, MultiMillerLoop, fe_from_bits_le,
        },
        chain,
        test::seeded_std_rng,
        transcript::InMemoryTranscript,
        DeserializeOwned, Itertools, Serialize, end_timer, start_timer,
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
use rand::RngCore;

use std::{fmt::Debug, hash::Hash, marker::PhantomData, convert::From, time::Instant};
use std::{mem, rc::Rc};

use self::strawman::{NUM_LIMB_BITS, NUM_LIMBS, T, RATE, R_F, R_P, SECURE_MDS, Chip};

use super::RecursiveCircuit;



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
    type Config = BaseConfig<C::Scalar>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = BaseCircuitParams;

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
            Vec<AssignedValue<C::Scalar>>,
            Vec<AssignedValue<C::Scalar>>,
        ),
        Error,
    > {
        Ok((Vec::new(), Vec::new()))
    }
}

#[allow(clippy::type_complexity)]
pub fn run_protostar_hyperplonk_ivc<C, P1, P2>(
    num_steps: usize,
    primary_circuit_params: BaseCircuitParams,
    cyclefold_circuit_params: BaseCircuitParams,
) -> (
    ProtostarIvcVerifierParam<
        C,
        P1,
        P2
    >,
    ProtostarAccumulatorInstance<C::Scalar, P1::Commitment>,
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
    let primary_num_vars = primary_circuit_params.k;
    let primary_atp = strawman::accumulation_transcript_param();
    let cyclefold_num_vars = cyclefold_circuit_params.k;
    let cyclefold_atp = strawman::accumulation_transcript_param();
    
    let preprocess_time = Instant::now();
    let (mut primary_circuit, mut cyclefold_circuit, ivc_pp, ivc_vp) = preprocess::<
        C,
        P1,
        P2,
        _,
        strawman::PoseidonNativeTranscript<_, _>,
        strawman::PoseidonTranscript<_, _>,
    >(  
        primary_num_vars,
        primary_atp,
        TrivialCircuit::default(),
        cyclefold_num_vars,
        cyclefold_atp,
        primary_circuit_params.clone(), 
        cyclefold_circuit_params.clone(),
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

    let primary_dtp = strawman::decider_transcript_param();
    let prove_decider_time = Instant::now();
    let (
        primary_acc,
        primary_proof,
    ) = {
        let mut primary_transcript = strawman::PoseidonTranscript::new(primary_dtp.clone());
        prove_decider(
            &ivc_pp,
            &primary_acc,
            &cyclefold_acc,
            &mut primary_transcript,
            seeded_std_rng(),
        )
        .unwrap();

        (
            primary_acc.instance,
            primary_transcript.into_proof(),
        )
    };
    println!("primary_proof: {:?}", primary_proof.len());
    let duration_prove_decider = prove_decider_time.elapsed();
    println!("Time for prove_decider: {:?}", duration_prove_decider);

    let verify_decider_time = Instant::now();
    let result = {
        let mut primary_transcript =
            strawman::PoseidonTranscript::from_proof(primary_dtp, primary_proof.as_slice());
        verify_decider::<_, _, _>(
            &ivc_vp,
            &primary_acc,
            &mut primary_transcript,
            seeded_std_rng(),
        )
    };
    let duration_verify_decider = verify_decider_time.elapsed();
    println!("Time for verify_decider: {:?}", duration_verify_decider);
    assert_eq!(result, Ok(()));

    (
        ivc_vp,
        primary_acc,
        primary_proof,
    )

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

// #[test]
// fn gemini_kzg_ipa_protostar_hyperplonk_cyclefold_mock() {
//     let cyclefold_circuit_params = BaseCircuitParams {
//         k: 16,
//         num_advice_per_phase: vec![1],
//         num_lookup_advice_per_phase: vec![1],
//         num_fixed: 1,
//         lookup_bits: Some(13),
//         num_instance_columns: 1,
//     };

//     let cyclefold_circuit = CycleFoldCircuit::<bn256::G1Affine>::new(None, cyclefold_circuit_params.clone());
//     // let instances = cyclefold_circuit.instances();
//     // println!("instances: {:?}", instances.len());
//     MockProver::run(16, &cyclefold_circuit, vec![]).unwrap().assert_satisfied();
// }



#[test]
fn gemini_kzg_ipa_protostar_hyperplonk_ivc() {
    const NUM_STEPS: usize = 6;

    let primary_circuit_params = BaseCircuitParams {
            k: 19,
            num_advice_per_phase: vec![1],
            num_lookup_advice_per_phase: vec![1],
            num_fixed: 1,
            lookup_bits: Some(13),
            num_instance_columns: 1,
        };

    let cyclefold_circuit_params = BaseCircuitParams {
            k: 17,
            num_advice_per_phase: vec![1],
            num_lookup_advice_per_phase: vec![0],
            num_fixed: 1,
            lookup_bits: Some(1),
            num_instance_columns: 1,
        };

    run_protostar_hyperplonk_ivc::<
        bn256::G1Affine,
        Gemini<UnivariateKzg<Bn256>>,
        MultilinearIpa<grumpkin::G1Affine>,
    >(NUM_STEPS, primary_circuit_params, cyclefold_circuit_params);
}


pub mod strawman {
    use crate::{
        accumulation::protostar::{
            ivc::{halo2::{test::strawman, AssignedProtostarAccumulatorInstance}, ProtostarAccumulationVerifierParam}, ProtostarAccumulatorInstance, ProtostarStrategy::{Compressing, NoCompressing}
        }, pcs::{multilinear::{Gemini, MultilinearHyrax}, univariate::UnivariateKzg, PolynomialCommitmentScheme}, util::{
            arithmetic::{
                fe_from_bits_le, fe_from_bool, fe_from_le_bytes, fe_to_fe, fe_truncated, BitField, CurveAffine, Field, FromUniformBytes, Group, OverridenCurveAffine, PrimeCurveAffine, PrimeField, PrimeFieldBits, TwoChainCurve
            }, end_timer, hash::{poseidon::Spec, Poseidon}, izip_eq, start_timer, transcript::{
                FieldTranscript, FieldTranscriptRead, FieldTranscriptWrite, InMemoryTranscript,
                Transcript, TranscriptRead, TranscriptWrite,
            }, Itertools
        }
    };

    use ark_std::end_timer;
    use halo2_base::{
        gates::{
            circuit::{builder::BaseCircuitBuilder, BaseCircuitParams, BaseConfig, CircuitBuilderStage}, flex_gate::{threads::SinglePhaseCoreManager, BasicGateConfig, FlexGateConfig, FlexGateConfigParams, GateChip, GateInstructions}, range::RangeConfig, RangeChip
        }, halo2_proofs::{circuit::Cell, plonk::Assigned, transcript}, poseidon::hasher::{spec::OptimizedPoseidonSpec, PoseidonHash, PoseidonHasher, PoseidonSponge}, utils::{decompose, decompose_fe_to_u64_limbs, fe_to_biguint, testing::base_test, BigPrimeField, CurveAffineExt, ScalarField}, AssignedValue, Context, ContextCell, QuantumCell::{Constant, Existing, Witness, WitnessFraction}
    };
    use halo2_base::halo2_proofs::plonk::Circuit;
    
    use halo2_base::halo2_proofs::{
        circuit::{AssignedCell, Layouter, Value},
        plonk::{Column, ConstraintSystem, Error, Instance},
    };
    
    use halo2_ecc::{
        fields::{fp::FpChip, FieldChip, native_fp::NativeFieldChip, Selectable},
        bigint::{self, CRTInteger, FixedCRTInteger, ProperCrtUint, ProperUint},
        ecc::{fixed_base, scalar_multiply, EcPoint, EccChip, BaseFieldEccChip, self},
    };

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

    use halo2_base::halo2_proofs::halo2curves::{
        bn256::{self, Bn256, Fr, Fq}, grumpkin};

    pub const NUM_LIMBS: usize = 3;
    pub const NUM_LIMB_BITS: usize = 88;
    pub const NUM_LIMB_BITS_PRIMARY_NON_NATIVE: usize = NUM_LIMB_BITS;
    pub const NUM_LIMBS_PRIMARY_NON_NATIVE: usize = NUM_LIMBS;
    pub const NUM_SUBLIMBS: usize = 5;
    pub const NUM_LOOKUPS: usize = 1;
    pub const LOOKUP_BITS: usize = 8;
    pub const WINDOW_BITS: usize = 4;

    pub const T: usize = 5;
    pub const RATE: usize = 4;
    pub const R_F: usize = 8;
    pub const R_P: usize = 60;
    pub const SECURE_MDS: usize = 0;

    pub const RANGE_BITS: usize = 254;
    pub const NUM_CHALLENGE_BITS: usize = 128;
    pub const NUM_CHALLENGE_BYTES: usize = NUM_CHALLENGE_BITS / 8;
    pub const NUM_HASH_BITS: usize = 250;

    pub fn fe_to_limbs<F1: ScalarField, F2: ScalarField>(fe: F1, num_limb_bits: usize, num_limbs: usize) -> Vec<F2> {
        fe.to_bytes_le()
            .chunks(num_limb_bits/8)
            .into_iter()
            .map(|bytes| match bytes.len() {
                1..=8 => F2::from_bytes_le(bytes),
                9..=16 => {
                    let lo = &bytes[..8];
                    let hi = &bytes[8..];
                    F2::from_bytes_le(hi) * F2::from(2).pow_vartime([64]) + F2::from_bytes_le(lo)
                }
                _ => unimplemented!(),
            })
            .take(num_limbs)
            .collect()
    }

    pub fn fe_from_limbs<F1: ScalarField, F2: ScalarField>(
        limbs: &[F1],
        num_limb_bits: usize,
    ) -> F2 {
        limbs.iter().rev().fold(F2::ZERO, |acc, limb| {
            acc * F2::from_u128(1 << num_limb_bits) + fe_to_fe::<F1, F2>(*limb)
        })
    }

    pub fn into_coordinates<C: CurveAffine>(ec_point: &C) -> [C::Base; 2] {
        let coords = ec_point.coordinates().unwrap();
        [*coords.x(), *coords.y()]
    }

    pub fn accumulation_transcript_param<F: ScalarField>() -> OptimizedPoseidonSpec<F, T, RATE> {
        OptimizedPoseidonSpec::new::<R_F, R_P,SECURE_MDS>()
    }

    pub fn decider_transcript_param<F: ScalarField>() -> OptimizedPoseidonSpec<F, T, RATE> {
        OptimizedPoseidonSpec::new::<R_F, R_P,SECURE_MDS>()
    }

    pub struct PoseidonNativeTranscript<F: ScalarField, S> {
        state: PoseidonHash<F, T, RATE>,
        stream: S,
    }

    impl<F: ScalarField> InMemoryTranscript for PoseidonNativeTranscript<F, Cursor<Vec<u8>>> {
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

    impl<F: ScalarField, S> FieldTranscript<F>
        for PoseidonNativeTranscript<F, S>
    {
        fn squeeze_challenge(&mut self) -> F {
            let hash = self.state.squeeze();
            self.state.update(&[hash]);
            fe_from_le_bytes(&hash.to_repr().as_ref()[..NUM_CHALLENGE_BYTES])
        }

        fn common_field_element(&mut self, fe: &F) -> Result<(), crate::Error> {
            self.state.update(&[*fe]);
            Ok(())
        }
    }

    impl<F: ScalarField, R: io::Read> FieldTranscriptRead<F>
        for PoseidonNativeTranscript<F, R>
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

    impl<F: ScalarField, W: io::Write> FieldTranscriptWrite<F>
        for PoseidonNativeTranscript<F, W>
    {
        fn write_field_element(&mut self, fe: &F) -> Result<(), crate::Error> {
            self.common_field_element(fe)?;
            let repr = fe.to_repr();
            self.stream
                .write_all(repr.as_ref())
                .map_err(|err| crate::Error::Transcript(err.kind(), err.to_string()))
        }
    }

    impl<C: CurveAffine, S> Transcript<C, C::Scalar> for PoseidonNativeTranscript<C::Scalar, S>
    where
        C::Base: ScalarField,
        C::Scalar: ScalarField,
    {
        fn common_commitment(&mut self, ec_point: &C) -> Result<(), crate::Error> {
            let element = into_coordinates(ec_point).into_iter().map(|fe| fe_to_limbs(fe, NUM_LIMB_BITS_PRIMARY_NON_NATIVE, NUM_LIMBS_PRIMARY_NON_NATIVE)).flatten().collect_vec();
            self.state.update(&element);
            Ok(())
        }
    }

    impl<C: CurveAffine, R: io::Read> TranscriptRead<C, C::Scalar> for PoseidonNativeTranscript<C::Scalar, R>
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

    impl<C: CurveAffine, W: io::Write> TranscriptWrite<C, C::Scalar> for PoseidonNativeTranscript<C::Scalar, W>
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

        fn common_field_element(&mut self, fe: &F) -> Result<(), crate::Error> {
            self.state.update(&fe_to_limbs(*fe, NUM_LIMB_BITS, NUM_LIMBS));
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
            self.state.update(&into_coordinates(ec_point));
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

    #[allow(clippy::type_complexity)]
    #[derive(Clone, Debug)]
    pub struct Chip<C: TwoChainCurve> 
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,
    {   
        pub range_chip: RangeChip<C::Scalar>,
        pub gate_chip: GateChip<C::Scalar>
    }

    impl<'a, C: TwoChainCurve> Chip<C> 
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,  
    {

        pub fn create(range_chip: RangeChip<C::Scalar>) -> Self {
            let gate_chip = range_chip.gate.clone();
                Self {
                    range_chip,
                    gate_chip,
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

        pub fn powers(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            base: &AssignedValue<C::Scalar>,
            n: usize,
        ) -> Result<Vec<AssignedValue<C::Scalar>>, Error> {
            Ok(match n {
                0 => Vec::new(),
                1 => vec![self.assign_constant(builder, C::Scalar::ONE)?],
                2 => vec![
                    self.assign_constant(builder, C::Scalar::ONE)?,
                    base.clone(),
                ],
                _ => {
                    let mut powers = Vec::with_capacity(n);
                    powers.push(self.assign_constant(builder, C::Scalar::ONE)?);
                    powers.push(base.clone());
                    for _ in 0..n - 2 {
                        powers.push(self.mul(builder, powers.last().unwrap(), base)?);
                    }
                    powers
                }
            })
        }

        pub fn inner_product<'b, 'c>(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: impl IntoIterator<Item = &'b AssignedValue<C::Scalar>>,
            rhs: impl IntoIterator<Item = &'c AssignedValue<C::Scalar>>,
        ) -> Result<AssignedValue<C::Scalar>, Error> 
        where
        AssignedValue<C::Scalar>: 'c + 'b,
        {
            Ok(self.gate_chip.inner_product(builder.main(), lhs.into_iter().map(|ref_val| Existing(ref_val.into())).collect_vec()
            ,rhs.into_iter().map(|ref_val| Existing(ref_val.into())).collect_vec()
        ))
        }

        pub fn constrain_equal_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &ProperCrtUint<C::Scalar>,
            rhs: &ProperCrtUint<C::Scalar>,
        ) -> Result<(), Error> {
            let base_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS, NUM_LIMBS);
            base_chip.assert_equal(builder.main(),lhs,rhs);
            Ok(())
        }
    
        pub fn assign_constant_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            constant: C::Base,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            let base_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS, NUM_LIMBS);
            Ok(base_chip.load_constant(builder.main(),constant))
        }
    
        pub fn assign_witness_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: C::Base,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            let base_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS, NUM_LIMBS);
            Ok(base_chip.load_private(builder.main(),witness))
        }    
    
        pub fn select_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            condition: &AssignedValue<C::Scalar>,
            when_true: &ProperCrtUint<C::Scalar>,
            when_false: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            let base_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS, NUM_LIMBS);
            Ok(base_chip.select(builder.main(),when_true.clone(),when_false.clone(),*condition))
        }
    
        pub fn fit_base_in_scalar(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            value: &ProperCrtUint<C::Scalar>,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            let zero = builder.main().load_zero();
            let base_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS, NUM_LIMBS);
            let decomposed = (0..NUM_LIMBS)
            .flat_map(|idx| {
                let number_of_bits = if idx == NUM_LIMBS - 1 {
                    base_chip.p.bits() as usize % NUM_LIMB_BITS
                } else {
                    NUM_LIMB_BITS
                };
                self.gate_chip.num_to_bits(builder.main(), value.limbs()[idx], number_of_bits)
            })
            .collect_vec();

            assert_eq!(decomposed.len(), base_chip.p.bits() as usize);

            decomposed
                .iter()
                .skip(NUM_HASH_BITS)
                .for_each(|bit| builder.main().constrain_equal(bit, &zero));

            Ok(self.gate_chip.bits_to_num(builder.main(), &decomposed[..NUM_HASH_BITS]))
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
            let base_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS, NUM_LIMBS);
            let one = base_chip.load_constant(builder.main(), C::Base::ONE);
            let add = base_chip.add_no_carry(builder.main(), a, b);
            Ok(base_chip.carry_mod(builder.main(), add))
        }
    
        pub fn sub_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            a: &ProperCrtUint<C::Scalar>,
            b: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            let base_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS, NUM_LIMBS);
            let sub = base_chip.sub_no_carry(builder.main(), a, b);
            Ok(base_chip.carry_mod(builder.main(), sub))
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
            let base_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS, NUM_LIMBS);
            Ok(base_chip.mul(builder.main(), lhs, rhs))
        }
    
        pub fn div_incomplete_base(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &ProperCrtUint<C::Scalar>,
            rhs: &ProperCrtUint<C::Scalar>,
        ) -> Result<ProperCrtUint<C::Scalar>, Error> {
            let base_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS, NUM_LIMBS);
            Ok(base_chip.divide_unsafe(builder.main(), lhs, rhs))
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

        pub fn constrain_equal_primary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            rhs: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        ) -> Result<(), Error> {
            let native_chip = NativeFieldChip::new(&self.range_chip);
            let ecc_chip = EccChip::new(&native_chip);
            ecc_chip.assert_equal(builder.main(), lhs.clone(), rhs.clone());
            Ok(())
        }

        pub fn assign_constant_primary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            constant: C::Secondary,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            let native_chip = NativeFieldChip::new(&self.range_chip);
            let ecc_chip = EccChip::new(&native_chip);
            Ok(ecc_chip.assign_constant_point(builder.main(), constant))
        }

        pub fn assign_witness_primary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: C::Secondary,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            let native_chip = NativeFieldChip::new(&self.range_chip);
            let ecc_chip = EccChip::new(&native_chip);
            Ok(ecc_chip.assign_point(builder.main(), witness))
        }

        pub fn select_primary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            condition: &AssignedValue<C::Scalar>,
            when_true: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            when_false: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            let native_chip = NativeFieldChip::new(&self.range_chip);
            let ecc_chip = EccChip::new(&native_chip);
            Ok(ecc_chip.select(builder.main(), when_true.clone(), when_false.clone(), *condition))
        }

        // assume x_1 != x_2 and lhs and rhs are not on infinity
        pub fn add_primary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            rhs: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            let native_chip = NativeFieldChip::new(&self.range_chip);
            let ecc_chip = EccChip::new(&native_chip);
            
            let lhs_x_is_zero = ecc_chip.field_chip.is_zero(builder.main(), &lhs.x);
            let lhs_y_is_zero = ecc_chip.field_chip.is_zero(builder.main(), &lhs.y);
            let lhs_is_zero = ecc_chip.field_chip.mul(builder.main(), lhs_x_is_zero, lhs_y_is_zero);
    
            let rhs_x_is_zero = ecc_chip.field_chip.is_zero(builder.main(), &rhs.x);
            let rhs_y_is_zero = ecc_chip.field_chip.is_zero(builder.main(), &rhs.y);
            let rhs_is_zero = ecc_chip.field_chip.mul(builder.main(), rhs_x_is_zero, rhs_y_is_zero);

            let both_is_zero = ecc_chip.field_chip.mul(builder.main(), lhs_is_zero, rhs_is_zero);
            let lhs_random = ecc_chip.load_random_point::<C::Secondary>(builder.main());
            let rhs_random = ecc_chip.load_random_point::<C::Secondary>(builder.main());
            let identity = self.assign_constant_primary(builder, C::Secondary::identity())?;

            let lhs = self.select_primary(builder, &both_is_zero, &lhs_random, &lhs)?;
            let rhs = self.select_primary(builder, &both_is_zero, &rhs_random, &rhs)?;

            let out_added = ecc_chip.add_unequal(builder.main(), lhs.clone(), rhs.clone(), false);
            let out = self.select_primary(builder, &lhs_is_zero, &rhs, &out_added)?;
            let out_one_could_be_is_zero = self.select_primary(builder, &rhs_is_zero, &lhs, &out)?;
            let result = self.select_primary(builder, &both_is_zero, &identity, &out_one_could_be_is_zero)?;  
            Ok(result)
        }

        pub fn scalar_mul_primary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            base: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            r_le_bits: &[AssignedValue<C::Scalar>],
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            let max_bits = 1;
            let native_chip = NativeFieldChip::new(&self.range_chip);
            let ecc_chip = EccChip::new(&native_chip);
            Ok(ecc_chip.scalar_mult::<C::Secondary>(builder.main(), base.clone(), r_le_bits.to_vec(), max_bits, WINDOW_BITS))
        }

        pub fn constrain_equal_primary_non_native(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            lhs: &EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
            rhs: &EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
        ) -> Result<(), Error> {
            let non_native_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS_PRIMARY_NON_NATIVE, NUM_LIMBS_PRIMARY_NON_NATIVE);
            let ecc_chip = EccChip::new(&non_native_chip);
            ecc_chip.assert_equal(builder.main(), lhs.clone(), rhs.clone());
            Ok(())
        }

        // todo check this unchecked
        pub fn assign_constant_primary_non_native(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            constant: C,
        ) -> Result<EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>, Error> {
            let non_native_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS_PRIMARY_NON_NATIVE, NUM_LIMBS_PRIMARY_NON_NATIVE);
            let ecc_chip = EccChip::new(&non_native_chip);
            Ok(ecc_chip.assign_constant_point(builder.main(), constant))
        }

        // todo check this unchecked
        pub fn assign_witness_primary_non_native(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: C,
        ) -> Result<EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>, Error> {
            let non_native_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS_PRIMARY_NON_NATIVE, NUM_LIMBS_PRIMARY_NON_NATIVE);
            let ecc_chip = EccChip::new(&non_native_chip);
            Ok(ecc_chip.assign_point_unchecked(builder.main(), witness))
        }

        pub fn select_primary_non_native(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            condition: &AssignedValue<C::Scalar>,
            when_true: &EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
            when_false: &EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
        ) -> Result<EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>, Error> {
            let non_native_chip = FpChip::<C::Scalar, C::Base>::new(&self.range_chip, NUM_LIMB_BITS_PRIMARY_NON_NATIVE, NUM_LIMBS_PRIMARY_NON_NATIVE);
            let ecc_chip = EccChip::new(&non_native_chip);
            Ok(ecc_chip.select(builder.main(), when_true.clone(), when_false.clone(), *condition))
        }

        pub fn assign_constant_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            constant: C::Secondary,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            let native_chip = NativeFieldChip::new(&self.range_chip);
            let ecc_chip = EccChip::new(&native_chip);
            Ok(ecc_chip.assign_constant_point(builder.main(), constant))
        }

        pub fn assign_witness_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            witness: C::Secondary,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            let native_chip = NativeFieldChip::new(&self.range_chip);
            let ecc_chip = EccChip::new(&native_chip);
            Ok(ecc_chip.assign_point(builder.main(), witness))
        }

        pub fn select_secondary(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            condition: &AssignedValue<C::Scalar>,
            when_true: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
            when_false: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
            let native_chip = NativeFieldChip::new(&self.range_chip);
            let ecc_chip = EccChip::new(&native_chip);
            Ok(ecc_chip.select(builder.main(), when_true.clone(), when_false.clone(), *condition))
        }

        // // assume x_1 != x_2 and lhs and rhs are not on infinity
        // pub fn add_secondary(
        //     &self,
        //     builder: &mut SinglePhaseCoreManager<C::Scalar>,
        //     lhs: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        //     rhs: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        // ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
        //     let native_chip = NativeFieldChip::new(&self.range_chip);
        //     let ecc_chip = EccChip::new(&native_chip);

        //     let lhs_x_is_zero = ecc_chip.field_chip.is_zero(builder.main(), &lhs.x);
        //     let lhs_y_is_zero = ecc_chip.field_chip.is_zero(builder.main(), &lhs.y);
        //     let lhs_is_zero = ecc_chip.field_chip.mul(builder.main(), lhs_x_is_zero, lhs_y_is_zero);

        //     let rhs_x_is_zero = ecc_chip.field_chip.is_zero(builder.main(), &rhs.x);
        //     let rhs_y_is_zero = ecc_chip.field_chip.is_zero(builder.main(), &rhs.y);
        //     let rhs_is_zero = ecc_chip.field_chip.mul(builder.main(), rhs_x_is_zero, rhs_y_is_zero);
        //     let both_is_zero = ecc_chip.field_chip.mul(builder.main(), lhs_is_zero, rhs_is_zero);
        //     let out_added = ecc_chip.add_unequal(builder.main(), lhs, rhs, false);

        //     let identity = self.assign_constant_secondary(builder, C::Secondary::identity())?;
        //     let out = self.select_secondary(builder, &lhs_is_zero, &rhs, &out_added)?;
        //     let out_one_could_be_is_zero = self.select_secondary(builder, &rhs_is_zero, &lhs, &out)?;
        //     self.select_secondary(builder, &both_is_zero, &identity, &out_one_could_be_is_zero)            
        // }

        // pub fn scalar_mul_secondary(
        //     &self,
        //     builder: &mut SinglePhaseCoreManager<C::Scalar>,
        //     base: &EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        //     le_bits: &[AssignedValue<C::Scalar>],
        // ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error> {
        //     let max_bits = 1;
        //     let native_chip = NativeFieldChip::new(&self.range_chip);
        //     let ecc_chip = EccChip::new(&native_chip);
        //     Ok(ecc_chip.scalar_mult::<C::Secondary>(builder.main(), base.clone(), le_bits.to_vec(), max_bits, WINDOW_BITS))
        // }

        // pub fn fixed_base_msm_secondary(
        //     &self,
        //     builder: &mut SinglePhaseCoreManager<C::Scalar>,
        //     bases: &[C::Secondary],
        //     scalars: Vec<ProperCrtUint<C::Scalar>>,
        // ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error>{
        //     let scalar_limbs_vec = scalars.iter().map(|scalar| scalar.limbs().to_vec()).collect();
        //     let max_scalar_bits_per_cell = NUM_LIMB_BITS;
        //     let native_chip = NativeFieldChip::new(&self.range_chip);
        //     let ecc_chip = EccChip::new(&native_chip);
        //     Ok(ecc_chip.fixed_base_msm::<C::Secondary>(builder, bases, scalar_limbs_vec, max_scalar_bits_per_cell))
        // }

        // pub fn variable_base_msm_secondary(
        //     &self,
        //     builder: &mut SinglePhaseCoreManager<C::Scalar>,
        //     bases: &[EcPoint<C::Scalar, AssignedValue<C::Scalar>>],
        //     scalars: Vec<ProperCrtUint<C::Scalar>>,
        // ) -> Result<EcPoint<C::Scalar, AssignedValue<C::Scalar>>, Error>{
        //     let scalar_limbs_vec = scalars.iter().map(|scalar| scalar.limbs().to_vec()).collect();
        //     let max_bits = NUM_LIMB_BITS;
        //     let native_chip = NativeFieldChip::new(&self.range_chip);
        //     let ecc_chip = EccChip::new(&native_chip);
        //     Ok(ecc_chip.variable_base_msm::<C::Secondary>(builder, bases, scalar_limbs_vec, max_bits))
        // }

    }

    impl<C: TwoChainCurve> Chip<C>
    where
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {
        pub const NUM_HASH_BITS: usize = NUM_HASH_BITS;

        pub fn new(_: OptimizedPoseidonSpec<C::Scalar, T, RATE>, chip: Chip<C>) -> Self {
            chip
        }

        pub fn hash_cyclefold_inputs<Comm: AsRef<C>>(
            spec: &OptimizedPoseidonSpec<C::Base, T, RATE>,
            vp_digest: C::Scalar,
            r_le_bits: Vec<C::Scalar>,
            primary_nark_witness_comm: Vec<Comm>,
            cross_term_comms: Vec<Comm>,
            acc: &ProtostarAccumulatorInstance<C::Scalar, Comm>,
            acc_prime: &ProtostarAccumulatorInstance<C::Scalar, Comm>,
        ) -> C::Base {
            // let fe_to_limbs = |fe| fe_to_limbs(fe, NUM_LIMB_BITS);
            let mut poseidon = PoseidonHash::from_spec(spec.clone());
            let inputs = iter::empty()
                //.chain([vp_digest]) // flat_map(fe_to_limbs)
                .chain([fe_to_fe(fe_from_bits_le(r_le_bits))])
                .chain(
                    primary_nark_witness_comm
                        .iter()
                        .map(AsRef::as_ref)
                        .flat_map(into_coordinates),
                )
                .chain(
                    cross_term_comms
                        .iter()
                        .map(AsRef::as_ref)
                        .flat_map(into_coordinates),
                )
                .chain(
                    acc.witness_comms
                        .iter()
                        .map(AsRef::as_ref)
                        .flat_map(into_coordinates),
                )
                .chain(into_coordinates(acc.e_comm.as_ref()).into_iter())
                // .chain(
                //     acc_prime.witness_comms
                //         .iter()
                //         .map(AsRef::as_ref)
                //         .flat_map(into_coordinates),
                // )
                // .chain(into_coordinates(acc_prime.e_comm.as_ref()).into_iter())
                .collect_vec();
            poseidon.update(inputs.as_slice());
            fe_truncated(poseidon.squeeze(), NUM_HASH_BITS)
        }

        pub fn hash_state<Comm: AsRef<C>>(
            spec: &OptimizedPoseidonSpec<C::Scalar, T, RATE>,
            vp_digest: C::Scalar,
            step_idx: usize,
            initial_input: &[C::Scalar],
            output: &[C::Scalar],
            acc: &ProtostarAccumulatorInstance<C::Scalar, Comm>,
        ) -> C::Scalar {
            let mut poseidon = PoseidonHash::from_spec(spec.clone());
            let fe_to_limbs = |fe| fe_to_limbs(fe, NUM_LIMB_BITS_PRIMARY_NON_NATIVE, NUM_LIMBS_PRIMARY_NON_NATIVE);
            let inputs = iter::empty()
                .chain([vp_digest, C::Scalar::from(step_idx as u64)])
                .chain(initial_input.iter().copied())
                .chain(output.iter().copied())
                .chain([acc.instances[0][0]])
                .chain(
                    acc.witness_comms
                        .iter()
                        .map(AsRef::as_ref)
                        .flat_map(into_coordinates).into_iter().map(fe_to_limbs).flatten(),
                )
                .chain(acc.challenges.iter().copied())
                .chain([acc.u])
                .chain(into_coordinates(acc.e_comm.as_ref()).into_iter().map(fe_to_limbs).flatten())
                .chain(acc.compressed_e_sum.into_iter())
                .collect_vec();
            poseidon.update(&inputs);
            fe_truncated(poseidon.squeeze(), NUM_HASH_BITS)
        }

        // pub fn hash_state_acc_prime<Comm: AsRef<C>>(
        //     spec: &OptimizedPoseidonSpec<C::Scalar, T, RATE>,
        //     vp_digest: C::Scalar,
        //     acc_prime: &ProtostarAccumulatorInstance<C::Base, Comm>,
        // ) -> C::Scalar {
        //     let mut poseidon = PoseidonHash::from_spec(spec.clone());
        //     let fe_to_limbs = |fe| fe_to_limbs(fe, NUM_LIMB_BITS);
        //     let inputs = iter::empty()
        //     // todo maybe dont need vpdigest
        //         .chain(iter::once(vp_digest))
        //         .chain(fe_to_limbs(acc_prime.instances[0][0]))
        //         .chain(fe_to_limbs(acc_prime.instances[0][1]))
        //         .chain(
        //             acc_prime.witness_comms
        //                 .iter()
        //                 .map(AsRef::as_ref)
        //                 .flat_map(into_coordinates),
        //         )
        //         .chain(acc_prime.challenges.iter().copied().flat_map(fe_to_limbs))
        //         .chain(fe_to_limbs(acc_prime.u))
        //         .chain(into_coordinates(acc_prime.e_comm.as_ref()))
        //         .chain(acc_prime.compressed_e_sum.map(fe_to_limbs).into_iter().flatten())
        //         .collect_vec();
        //     poseidon.update(inputs.as_slice());
        //     fe_truncated(poseidon.squeeze(), NUM_HASH_BITS)
        // }

        pub fn hash_assigned_state(
            &self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            vp_digest: &AssignedValue<C::Scalar>,
            step_idx: &AssignedValue<C::Scalar>,
            initial_input: &[AssignedValue<C::Scalar>],
            output: &[AssignedValue<C::Scalar>],
            acc: &AssignedProtostarAccumulatorInstance<
                AssignedValue<C::Scalar>,
                EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
            >,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            let inputs = iter::empty()
                .chain([vp_digest, step_idx])
                .chain(initial_input)
                .chain(output)
                .chain([&acc.instances[0][0]])
                .chain(
                    acc.witness_comms
                        .iter()
                        .flat_map(|point| vec![point.x(), point.y()].into_iter().map(ProperCrtUint::limbs).flatten()),
                )
                .chain(acc.challenges.iter())
                .chain([&acc.u])
                .chain(vec![acc.e_comm.x(), acc.e_comm.y()].into_iter().map(ProperCrtUint::limbs).flatten())
                .chain(
                    acc.compressed_e_sum
                        .as_ref()
                        .into_iter())
                .copied()
                .collect_vec();
            let mut poseidon_chip = PoseidonSponge::<C::Scalar, T, RATE>::new::<R_F, R_P, SECURE_MDS>(builder.main());
            poseidon_chip.update(&inputs);
            let hash = poseidon_chip.squeeze(builder.main(), &self.gate_chip);
            // change to strict
            let hash_le_bits = self.gate_chip.num_to_bits(builder.main(), hash, RANGE_BITS);
            Ok(self.gate_chip.bits_to_num(builder.main(), &hash_le_bits[..NUM_HASH_BITS]))
        }

        // pub fn hash_assigned_acc_prime(
        //     &self,
        //     builder: &mut SinglePhaseCoreManager<C::Scalar>,
        //     vp_digest: &AssignedValue<C::Scalar>,
        //     acc_prime: &AssignedProtostarAccumulatorInstance<
        //         ProperCrtUint<C::Scalar>,
        //         EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
        //     >,
        // ) -> Result<AssignedValue<C::Scalar>, Error> {
        //     let inputs = iter::empty()
        //         .chain([vp_digest])
        //         .chain(acc_prime.instances[0][0].limbs().iter())
        //         .chain(acc_prime.instances[0][1].limbs().iter())
        //         .chain(
        //             acc_prime.witness_comms
        //                 .iter()
        //                 .flat_map(|point| vec![point.x(), point.y()].into_iter()),
        //         )
        //         .chain(acc_prime.challenges.iter().flat_map(ProperCrtUint::limbs))
        //         .chain(acc_prime.u.limbs())
        //         .chain(vec![acc_prime.e_comm.x(), acc_prime.e_comm.y()].into_iter())
        //         .chain(
        //             acc_prime.compressed_e_sum
        //                 .as_ref()
        //                 .map(ProperCrtUint::limbs)
        //                 .into_iter()
        //                 .flatten(),
        //         )
        //         .copied()
        //         .collect_vec();
        //     let mut poseidon_chip = PoseidonSponge::<C::Scalar, T, RATE>::new::<R_F, R_P, SECURE_MDS>(builder.main());
        //     poseidon_chip.update(&inputs);
        //     let hash = poseidon_chip.squeeze(builder.main(), &self.gate_chip);
        //     // change to strict
        //     let hash_le_bits = self.gate_chip.num_to_bits(builder.main(), hash, RANGE_BITS);
        //     Ok(self.gate_chip.bits_to_num(builder.main(), &hash_le_bits[..NUM_HASH_BITS]))
        // }

    }

    pub struct PoseidonNativeTranscriptChip<C: TwoChainCurve> 
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,
    {
        poseidon_chip: PoseidonSponge<C::Scalar, T, RATE>,
        chip: Chip<C>,
        proof: Value<Cursor<Vec<u8>>>,
    }

    #[derive(Clone)]
    pub struct NativeChallenge<F: BigPrimeField> {
        pub challenge_le_bits: Vec<AssignedValue<F>>,
        pub challenge: AssignedValue<F>,
    }

    impl<F: BigPrimeField> AsRef<AssignedValue<F>> for NativeChallenge<F> {
        fn as_ref(&self) -> &AssignedValue<F> {
            &self.challenge
        }
    }

    impl<C: TwoChainCurve> PoseidonNativeTranscriptChip<C>
    where
        C: TwoChainCurve,
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {

        pub fn new(ctx: &mut Context<C::Scalar>, spec: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
            chip: Chip<C>, proof: Value<Vec<u8>>) -> Self {
            let poseidon_chip = PoseidonSponge::from_spec(ctx, spec);
            PoseidonNativeTranscriptChip {
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
            r: &NativeChallenge<C::Scalar>,
        ) -> Result<Vec<AssignedValue<C::Scalar>>, Error> {
            Ok(r.challenge_le_bits.clone())
        }

        pub fn common_field_element(
            &mut self,
            value: &AssignedValue<C::Scalar>,
        ) -> Result<(), Error> {
            self.poseidon_chip.update(&[*value]);
            Ok(())
        }

        pub fn common_commitment(
            &mut self,
            value: &EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
        ) -> Result<(), Error> {
            [value.x(), value.y()].iter().filter_map(|&opt| Some(opt))
            .for_each(|v| v.limbs().iter()
            .for_each(|&limb| self.poseidon_chip.update(&[limb])));
            Ok(())
        }

        // pub fn common_commitment(
        //     &mut self,
        //     value: &EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
        // ) -> Result<(), Error> {
        //     [value.x(), value.y()].iter().filter_map(|&opt| Some(opt))
        //     .for_each(|v| self.poseidon_chip.update(&[*v.native()]));
        //     Ok(())
        // }

        pub fn read_field_element(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
        ) -> Result<AssignedValue<C::Scalar>, Error> {
            let fe = self.proof.as_mut().and_then(|proof| {
                let mut repr = <C::Scalar as PrimeField>::Repr::default();
                if proof.read_exact(repr.as_mut()).is_err() {
                    return Value::unknown();
                }
                C::Scalar::from_repr_vartime(repr)
                    .map(Value::known)
                    .unwrap_or_else(Value::unknown)
            });
            let fe = self.chip.assign_witness(builder, fe.assign().unwrap_or_default())?;
            self.common_field_element(&fe)?;
            Ok(fe)
        }

        pub fn read_commitment(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
        ) -> Result<EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>, Error> {
            let comm = self.proof.as_mut().and_then(|proof| {
                let mut reprs = [<C::Base as PrimeField>::Repr::default(); 2];
                for repr in &mut reprs {
                    if proof.read_exact(repr.as_mut()).is_err() {
                        return Value::unknown();
                    }
                }
                let [x, y] = reprs.map(|repr| {
                    C::Base::from_repr_vartime(repr)
                        .map(Value::known)
                        .unwrap_or_else(Value::unknown)
                });
                x.zip(y).and_then(|(x, y)| {
                    Option::from(C::from_xy(x, y))
                        .map(Value::known)
                        .unwrap_or_else(Value::unknown)
                })
            });
            let comm = self.chip.assign_witness_primary_non_native(builder, comm.assign().unwrap_or_default())?;
            self.common_commitment(&comm)?;
            Ok(comm)
        }

        pub fn squeeze_challenges(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            n: usize,
        ) -> Result<Vec<NativeChallenge<C::Scalar>>, Error> {
            (0..n).map(|_| self.squeeze_challenge(builder)).collect()
        }
    
        pub fn common_field_elements(
            &mut self,
            fes: &[AssignedValue<C::Scalar>],
        ) -> Result<(), Error> {
            fes.iter().try_for_each(|fe| self.common_field_element(fe))
        }
    
        pub fn read_field_elements(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            n: usize,
        ) -> Result<Vec<AssignedValue<C::Scalar>>, Error> {
            (0..n).map(|_| self.read_field_element(builder)).collect()
        }
    
        pub fn common_commitments(
            &mut self,
            comms: &[EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>],
        ) -> Result<(), Error> {
            comms
                .iter()
                .try_for_each(|comm| self.common_commitment(comm))
        }
    
        pub fn read_commitments(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
            n: usize,
        ) -> Result<Vec<EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>>, Error> {
            (0..n).map(|_| self.read_commitment(builder)).collect()
        }
    
        pub fn absorb_accumulator(
            &mut self,
            acc: &AssignedProtostarAccumulatorInstance<
                AssignedValue<C::Scalar>,
                EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>,
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
        
        pub fn squeeze_challenge(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
        ) -> Result<NativeChallenge<C::Scalar>, Error> {
            let range_chip = &self.chip.range_chip;
            let hash = self.poseidon_chip.squeeze(builder.main(), &range_chip.gate);
            self.poseidon_chip.update(&[hash]);
            // todo change this to num_to_bits_strict and use as r_le_bits in the verifier
            let challenge_le_bits = range_chip.gate.num_to_bits(builder.main(),hash, RANGE_BITS).into_iter().take(NUM_CHALLENGE_BITS).collect_vec();
            let challenge = range_chip.gate.bits_to_num(builder.main(), &challenge_le_bits);                            

            Ok(NativeChallenge {
                challenge_le_bits,
                challenge,
            })
        }
    }

    fn native_transcript_test<AT1>()
    where
        AT1: TranscriptRead<<Gemini<UnivariateKzg<Bn256>> as PolynomialCommitmentScheme<bn256::Fr>>::CommitmentChunk, bn256::Fr>
        + TranscriptWrite<<Gemini<UnivariateKzg<Bn256>> as PolynomialCommitmentScheme<bn256::Fr>>::CommitmentChunk, bn256::Fr>
        + InMemoryTranscript<Param = OptimizedPoseidonSpec<bn256::Fr, T, RATE>>,
     {
        let circuit_builder = RefCell::new(BaseCircuitBuilder::<bn256::Fr>::from_stage(CircuitBuilderStage::Mock).use_k(10).use_lookup_bits(9));
        let range_chip = circuit_builder.borrow().range_chip();
        let tcc_chip = Chip::<bn256::G1Affine>::create(range_chip);
        let mut binding = circuit_builder.borrow_mut();
        let builder = binding.pool(0);

        let spec = OptimizedPoseidonSpec::<bn256::Fr, T, RATE>::new::<R_F, R_P, SECURE_MDS>();
        let atp = strawman::accumulation_transcript_param();
        let mut native_transcript = AT1::new(atp);
        native_transcript.write_field_element(&bn256::Fr::zero()).unwrap();
        let native_challenge = native_transcript.squeeze_challenge();
        let proof = native_transcript.into_proof();
        // let instances = [&bn256::Fr::zero(), &bn256::Fr::zero()].map(Value::as_ref);  
        let circuit_transcript =
            &mut PoseidonNativeTranscriptChip::new(builder.main(), spec.clone(), tcc_chip.clone(), Value::known(proof));
        let fe = circuit_transcript.read_field_element(builder).unwrap();
        assert_eq!(*fe.value(), bn256::Fr::zero());

        let circuit_challenge = circuit_transcript.squeeze_challenge(builder).unwrap();
        assert_eq!(*circuit_challenge.as_ref().value(), native_challenge);

        // let fe = hash_chip.read_field_element(&mut builder).unwrap();
        // let comm = chip.read_commitment(&mut builder).unwrap();
        // let challenges = chip.squeeze_challenges(&mut builder, 2).unwrap();
        // let challenges = challenges.iter().map(|c| chip.challenge_to_le_bits(c).unwrap()).collect_vec();
        // let fes = chip.read_field_elements(&mut builder, 2).unwrap();
        // let comms = chip.read_commitments(&mut builder, 2).unwrap();
        // let acc = AssignedProtostarAccumulatorInstance {
        //     instances: [[fe, fe], [fe, fe]],
        //     witness_comms: [comm, comm],
        //     challenges: [fe, fe],
        //     u: fe,
        //     e_comm: comm,
        //     compressed_e_sum: Some(fe),
        // };
        // chip.absorb_accumulator(&acc).unwrap();
    }

    #[test]
    fn run_native_transcript_test() {
        native_transcript_test::<PoseidonNativeTranscript<_, _>>();
    }

    //#[derive(Clone, Debug)]
    pub struct PoseidonTranscriptChip<C: TwoChainCurve> 
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,
    {
        poseidon_chip: PoseidonSponge<C::Scalar, T, RATE>,
        chip: Chip<C>,
        proof: Value<Cursor<Vec<u8>>>,
    }

    #[derive(Clone)]
    pub struct Challenge<F: BigPrimeField> {
        pub le_bits: Vec<AssignedValue<F>>,
        pub scalar: ProperCrtUint<F>,
    }

    impl<F: BigPrimeField> AsRef<ProperCrtUint<F>> for Challenge<F> {
        fn as_ref(&self) -> &ProperCrtUint<F> {
            &self.scalar
        }
    }

    impl<C: TwoChainCurve> PoseidonTranscriptChip<C>
    where
        C: TwoChainCurve,
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {

        pub fn new(ctx: &mut Context<C::Scalar>, spec: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
            chip: Chip<C>, proof: Value<Vec<u8>>) -> Self {
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
            Ok(challenge.le_bits.clone())
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
            (0..n).map(|_| self.read_commitment(builder)).collect()
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
        
        pub fn squeeze_challenge(
            &mut self,
            builder: &mut SinglePhaseCoreManager<C::Scalar>,
        ) -> Result<Challenge<C::Scalar>, Error> {
            let range_chip = &self.chip.range_chip;
            let (challenge_le_bits, challenge) = {
                let hash = self.poseidon_chip.squeeze(builder.main(), &range_chip.gate);
                self.poseidon_chip.update(&[hash]);
                // todo change this to num_to_bits_strict and use as r_le_bits in the verifier
                let challenge_le_bits = range_chip.gate.num_to_bits(builder.main(),hash, RANGE_BITS).into_iter().take(NUM_CHALLENGE_BITS).collect_vec();
                let challenge = range_chip.gate.bits_to_num(builder.main(), &challenge_le_bits);
                (challenge_le_bits, challenge)
            };

            let scalar = self.chip.assign_witness_base(builder, fe_to_fe(challenge.value().clone()))?;
            let scalar_in_base = scalar.native();
            self.chip.constrain_equal(builder, &challenge, scalar_in_base).unwrap();                                       

            Ok(Challenge {
                le_bits: challenge_le_bits,
                scalar: scalar,
            })
        }
    }
}