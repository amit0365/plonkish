pub mod native;
pub mod nonnative;

use std::io::{self, Cursor};

use halo2_base::utils::{PrimeField, ScalarField};
//use halo2_gadgets::poseidon::{spec::PoseidonSpec, PoseidonHash};
use poseidon::{Spec as PoseidonSpec, Poseidon as PoseidonHash};
use halo2_proofs::arithmetic::CurveAffine;

use crate::{accumulation::protostar::ivc::halo2::ivc_circuits::primary::{R_F, R_P}, util::{arithmetic::{fe_from_le_bytes, fe_to_limbs, into_coordinates}, transcript::{FieldTranscript, FieldTranscriptRead, FieldTranscriptWrite, InMemoryTranscript, Transcript, TranscriptRead, TranscriptWrite}}};
use crate::accumulation::protostar::ivc::halo2::ivc_circuits::primary::{T, RATE};
pub const RANGE_BITS: usize = 254;
pub const NUM_CHALLENGE_BITS: usize = 128;
pub const NUM_CHALLENGE_BYTES: usize = NUM_CHALLENGE_BITS / 8;
pub const NUM_HASH_BITS: usize = 250;

pub const NUM_LIMBS: usize = 3;
pub const NUM_LIMB_BITS: usize = 88;

    pub fn accumulation_transcript_param<F: ScalarField>() -> PoseidonSpec<F, T, RATE> {
        PoseidonSpec::<F, T, RATE>::new(R_F, R_P)
    }

    pub fn decider_transcript_param<F: ScalarField>() -> PoseidonSpec<F, T, RATE> {
        PoseidonSpec::<F, T, RATE>::new(R_F, R_P)
    }

    #[derive(Clone)]
    pub struct PoseidonTranscript<F: ScalarField, S> {
        state: PoseidonHash<F, T, RATE>,
        stream: S,
    }

    impl<F: ScalarField> InMemoryTranscript for PoseidonTranscript<F, Cursor<Vec<u8>>> {
        type Param = PoseidonSpec<F, T, RATE>;

        fn new(spec: Self::Param) -> Self {
            Self {
                state: PoseidonHash::new_with_spec(spec),
                stream: Default::default(),
            }
        }

        fn into_proof(self) -> Vec<u8> {
            self.stream.into_inner()
        }

        fn from_proof(spec: Self::Param, proof: &[u8]) -> Self {
            Self {
                state: PoseidonHash::new_with_spec(spec),
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
    
    #[derive(Clone)]
    pub struct PoseidonNativeTranscript<F: ScalarField, S> {
        state: PoseidonHash<F, T, RATE>,
        stream: S,
    }

    impl<F: ScalarField> InMemoryTranscript for PoseidonNativeTranscript<F, Cursor<Vec<u8>>> {
        type Param = PoseidonSpec<F, T, RATE>;

        fn new(spec: Self::Param) -> Self {
            Self {
                state: PoseidonHash::new_with_spec(spec),
                stream: Default::default(),
            }
        }

        fn into_proof(self) -> Vec<u8> {
            self.stream.into_inner()
        }

        fn from_proof(spec: Self::Param, proof: &[u8]) -> Self {
            Self {
                state: PoseidonHash::new_with_spec(spec),
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
            let coords = into_coordinates(ec_point);
            let limbs: Vec<_> = coords.iter()
                .flat_map(|&fe| fe_to_limbs(fe, NUM_LIMB_BITS, NUM_LIMBS))
                .collect();
            self.state.update(&limbs);            
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