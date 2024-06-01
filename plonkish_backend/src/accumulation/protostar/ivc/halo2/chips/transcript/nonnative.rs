use std::io::{Cursor, Read};
use halo2_base::{halo2_proofs::{circuit::{AssignedCell, Layouter, Value}, plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector}, poly::Rotation}, utils::{biguint_to_fe, decompose_biguint, fe_to_biguint, modulus, BigPrimeField, FromUniformBytes, PrimeField, ScalarField}};
use halo2_gadgets::poseidon::{spec::PoseidonSpec, PoseidonSpongeChip, Pow5Chip};
use halo2_proofs::{arithmetic::{CurveAffine, Field}, halo2curves::ff::PrimeFieldBits};
use num_bigint::BigUint;
use itertools::Itertools;
use crate::{accumulation::protostar::ivc::{halo2::{chips::main_chip::{EcPointNative, EcPointNonNative, MainChip, MainChipConfig, NonNativeNumber, Number}}, ProtostarAccumulationVerifierParam}, util::arithmetic::{fe_to_fe, TwoChainCurve}};
use crate::accumulation::protostar::ProtostarStrategy::{Compressing, NoCompressing};
use std::io::Write;
use super::native::AssignedProtostarAccumulatorInstance;
use crate::accumulation::protostar::ivc::halo2::ivc_circuits::primary::{T, RATE};

pub const RANGE_BITS: usize = 254;
pub const NUM_CHALLENGE_BITS: usize = 128;

#[derive(Clone)]
pub struct Challenge<F: BigPrimeField> {
    pub le_bits: Vec<Number<F>>,
    pub scalar: NonNativeNumber<F>,
}

impl<F: BigPrimeField> AsRef<NonNativeNumber<F>> for Challenge<F> {
    fn as_ref(&self) -> &NonNativeNumber<F> {
        &self.scalar
    }
}

#[derive(Clone)]
pub struct PoseidonTranscriptChip<C: TwoChainCurve> 
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    poseidon_chip: PoseidonSpongeChip<C::Scalar, T, RATE>,
    chip: MainChip<C>,
    proof: Value<Cursor<Vec<u8>>>,
}

impl<C: TwoChainCurve> PoseidonTranscriptChip<C>
where
    C: TwoChainCurve,
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{

    type Num = Number<C::Scalar>;

    pub fn new(layouter: &mut impl Layouter<C::Scalar>, pow5_chip: Pow5Chip<C::Scalar, T, RATE>, spec: PoseidonSpec,
        main_chip: MainChip<C>, proof: Value<Vec<u8>>) -> Self {
        let poseidon_chip = PoseidonSpongeChip::from_spec(pow5_chip, layouter.namespace(|| "poseidon_chip_nonnative"), spec);
        PoseidonTranscriptChip {
            poseidon_chip,
            chip: main_chip,
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
    ) -> Result<Vec<Self::Num>, Error> {
        Ok(challenge.le_bits.clone())
    }

    pub fn common_field_element(
        &mut self,
        value: &NonNativeNumber<C::Scalar>,
    ) -> Result<(), Error> {
        value.limbs.iter().for_each(|limb| self.poseidon_chip.update(&[limb.0.clone()]));
        Ok(())
    }

    pub fn common_commitment(
        &mut self,
        value: &EcPointNative<C>,
    ) -> Result<(), Error> {
        [value.x.clone(), value.y.clone()].iter().filter_map(|opt| Some(opt)).for_each(|v| self.poseidon_chip.update(&[v.0.clone()]));
        Ok(())
    }

    pub fn read_field_element(
        &mut self,
        layouter: &mut impl Layouter<C::Scalar>,
    ) -> Result<NonNativeNumber<C::Scalar>, Error> {
        let fe = self.proof.as_mut().and_then(|proof| {
            let mut repr = <C::Base as PrimeField>::Repr::default();
            if proof.read_exact(repr.as_mut()).is_err() {
                return Value::unknown();
            }
            C::Base::from_repr_vartime(repr)
                .map(Value::known)
                .unwrap_or_else(Value::unknown)
        });
        let fe = self.chip.assign_witness_base(layouter, fe.assign().unwrap_or_default())?;
        self.common_field_element(&fe)?;
        Ok(fe)
    }

    // not used in verifier circuit, only for testing
    pub fn write_field_element(
        &mut self, 
        layouter: &mut impl Layouter<C::Scalar>,
        fe: &C::Base
    ) -> Result<NonNativeNumber<C::Scalar>, Error> {
        let repr = fe.to_repr();
        self.proof.as_mut().map(|proof| {
                proof.write_all(repr.as_ref())
                    .map_err(|err| crate::Error::Transcript(err.kind(), err.to_string()))
            }).unwrap(); 

        let fe = self.chip.assign_witness_base(layouter, *fe)?;
        self.common_field_element(&fe)?;
        Ok(fe)

    }

    pub fn read_commitment(
        &mut self,
        layouter: &mut impl Layouter<C::Scalar>,
    ) -> Result<EcPointNative<C>, Error> {
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
        let comm = self.chip.assign_witness_secondary(layouter, comm.assign().unwrap_or_default())?;
        self.common_commitment(&comm)?;
        Ok(comm)
    }

    // not used in verifier circuit, only for testing
    pub fn write_commitment(
        &mut self, 
        layouter: &mut impl Layouter<C::Scalar>,
        ec_point: &C::Secondary
    ) -> Result<EcPointNative<C>, Error> {
        let coordinates = ec_point.coordinates().unwrap();
            for coordinate in [coordinates.x(), coordinates.y()] {
                    let repr = coordinate.to_repr();
                    self.proof.as_mut().map(|proof| {
                        proof.write_all(repr.as_ref())
                            .map_err(|err| crate::Error::Transcript(err.kind(), err.to_string()))
                    }).unwrap();
                }
        let comm = self.chip.assign_witness_secondary(layouter, *ec_point)?;
        self.common_commitment(&comm)?;

        Ok(comm)
    }

    pub fn squeeze_challenges(
        &mut self,
        layouter: &mut impl Layouter<C::Scalar>,
        n: usize,
    ) -> Result<Vec<Challenge<C::Scalar>>, Error> {
        (0..n).map(|_| self.squeeze_challenge(layouter)).collect()
    }

    pub fn common_field_elements(
        &mut self,
        fes: &[NonNativeNumber<C::Scalar>],
    ) -> Result<(), Error> {
        fes.iter().try_for_each(|fe| self.common_field_element(fe))
    }

    pub fn read_field_elements(
        &mut self,
        layouter: &mut impl Layouter<C::Scalar>,
        n: usize,
    ) -> Result<Vec<NonNativeNumber<C::Scalar>>, Error> {
        (0..n).map(|_| self.read_field_element(layouter)).collect()
    }

    pub fn common_commitments(
        &mut self,
        comms: &[EcPointNative<C>],
    ) -> Result<(), Error> {
        comms
            .iter()
            .try_for_each(|comm| self.common_commitment(comm))
    }

    pub fn read_commitments(
        &mut self,
        layouter: &mut impl Layouter<C::Scalar>,
        n: usize,
    ) -> Result<Vec<EcPointNative<C>>, Error> {
        (0..n).map(|_| self.read_commitment(layouter)).collect()
    }

    pub fn absorb_accumulator(
        &mut self,
        acc: &AssignedProtostarAccumulatorInstance<
            NonNativeNumber<C::Scalar>,
            EcPointNative<C>,
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
        layouter: &mut impl Layouter<C::Scalar>,
    ) -> Result<Challenge<C::Scalar>, Error> {

        let (challenge_le_bits, challenge) = {

            let hash = self.poseidon_chip.squeeze(layouter.namespace(|| "squeeze_poseidon"))?;
            self.poseidon_chip.update(&[hash.clone()]);
            // todo change this to num_to_bits_strict and use as r_le_bits in the verifier
            let challenge_le_bits = self.chip.num_to_bits(layouter, RANGE_BITS, &Number(hash))?.into_iter().take(NUM_CHALLENGE_BITS).collect_vec();
            let challenge = self.chip.bits_to_num(layouter, &challenge_le_bits)?;     
            
            (challenge_le_bits, challenge)
        };

        let scalar = self.chip.assign_witness_base(layouter, fe_to_fe(challenge.value()))?;
        let scalar_in_base = scalar.native();
        self.chip.constrain_equal(layouter, &challenge, scalar_in_base).unwrap();                                       

        Ok(Challenge {
            le_bits: challenge_le_bits,
            scalar,
        })
    }
}