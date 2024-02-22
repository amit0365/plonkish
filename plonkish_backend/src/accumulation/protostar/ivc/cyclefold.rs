use halo2_base::{halo2_proofs::
    {plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance}, 
    dev::MockProver, 
    arithmetic::Field,
    halo2curves::group::{prime::PrimeCurveAffine, Curve, Group},
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value}}, 
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
    gates::{circuit::{builder::{BaseCircuitBuilder, self}, BaseCircuitParams, CircuitBuilderStage, BaseConfig}, GateInstructions, flex_gate::threads::SinglePhaseCoreManager}, AssignedValue, poseidon::hasher::{spec::OptimizedPoseidonSpec, PoseidonSponge, PoseidonHash}};
use halo2_ecc::{ecc::EcPoint, bigint::ProperCrtUint};
use halo2_gadgets::poseidon::primitives::{ConstantLength, Spec, Hash as inlineHash};
use itertools::Itertools;
use core::{borrow::Borrow, marker::PhantomData};
use std::{iter, time::Instant, cell::RefCell};
use super::halo2::{chips::{poseidon::{hash_chip::{PoseidonChip, PoseidonConfig}, spec::PoseidonSpec}, scalar_mul::ec_chip::{ScalarMulChip, ScalarMulChipConfig, ScalarMulChipInputs}, T, R, L}, test::strawman::{self, RANGE_BITS, NUM_CHALLENGE_BITS, NUM_LIMBS, NUM_LIMB_BITS, R_F, R_P, SECURE_MDS, NUM_HASH_BITS}};
use super::halo2::test::strawman::{Chip, PoseidonTranscriptChip, fe_to_limbs, into_coordinates};
use ivc::ProtostarAccumulationVerifierParam;
use crate::{util::{
    end_timer, 
    transcript::{TranscriptRead, TranscriptWrite},
    arithmetic::{PrimeFieldBits, CurveAffine, TwoChainCurve, fe_to_fe, fe_from_bits_le, fe_to_bits_le, fe_truncated}, izip_eq, start_timer}, 
    accumulation::{PlonkishNarkInstance, protostar::{ProtostarAccumulatorInstance, ivc::{self, halo2::chips::scalar_mul::ec_chip::ScalarMulConfigInputs}, ProtostarStrategy::{Compressing, NoCompressing}}}, frontend::halo2::CircuitExt, backend::PlonkishCircuit, poly::multilinear::MultilinearPolynomial};
use rand::RngCore;

pub const NUM_ADVICE: usize = 5;
pub const NUM_FIXED: usize = 1;

// public inputs length for the CycleFoldInputs for compressing 
pub const CF_IO_LEN: usize = 1;

pub type AssignedCycleFoldInputs<Assigned, AssignedSecondary> =
    CycleFoldInputs<Assigned, AssignedSecondary>;

#[derive(Debug, Clone)]
pub struct CycleFoldInputs<F, C> 
{   
    pub r_le_bits: Vec<F>,
    pub r: F,
    pub nark_witness_comms: Vec<C>,
    pub cross_term_comms: Vec<C>,
    pub acc_witness_comms: Vec<C>,
    pub acc_e_comm: C,
    pub acc_prime_witness_comms: Vec<C>,
    pub acc_prime_e_comm: C,
}

#[derive(Clone)]
pub struct CycleFoldConfig<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    // poseidon: PoseidonConfig<C, T, R, L>,
    // advice: Column<Advice>,
    scalar_mul: ScalarMulChipConfig<C>,
    instance: Column<Instance>,
}

#[derive(Debug, Clone)]
pub struct CycleFoldCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub primary_avp: ProtostarAccumulationVerifierParam<C::Scalar>,
    // pub cyclefold_avp: Option<ProtostarAccumulationVerifierParam<C::Scalar>>,
    pub hash_config: PoseidonSpec,
    pub inputs: CycleFoldInputs<C::Scalar, C::Secondary>,
}

impl<C> CycleFoldCircuit<C> 
where
    C: TwoChainCurve, 
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{

    pub const R_LE_BITS: [C::Scalar; NUM_CHALLENGE_BITS] = [C::Scalar::ZERO; NUM_CHALLENGE_BITS];

    pub fn new(
        primary_avp: Option<ProtostarAccumulationVerifierParam<C::Scalar>>,
    ) -> Self 
    {
        let primary_avp = primary_avp.unwrap_or_default();
        let hash_config = PoseidonSpec;

        let num_witness_comm = primary_avp.num_folding_witness_polys();
        let num_cross_comms = match primary_avp.strategy {
            NoCompressing => primary_avp.num_cross_terms,
            Compressing => 1
        };

        let bytes: &[u8] = &[44, 74, 155, 202, 230, 209, 105, 242, 77, 222, 213, 71, 58, 97, 34, 113, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let inputs = 
            CycleFoldInputs::<C::Scalar, C::Secondary>{
                r_le_bits: fe_to_bits_le(C::Scalar::from_bytes_le(bytes)).into_iter().take(NUM_CHALLENGE_BITS).collect_vec(), // Self::R_LE_BITS.to_vec(),
                r: C::Scalar::from_bytes_le(bytes),
                nark_witness_comms: vec![C::Secondary::identity(); num_witness_comm],
                cross_term_comms: vec![C::Secondary::identity(); num_cross_comms],
                acc_witness_comms: vec![C::Secondary::identity(); num_witness_comm],
                acc_e_comm: C::Secondary::identity(),
                acc_prime_witness_comms: vec![C::Secondary::identity(); num_witness_comm],
                acc_prime_e_comm: C::Secondary::identity(),
            };

        Self {
            primary_avp: primary_avp.clone(),
            //cyclefold_avp: None,
            hash_config,
            inputs,
        }
    }

    pub fn init(&mut self, vp_digest: C::Scalar) {
        // assert_eq!(&self.cyclefold_avp.unwrap().num_instances, &[CF_IO_LEN]);
        self.primary_avp.vp_digest = vp_digest;
    }

    pub fn update_cyclefold_inputs<Comm: AsRef<C::Secondary>>(
        &mut self,
        r_le_bits: Vec<C::Base>,
        r: C::Base,
        cross_term_comms: Vec<Comm>,
        primary_nark: ProtostarAccumulatorInstance<C::Base, Comm>,
        acc: ProtostarAccumulatorInstance<C::Base, Comm>,
        acc_prime: ProtostarAccumulatorInstance<C::Base, Comm>,
    ) {
        let convert_vec_comms = |comms: &[Comm]| comms.iter().map(AsRef::as_ref).cloned().collect_vec();
        self.inputs = CycleFoldInputs::<C::Scalar, C::Secondary> {
            r_le_bits: r_le_bits.into_iter().map(fe_to_fe).collect::<Vec<_>>(),
            r: fe_to_fe(r),
            nark_witness_comms: convert_vec_comms(&primary_nark.witness_comms),
            cross_term_comms: convert_vec_comms(&cross_term_comms),
            acc_witness_comms: convert_vec_comms(&acc.witness_comms),
            acc_e_comm: *acc.e_comm.as_ref(),
            acc_prime_witness_comms: convert_vec_comms(&acc_prime.witness_comms),
            acc_prime_e_comm: *acc_prime.e_comm.as_ref(),
        };
    }

    pub fn sm_chip_inputs(
        &self,
        cf_inputs: &CycleFoldInputs<C::Scalar, C::Secondary>
    ) -> Result<Vec<ScalarMulChipInputs<C::Scalar, C::Secondary>>, Error> {

        let mut sm_inputs = Vec::new();
        for i in 0..cf_inputs.nark_witness_comms.len() + 1 {

            let nark_comm;
            let acc_comm;
            let acc_prime_comm;

            if i == cf_inputs.nark_witness_comms.len() {
                nark_comm = cf_inputs.cross_term_comms[0];
                acc_comm = cf_inputs.acc_e_comm;
                acc_prime_comm = cf_inputs.acc_prime_e_comm;
            } else {
                nark_comm = cf_inputs.nark_witness_comms[i];
                acc_comm = cf_inputs.acc_witness_comms[i];
                acc_prime_comm = cf_inputs.acc_prime_witness_comms[i];
            }

            let input = ScalarMulChipInputs::<C::Scalar, C::Secondary> {
                r_le_bits: cf_inputs.r_le_bits.clone(),
                r: cf_inputs.r,
                nark_comm,
                acc_comm,
                acc_prime_comm,
            };

            sm_inputs.push(input);
        }

        Ok(sm_inputs)
    }

    pub fn sm_config_inputs(
        &self,
        sm_inputs: &Vec<ScalarMulChipInputs<C::Scalar, C::Secondary>>
    ) -> Result<Vec<ScalarMulConfigInputs<C>>, Error> {

        let vec_len: usize = 129;
        let mut sm_config_inputs = Vec::new();
        for inputs in sm_inputs{
            let mut nark_x_vec = Vec::new();
            let mut nark_y_vec = Vec::new();
            let mut rnark_x_vec = Vec::new();
            let mut rnark_y_vec = Vec::new();

            let one = C::Scalar::ONE;
            let zero = C::Scalar::ZERO;
            let r_le_bits = &inputs.r_le_bits;
            let r_le_bits_value = r_le_bits.iter().map(|fe| Value::known(*fe)).collect_vec();
            let r_window_bits = r_le_bits[1..].chunks(2).collect_vec();

            // push last element as the first rbit
            let mut rbits_vec = Vec::new();
            rbits_vec = r_le_bits_value.clone();
            rbits_vec.push(r_le_bits_value[0]);

            let p_zero = C::Secondary::identity();
            let mut p = inputs.nark_comm; 
            let acc = inputs.acc_comm;
            let r = inputs.r;
            let p_single = p;
            
            // initial assumption: rbits[0] = 1
            let p_single_x = into_coordinates(&p_single)[0];
            let p_single_y = into_coordinates(&p_single)[1];
            nark_x_vec.push(Value::known(p_single_x));
            nark_y_vec.push(Value::known(p_single_y));
            rnark_x_vec.push(Value::known(p_single_x));
            rnark_y_vec.push(Value::known(p_single_y)); 

            for idx in (1..vec_len-2).step_by(2) {
                p = <C::Secondary as CurveAffine>::CurveExt::double(&p.into()).into(); 
                nark_x_vec.push(Value::known(into_coordinates(&p)[0]));
                nark_y_vec.push(Value::known(into_coordinates(&p)[1]));
                let p_single = p;

                p = <C::Secondary as CurveAffine>::CurveExt::double(&p.into()).into();
                nark_x_vec.push(Value::known(into_coordinates(&p)[0]));
                nark_y_vec.push(Value::known(into_coordinates(&p)[1])); 

                let p_triple = (p + p_single).to_affine();
                rnark_x_vec.push(Value::known(into_coordinates(&p_triple)[0]));
                rnark_y_vec.push(Value::known(into_coordinates(&p_triple)[0])); 

                let acc_sel = match r_window_bits[idx/2] {
                    [z, o] if *z == zero && *o == zero => p_zero,    // 00
                    [z, o] if *z == one && *o == zero => p_single,   // 10
                    [z, o] if *z == zero && *o == one => p,          // 01
                    [z, o] if *z == one && *o == one => p_triple,    // 11
                    _ => panic!("Invalid window"),
                };

                let acc_prev = C::Secondary::from_xy(rnark_x_vec[idx-1].assign().unwrap(), rnark_y_vec[idx-1].assign().unwrap()).unwrap();
                let acc_next = (acc_prev + acc_sel).to_affine();

                rnark_x_vec.push(Value::known(into_coordinates(&acc_next)[0]));
                rnark_y_vec.push(Value::known(into_coordinates(&acc_next)[1]));

            }

            // push last rbit 
            p = <C::Secondary as CurveAffine>::CurveExt::double(&p.into()).into(); 
            nark_x_vec.push(Value::known(into_coordinates(&p)[0]));
            nark_y_vec.push(Value::known(into_coordinates(&p)[1]));

            if r_le_bits[vec_len-2] == one {
                let acc_prev = C::Secondary::from_xy(rnark_x_vec[vec_len-3].assign().unwrap(), rnark_y_vec[vec_len-3].assign().unwrap()).unwrap();
                let acc_next = (acc_prev + p).to_affine();
                rnark_x_vec.push(Value::known(into_coordinates(&acc_next)[0]));
                rnark_y_vec.push(Value::known(into_coordinates(&acc_next)[1]));
            } else {
                rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-3].assign().unwrap()));
                rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-3].assign().unwrap()));
            }

            // push last element as the first rbit
            nark_x_vec.push(Value::known(into_coordinates(&p_single)[0]));
            nark_y_vec.push(Value::known(into_coordinates(&p_single)[1]));

            // correct initial assumption
            if r_le_bits[0] == one {
                rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-2].assign().unwrap()));
                rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-2].assign().unwrap()));
            } else {
                let acc_prev = C::Secondary::from_xy(rnark_x_vec[vec_len-2].assign().unwrap(), rnark_y_vec[vec_len-2].assign().unwrap()).unwrap();
                let acc_next = (acc_prev - p_single).to_affine();
                rnark_x_vec.push(Value::known(into_coordinates(&acc_next)[0]));
                rnark_y_vec.push(Value::known(into_coordinates(&acc_next)[1]));
            }
            let r_non_native: C::Base = fe_to_fe(r);
            let scalar_mul_given= (p_single * r_non_native).to_affine();
            let scalar_mul_calc = C::Secondary::from_xy(rnark_x_vec[vec_len-1].assign().unwrap(), rnark_y_vec[vec_len-1].assign().unwrap()).unwrap();
            let acc_prime_calc  = (scalar_mul_calc + acc).to_affine();
            let acc_prime_given = inputs.acc_prime_comm; 
            assert_eq!(acc_prime_calc, acc_prime_given);
            assert_eq!(scalar_mul_given, scalar_mul_calc);

            let inputs =
                ScalarMulConfigInputs::<C> { 
                    rbits_vec, r: Value::known(r), nark_x_vec, nark_y_vec, rnark_x_vec, rnark_y_vec, 
                    acc_x: Value::known(into_coordinates(&acc)[0]), 
                    acc_y: Value::known(into_coordinates(&acc)[1]), 
                    acc_prime_calc_x: Value::known(into_coordinates(&acc_prime_calc)[0]), 
                    acc_prime_calc_y: Value::known(into_coordinates(&acc_prime_calc)[1]), 
                    acc_prime_given_x: Value::known(into_coordinates(&acc_prime_given)[0]), 
                    acc_prime_given_y: Value::known(into_coordinates(&acc_prime_given)[1])
                };

            sm_config_inputs.push(inputs);
        }

        Ok(sm_config_inputs)
    }

    pub fn hash_inputs(
        &self,
        inputs: &CycleFoldInputs<C::Scalar, C::Secondary>
    ) -> C::Scalar {
        let witness_comm =
            inputs.nark_witness_comms.clone().into_iter()
            .zip(inputs.acc_witness_comms.clone().into_iter())
            .flat_map(|(a, b)| vec![a, b])
            .collect_vec();

        let inputs_vec = iter::empty()
            .chain([C::Scalar::ONE])
            //.chain([vp_digest]).flat_map(fe_to_limbs)
            // .chain([fe_from_bits_le(inputs.r_le_bits.clone())])
            // .chain(
            //     witness_comm
            //         .iter()
            //         .flat_map(into_coordinates))  
            // .chain(
            //     inputs.cross_term_comms
            //         .iter()
            //         .flat_map(into_coordinates))
            // .chain(into_coordinates(&inputs.acc_e_comm).into_iter())                     
            .collect_vec();

        let message: [C::Scalar; L] =
        match inputs_vec.try_into() {
            Ok(arr) => arr,
            Err(_) => panic!("Failed to convert Vec to Array"),
        };
        assert_eq!(L, message.len());

        let hash = inlineHash::<C::Scalar, PoseidonSpec, ConstantLength<L>, 5, 4>::init().hash(message);
        let hash_truncated = fe_truncated(hash, NUM_HASH_BITS);
        println!("hash_truncated: {:?}", hash_truncated);
        println!("hash: {:?}", hash);
        // hash_truncated
        hash

    }
}

impl<C> Circuit<C::Scalar> for CycleFoldCircuit<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    type Params = ();
    type Config = CycleFoldConfig<C>; 
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        
        let advices = [0; 6].map(|_| meta.advice_column());
        let constants = [0; 10].map(|_| meta.fixed_column());
        meta.enable_constant(constants[5]);

        for col in &advices {
            meta.enable_equality(*col);
        }

        for col in &constants {
            meta.enable_equality(*col);
        }

        let instance = meta.instance_column();
        meta.enable_equality(instance);

        // let poseidon = 
        //     PoseidonChip::<C, PoseidonSpec, T, R, L>::configure(
        //         meta,
        //         advices[..5].try_into().unwrap(),
        //         advices[5],
        //         constants[..5].try_into().unwrap(), 
        //         constants[5..].try_into().unwrap(), 
        //     );

        let scalar_mul = ScalarMulChipConfig::<C>::configure(meta, advices[..NUM_ADVICE].try_into().unwrap());

        Self::Config {
            // poseidon,
            //advice: advices[0],
            scalar_mul,
            instance,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {

        let mut hash_inputs = Vec::new();
        // let hash_chip = PoseidonChip::<C, PoseidonSpec, 5, 4, L>::construct(
        //     config.poseidon,
        // );

        let sm_chip_inputs = self.sm_chip_inputs(&self.inputs)?;
        let sm_config_inputs = self.sm_config_inputs(&sm_chip_inputs)?;

        for i in 0..sm_config_inputs.len() {
            if i == 0 {
                hash_inputs.extend_from_slice(&config.scalar_mul.assign(layouter.namespace(|| "ScalarMulChip"), sm_config_inputs[i].clone(), 1)?);
            } else {
                // hash_inputs.extend_from_slice(&config.scalar_mul.assign(layouter.namespace(|| "ScalarMulChip"), sm_config_inputs[i].clone(), 1)?[1..]);
            }
        }
        
        //layouter.constrain_instance(hash_inputs[0].cell(), config.instance, 0)?;

            // hash_inputs.push(layouter.assign_region(
            //     || "load message",
            //     |mut region| {
            //         region.assign_advice(
            //             || "value",
            //             config.advice,
            //             0,
            //             || Value::known(C::Scalar::ONE),
            //         )
            //     },
            // )?);

        // let message: [AssignedCell<C::Scalar, C::Scalar>; L] =
        // match hash_inputs.try_into() {
        //     Ok(arr) => arr,
        //     Err(_) => panic!("Failed to convert Vec to Array"),
        // };

        // let hash = hash_chip.hash(
        //     layouter.namespace(|| "perform poseidon hash"),
        //     message,
        // )?;
        // println!("hash_circuit: {:?}", hash);
        // layouter.constrain_instance(hash.cell(), config.instance, 0)?;

        Ok(())
    }
}

impl<C> CircuitExt<C::Scalar> for CycleFoldCircuit<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{   
    fn instances(&self) -> Vec<Vec<C::Scalar>> {
        let mut instances = vec![vec![C::Scalar::ZERO; CF_IO_LEN]];
        let inputs = &self.inputs;
        instances[0][0] = self.hash_inputs(inputs);
        instances
    }

    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}
