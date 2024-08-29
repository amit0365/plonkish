use halo2_base::{gates::{circuit::{builder::{self, BaseCircuitBuilder}, BaseCircuitParams, BaseConfig, CircuitBuilderStage}, flex_gate::threads::SinglePhaseCoreManager, GateInstructions}, halo2_proofs::
    {arithmetic::Field, circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value}, dev::MockProver, halo2curves::group::{prime::PrimeCurveAffine, Curve, Group}, plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector}, poly::Rotation}, poseidon::hasher::{spec::OptimizedPoseidonSpec, PoseidonHash, PoseidonSponge}, utils::{BigPrimeField, ScalarField}, AssignedValue};
use halo2_gadgets::poseidon::{primitives::{ConstantLength, Hash as inlineHash, Spec}};
use halo2_base::halo2_proofs::halo2curves::ff::BatchInvert;
use itertools::Itertools;
use core::{borrow::Borrow, marker::PhantomData};
use std::{cell::RefCell, fs::File, iter, time::Instant};
use crate::accumulation::protostar::ivc::halo2::chips::{poseidon::hash_chip::Poseidon2Chip, scalar_mul::ecc_deg6_hash::{ScalarMulChip, ScalarMulChipConfig, ScalarMulChipInputs, ScalarMulConfigInputs, NUM_ADVICE_SM, NUM_FIXED_SM, NUM_INSTANCE_SM}};
use crate::{accumulation::protostar::ivc::halo2::chips::transcript::{NUM_HASH_BITS, NUM_CHALLENGE_BITS}, util::arithmetic::{fe_from_limbs, fe_to_limbs, into_coordinates}};
use crate::accumulation::protostar::ivc::halo2::{ProtostarAccumulationVerifierParam, chips::{L, T, R as RATE, NUM_ADVICE, NUM_CONSTANTS}};
use crate::{accumulation::{protostar::{ProtostarAccumulatorInstance, ProtostarStrategy::{Compressing, NoCompressing}}, PlonkishNarkInstance}, backend::PlonkishCircuit, frontend::halo2::CircuitExt, poly::multilinear::MultilinearPolynomial, util::{
    arithmetic::{add_proj, add_proj_comp, double_proj, double_proj_comp, fe_from_bits_le, fe_to_bits_le, fe_to_fe, fe_truncated, into_coordinate_proj, is_identity_proj, is_scaled_identity_proj, powers, sub_proj_comp, CurveAffine, PrimeFieldBits, ProjectivePoint, TwoChainCurve}, end_timer, izip_eq, start_timer, transcript::{TranscriptRead, TranscriptWrite}}};
use rand::RngCore;
use poseidon::{Spec as PoseidonSpec, Poseidon as PoseidonInlineHash};
use crate::accumulation::protostar::ivc::halo2::ivc_circuits::primary::{R_F, R_P};
use crate::accumulation::protostar::ivc::halo2::chips::poseidon::{hash_chip::{PoseidonChip, PoseidonConfig}, spec::PoseidonSpec as PoseidonChipSpec};
use poseidon2::circuit::spec::PoseidonSpec as Poseidon2ChipSpec;
use crate::accumulation::protostar::ivc::halo2::chips::poseidon::hash_chip::Poseidon2Config;
// public inputs length for the CycleFoldInputs for compressing 
pub const CF_IO_LEN: usize = 1;
pub const NUM_FIXED: usize = NUM_CONSTANTS + 1;

// pub type AssignedCycleFoldInputs<Assigned, AssignedSecondary> =
//     CycleFoldInputs<Assigned, AssignedSecondary>;

// #[derive(Debug, Clone)]
// pub struct FunctionConfig 
// {
//     advices: [Column<Advice>; 3],
//     selectors: [Selector; 2],
//     instance: Column<Instance>,
//     // constant: Column<Fixed>
// }

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
    //poseidon: PoseidonConfig<C, T, RATE, L>,
    poseidon: Poseidon2Config<C, T, RATE, L>,
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
    pub hash_config: PoseidonSpec<C::Scalar, T, RATE>,
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
        let hash_config = PoseidonSpec::<C::Scalar, T, RATE>::new(R_F, R_P);

        let num_witness_comm = primary_avp.num_folding_witness_polys();
        let num_cross_comms = match primary_avp.strategy {
            NoCompressing => primary_avp.num_cross_terms,
            Compressing => 1
        };

        let inputs = 
            CycleFoldInputs::<C::Scalar, C::Secondary>{
                r_le_bits: fe_to_bits_le(C::Scalar::ZERO).into_iter().take(NUM_CHALLENGE_BITS).collect_vec(), 
                r: C::Scalar::ZERO,
                nark_witness_comms: vec![C::Secondary::identity(); num_witness_comm],
                cross_term_comms: vec![C::Secondary::identity(); num_cross_comms],
                acc_witness_comms: vec![C::Secondary::identity(); num_witness_comm],
                acc_e_comm: C::Secondary::identity(),
                acc_prime_witness_comms: vec![C::Secondary::identity(); num_witness_comm],
                acc_prime_e_comm: C::Secondary::identity(),
            };

        Self {
            primary_avp: primary_avp.clone(),
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

    pub fn config_inputs_ecc_deg6_full(
        &self,
        sm_inputs: &Vec<ScalarMulChipInputs<C::Scalar, C::Secondary>>
    ) -> Result<Vec<ScalarMulConfigInputs<C>>, Error> {

        let scalar_bits = NUM_CHALLENGE_BITS;
        let mut sm_config_inputs = Vec::new();

        for inputs in sm_inputs{
            let r = inputs.r;
            let rbits_fe = &inputs.r_le_bits;
            let rbits_rev_fe = rbits_fe.iter().rev().cloned().collect_vec();
            let rbits_rev = rbits_rev_fe.iter().map( |fe|
                { if *fe == C::Scalar::ONE {true} else {false} })
                .collect_vec();

            let rbits_vec = rbits_rev_fe.iter().map(|fe| Value::known(*fe)).collect_vec();
            let re2_vec = powers(C::Scalar::from(2)).take(scalar_bits + 1).map(Value::known).collect_vec().into_iter().rev().collect_vec();
            let mut rlc_vec = vec![Value::known(C::Scalar::ZERO)];
            for i in 0..scalar_bits {
                let rlc = if rbits_rev[i] { rlc_vec[i] + re2_vec[i] } else { rlc_vec[i] };
                rlc_vec.push(rlc);
            }
            let zero = ProjectivePoint {
                x: C::Scalar::ZERO,
                y: C::Scalar::ONE,
                z: C::Scalar::ZERO,
            };
            
            let p = inputs.nark_comm; 
            let acc_comm = inputs.acc_comm;
            let acc_prime_comm = inputs.acc_prime_comm;

            let p_coord = into_coordinate_proj(&p);
            let p_single_x = into_coordinates(&p)[0];
            let p_single_y = into_coordinates(&p)[1];
            let mut ptx_vec = Vec::new();
            let mut pty_vec = Vec::new();
            for i in 0..scalar_bits {
                ptx_vec.push(Value::known(p_single_x));
                pty_vec.push(Value::known(p_single_y));
            }

            let acc_comm_x = into_coordinates(&acc_comm)[0];
            let acc_comm_y = into_coordinates(&acc_comm)[1];
    
            let mut acc_prev = ProjectivePoint::identity();
            let mut acc_prev_xvec = Vec::new();
            let mut acc_prev_yvec = Vec::new();
            let mut acc_prev_zvec = Vec::new();
    
            let mut lhs_double_xvec = Vec::new();
            let mut lhs_double_yvec = Vec::new();
            let mut lhs_double_zvec = Vec::new();
            let mut lhs_zvec = Vec::new();
            let mut rhs_zvec = Vec::new();
    
            acc_prev_xvec.push(acc_prev.x);
            acc_prev_yvec.push(acc_prev.y); 
            acc_prev_zvec.push(acc_prev.z);
    
            for i in 0..scalar_bits {
                let choice_proj = if rbits_rev[i] { 
                    ProjectivePoint::new(p_single_x, p_single_y, C::Scalar::ONE)
                } else { zero };
                
                acc_prev = double_proj_comp(acc_prev);
                let lhs = acc_prev;
                acc_prev = add_proj_comp(acc_prev, choice_proj);
                acc_prev_xvec.push(acc_prev.x);
                acc_prev_yvec.push(acc_prev.y);
                acc_prev_zvec.push(acc_prev.z);
    
                lhs_double_xvec.push(lhs.x);
                lhs_double_yvec.push(lhs.y);
                lhs_double_zvec.push(lhs.z);
            }
    
            for i in 0..scalar_bits {
                let acc_prev_proj = ProjectivePoint::new(acc_prev_xvec[i+1], acc_prev_yvec[i+1], acc_prev_zvec[i+1]);
                let lhs_double_proj = ProjectivePoint::new(lhs_double_xvec[i], lhs_double_yvec[i], lhs_double_zvec[i]);
                let p_single_proj = if rbits_rev[i] { 
                    ProjectivePoint::new(p_single_x, p_single_y, C::Scalar::ONE)
                } else { zero };
    
                let rhs = sub_proj_comp(acc_prev_proj, p_single_proj);
                if is_identity_proj(rhs) && is_identity_proj(lhs_double_proj) {
                    lhs_zvec.push(C::Scalar::ONE);
                    rhs_zvec.push(C::Scalar::ONE);
                } else if is_identity_proj(rhs) && is_scaled_identity_proj(lhs_double_proj) {
                    lhs_zvec.push(lhs_double_proj.y);
                    rhs_zvec.push(C::Scalar::ONE);
                } else if is_identity_proj(lhs_double_proj) && is_scaled_identity_proj(rhs) {
                    lhs_zvec.push(C::Scalar::ONE);
                    rhs_zvec.push(rhs.y);
                } else {
                    lhs_zvec.push(lhs_double_zvec[i]);
                    rhs_zvec.push(rhs.z);
                }
            }
    
            let batch_invert_time = Instant::now();
            lhs_zvec.batch_invert();
            // println!("batch_invert_time2: {:?}", batch_invert_time.elapsed());
            
            let lambda_vec = lhs_zvec.iter().zip(rhs_zvec).map(|(lhs, rhs)| Value::known(*lhs*rhs)).collect_vec();        
            let r_native = fe_from_bits_le(rbits_fe.clone());
            let r_non_native: C::Base = fe_to_fe(r_native);
            let scalar_mul_given: C::Secondary = (p * r_non_native).into();
            let scalar_mul_calc = ProjectivePoint::new(acc_prev_xvec.last().unwrap().clone(), acc_prev_yvec.last().unwrap().clone(), acc_prev_zvec.last().unwrap().clone());
            let scalar_mul_calc_affine = scalar_mul_calc.to_affine();
            let scalar_mul_calc_curve = C::Secondary::from_xy(scalar_mul_calc_affine.0, scalar_mul_calc_affine.1).unwrap();

            let acc_prime_calc  = (scalar_mul_calc_curve + acc_comm).to_affine();
            let acc_prime_given = inputs.acc_prime_comm; 
            assert_eq!(acc_prime_calc, acc_prime_given);
            assert_eq!(scalar_mul_given, scalar_mul_calc_curve);

            // do point addition of comm and sm
            let result_given = acc_comm + scalar_mul_given;
            let comm_proj = ProjectivePoint::new(acc_comm_x, acc_comm_y, C::Scalar::ONE);
            let result_calc = acc_comm + scalar_mul_calc_curve;
            // assert_eq!(result_given.x * result_calc.z, result_calc.x * result_given.z);
            // assert_eq!(result_given.y * result_calc.z, result_calc.y * result_given.z);

            let result_calc_affine = result_calc.to_affine();
            let result_calc_affine_x = into_coordinates(&result_calc_affine)[0];
            let result_calc_affine_y = into_coordinates(&result_calc_affine)[1];
            let acc_x_vec = acc_prev_xvec.iter().map(|fe| Value::known(*fe)).collect_vec();
            let acc_y_vec = acc_prev_yvec.iter().map(|fe| Value::known(*fe)).collect_vec();
            let acc_z_vec = acc_prev_zvec.iter().map(|fe| Value::known(*fe)).collect_vec();
    
            let inputs =
                ScalarMulConfigInputs::<C> { 
                    rbits_vec, 
                    re2_vec,
                    rlc_vec,
                    ptx_vec,
                    pty_vec,
                    acc_x_vec, 
                    acc_y_vec, 
                    acc_z_vec,
                    lambda_vec, 
                    comm_X: Value::known(acc_comm_x),
                    comm_Y: Value::known(acc_comm_y),
                    sm_X: Value::known(scalar_mul_calc_affine.0),
                    sm_Y: Value::known(scalar_mul_calc_affine.1),
                    X3: Value::known(result_calc_affine_x),
                    Y3: Value::known(result_calc_affine_y),
                };  

            sm_config_inputs.push(inputs);
        }

        Ok(sm_config_inputs)
    }

    pub fn hash_inputs(
        &self,
        vp_digest: C::Scalar,
        inputs: &CycleFoldInputs<C::Scalar, C::Secondary>
    ) -> C::Scalar {
        let witness_comm =
            inputs.nark_witness_comms.clone().into_iter()
            .zip(inputs.acc_witness_comms.clone().into_iter())
            .flat_map(|(a, b)| vec![a, b])
            .collect_vec();

        let inputs_vec = iter::empty()
            //.chain([vp_digest])
            .chain([fe_from_bits_le(inputs.r_le_bits.clone())])
            .chain(
                witness_comm
                    .iter()
                    .flat_map(into_coordinates))  
            .chain(
                inputs.cross_term_comms
                    .iter()
                    .flat_map(into_coordinates))
            .chain(into_coordinates(&inputs.acc_e_comm).into_iter())                     
            .collect_vec();

        let message: [C::Scalar; L] =
        match inputs_vec.try_into() {
            Ok(arr) => arr,
            Err(_) => panic!("Failed to convert Vec to Array"),
        };
        assert_eq!(L, message.len());

        //let hash = inlineHash::<C::Scalar, Spec<C::Scalar, T, RATE>, ConstantLength<L>, T, RATE>::init().hash(message);
        let mut poseidon = PoseidonInlineHash::<C::Scalar, T, RATE>::new(R_F, R_P);
        poseidon.update(&message);
        let hash = poseidon.squeeze();
        fe_truncated(hash, NUM_HASH_BITS)
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

        let instance = [0; NUM_INSTANCE_SM].map(|_| meta.instance_column());
        for col in &instance {
            meta.enable_equality(*col);
        }

        let advices = [0; NUM_ADVICE_SM + 1].map(|_| meta.advice_column());
        for col in &advices {
            meta.enable_equality(*col);
        }

        let constants = [0; NUM_FIXED].map(|_| meta.fixed_column());
        for col in &constants {
            meta.enable_constant(*col);
            meta.enable_equality(*col);
        }

        let scalar_mul = ScalarMulChipConfig::<C>::configure(meta, advices[..NUM_ADVICE_SM].try_into().unwrap(), [constants[NUM_CONSTANTS]]);
        
        //let poseidon = 
            // PoseidonChip::<C, PoseidonChipSpec, T, RATE, L>::configure(
            //     meta,
            //     advices[..T].try_into().unwrap(),
            //     advices[T],
            //     constants[..T].try_into().unwrap(), 
            //     constants[T..2*T].try_into().unwrap(), 
            // );

        let poseidon = 
            Poseidon2Chip::<C, Poseidon2ChipSpec, T, RATE, L>::configure(
                meta,
                advices[..T].try_into().unwrap(),
                advices[T],
                constants[..T].try_into().unwrap(), 
                constants[T..2*T].try_into().unwrap(), 
            );

        Self::Config {
            poseidon,
            scalar_mul,
            instance: instance[0],
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {

        let mut hash_inputs = Vec::new();
        let sm_chip_inputs = self.sm_chip_inputs(&self.inputs)?;
        let config_inputs_time = Instant::now();
        let config_inputs = self.config_inputs_ecc_deg6_full(&sm_chip_inputs)?;
        println!("config_input_time: {:?}", config_inputs_time.elapsed());

        for i in 0..config_inputs.len() {
            if i == 0 {
                hash_inputs.extend_from_slice(&config.scalar_mul.assign(layouter.namespace(|| "ScalarMulChip"), config_inputs[i].clone())?);
            } else {
                hash_inputs.extend_from_slice(&config.scalar_mul.assign(layouter.namespace(|| "ScalarMulChip"), config_inputs[i].clone())?[1..]);
            }
        }
        
        // let hash_chip = PoseidonChip::<C, PoseidonChipSpec, T, RATE, L>::construct(
        //     config.poseidon,
        // );

        let hash_chip = Poseidon2Chip::<C, Poseidon2ChipSpec, T, RATE, L>::construct(
            config.poseidon,
        );

        let message: [AssignedCell<C::Scalar, C::Scalar>; L] =
        match hash_inputs.try_into() {
            Ok(arr) => arr,
            Err(_) => panic!("Failed to convert Vec to Array"),
        };

        let time = Instant::now();
        let hash = hash_chip.hash(
                layouter.namespace(|| "perform poseidon hash"),
                message.clone(),
        )?;
        println!("hash: {:?}", time.elapsed());

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
        // instances[0][0] = self.hash_inputs(inputs);
        instances
    }

    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}
