use halo2_base::{halo2_proofs::
    {plonk::{Circuit, Error, ConstraintSystem}, 
    dev::MockProver, 
    arithmetic::Field,
    halo2curves::group::{prime::PrimeCurveAffine, Curve, Group},
    circuit::{Layouter, SimpleFloorPlanner, Value}}, 
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
    gates::{circuit::{builder::{BaseCircuitBuilder, self}, BaseCircuitParams, CircuitBuilderStage, BaseConfig}, GateInstructions, flex_gate::threads::SinglePhaseCoreManager}, AssignedValue, poseidon::hasher::{spec::OptimizedPoseidonSpec, PoseidonSponge, PoseidonHash}};
use halo2_ecc::{ecc::EcPoint, bigint::ProperCrtUint};
use itertools::Itertools;
use core::{borrow::Borrow, marker::PhantomData};
use std::{iter, time::Instant, cell::RefCell};
use super::halo2::{chips::{poseidon::spec_t13::PoseidonSpec, scalar_mul::ec_chip::{ScalarMulChip}}, test::strawman::{self, RANGE_BITS, NUM_CHALLENGE_BITS, NUM_LIMBS, NUM_LIMB_BITS, R_F, R_P, SECURE_MDS, NUM_HASH_BITS}};
use super::halo2::test::strawman::{Chip, PoseidonTranscriptChip, fe_to_limbs, into_coordinates};
use ivc::ProtostarAccumulationVerifierParam;
use crate::{util::{
    end_timer, 
    transcript::{TranscriptRead, TranscriptWrite},
    arithmetic::{PrimeFieldBits, CurveAffine, TwoChainCurve, fe_to_fe, fe_from_bits_le, fe_to_bits_le, fe_truncated}, izip_eq, start_timer}, 
    accumulation::{PlonkishNarkInstance, protostar::{ProtostarAccumulatorInstance, ivc::{self, halo2::chips::scalar_mul::ec_chip::ScalarMulConfigInputs}, ProtostarStrategy::{Compressing, NoCompressing}}}, frontend::halo2::CircuitExt, backend::PlonkishCircuit, poly::multilinear::MultilinearPolynomial};
use rand::RngCore;

pub const T: usize = 5;
pub const R: usize = 4;
pub const L: usize = 20;
pub const NUM_ADVICE: usize = 1;
pub const NUM_FIXED: usize = 1;

// public inputs length for the CycleFoldInputs for compressing 
pub const CF_IO_LEN: usize = 1;

pub type AssignedCycleFoldInputs<Assigned, AssignedSecondary> =
    CycleFoldInputs<Assigned, AssignedSecondary>;

#[derive(Debug, Clone)]
pub struct CycleFoldInputs<F, C> 
{   
    pub r_le_bits: Vec<F>,
    pub nark_witness_comms: Vec<C>,
    pub cross_term_comms: Vec<C>,
    pub acc_witness_comms: Vec<C>,
    pub acc_e_comm: C,
    pub acc_prime_witness_comms: Vec<C>,
    pub acc_prime_e_comm: C,
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
    pub hash_config: OptimizedPoseidonSpec<C::Scalar, T, R>,
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
            builder_params: BaseCircuitParams
        ) -> Self {
            let primary_avp = primary_avp.unwrap_or_default();
            let poseidon_spec = OptimizedPoseidonSpec::<C::Scalar, T, R>::new::<R_F, R_P, SECURE_MDS>();
            let hash_config = poseidon_spec.clone();

            let num_witness_comm = primary_avp.num_folding_witness_polys();
            let num_cross_comms = match primary_avp.strategy {
                NoCompressing => primary_avp.num_cross_terms,
                Compressing => 1
            };

            let bytes: &[u8] = &[44, 74, 155, 202, 230, 209, 105, 242, 77, 222, 213, 71, 58, 97, 34, 113, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
            let inputs = 
                CycleFoldInputs::<C::Scalar, C::Secondary>{
                    r_le_bits: fe_to_bits_le(C::Scalar::from_bytes_le(bytes)).into_iter().take(NUM_CHALLENGE_BITS).collect_vec(), // Self::R_LE_BITS.to_vec(),
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
        cross_term_comms: Vec<Comm>,
        primary_nark: ProtostarAccumulatorInstance<C::Base, Comm>,
        acc: ProtostarAccumulatorInstance<C::Base, Comm>,
        acc_prime: ProtostarAccumulatorInstance<C::Base, Comm>,
    ) {
        let convert_vec_comms = |comms: &[Comm]| comms.iter().map(AsRef::as_ref).cloned().collect_vec();
        self.inputs = CycleFoldInputs::<C::Scalar, C::Secondary> {
            r_le_bits: r_le_bits.into_iter().map(fe_to_fe).collect::<Vec<_>>(),
            nark_witness_comms: convert_vec_comms(&primary_nark.witness_comms),
            cross_term_comms: convert_vec_comms(&cross_term_comms),
            acc_witness_comms: convert_vec_comms(&acc.witness_comms),
            acc_e_comm: *acc.e_comm.as_ref(),
            acc_prime_witness_comms: convert_vec_comms(&acc_prime.witness_comms),
            acc_prime_e_comm: *acc_prime.e_comm.as_ref(),
        };
    }

    // pub fn prepare_inputs_scalar_chip(
    //     &self,
    //     inputs: &CycleFoldInputs<C::Scalar, C::Secondary>
    // ) -> Result<ScalarMulChipInputs<C::Scalar, C::Secondary>, Error> {

    // }

    // pub fn form_scalar_chip_inputs(
    //     &self,
    //     inputs: &ScalarMulChipInputs<C::Scalar, C::Secondary>
    // ) -> Result<ScalarMulConfigInputs<C::Scalar>, Error> {

    //     let vec_len: usize = 129;
    //     let mut nark_x_vec = Vec::new();
    //     let mut nark_y_vec = Vec::new();
    //     let mut rnark_x_vec = Vec::new();
    //     let mut rnark_y_vec = Vec::new();

    //     let one = C::Scalar::ONE;
    //     let zero = C::Scalar::ZERO;
    //     let r_le_bits = &inputs.r_le_bits;
    //     let r_le_bits_value = r_le_bits.iter().map(|fe| Value::known(*fe)).collect_vec();
    //     let r_window_bits = r_le_bits[1..].chunks(2).collect_vec();

    //     // push last element as the first rbit
    //     let mut rbits_vec = Vec::new();
    //     rbits_vec = r_le_bits_value.clone();
    //     rbits_vec.push(r_le_bits_value[0]);

    //     let p_zero = C::Secondary::identity();
    //     let mut p = inputs.nark_comm; 
    //     let acc = inputs.acc_comm;
    //     let p_single = p;
        
    //     // initial assumption: rbits[0] = 1
    //     let p_single_x = into_coordinates(&p_single)[0];
    //     let p_single_y = into_coordinates(&p_single)[1];
    //     nark_x_vec.push(Value::known(p_single_x));
    //     nark_y_vec.push(Value::known(p_single_y));
    //     rnark_x_vec.push(Value::known(p_single_x));
    //     rnark_y_vec.push(Value::known(p_single_y)); 

    //     for idx in (1..vec_len-2).step_by(2) {
    //         p = <C::Secondary as CurveAffine>::CurveExt::double(&p.into()).into(); 
    //         nark_x_vec.push(Value::known(into_coordinates(&p)[0]));
    //         nark_y_vec.push(Value::known(into_coordinates(&p)[1]));
    //         let p_single = p;

    //         p = <C::Secondary as CurveAffine>::CurveExt::double(&p.into()).into();
    //         nark_x_vec.push(Value::known(into_coordinates(&p)[0]));
    //         nark_y_vec.push(Value::known(into_coordinates(&p)[1])); 

    //         let p_triple = (p + p_single).to_affine();
    //         rnark_x_vec.push(Value::known(into_coordinates(&p_triple)[0]));
    //         rnark_y_vec.push(Value::known(into_coordinates(&p_triple)[0])); 

    //         let acc_sel = match r_window_bits[idx/2] {
    //             [z, o] if *z == zero && *o == zero => p_zero,    // 00
    //             [z, o] if *z == one && *o == zero => p_single,   // 10
    //             [z, o] if *z == zero && *o == one => p,          // 01
    //             [z, o] if *z == one && *o == one => p_triple,    // 11
    //             _ => panic!("Invalid window"),
    //         };

    //         let acc_prev = C::Secondary::from_xy(rnark_x_vec[idx-1].assign().unwrap(), rnark_y_vec[idx-1].assign().unwrap()).unwrap();
    //         let acc_next = (acc_prev + acc_sel).to_affine();

    //         rnark_x_vec.push(Value::known(into_coordinates(&acc_next)[0]));
    //         rnark_y_vec.push(Value::known(into_coordinates(&acc_next)[1]));

    //     }

    //     // push last rbit 
    //     p = <C::Secondary as CurveAffine>::CurveExt::double(&p.into()).into(); 
    //     nark_x_vec.push(Value::known(into_coordinates(&p)[0]));
    //     nark_y_vec.push(Value::known(into_coordinates(&p)[1]));

    //     if r_le_bits[vec_len-2] == one {
    //         let acc_prev = C::Secondary::from_xy(rnark_x_vec[vec_len-3].assign().unwrap(), rnark_y_vec[vec_len-3].assign().unwrap()).unwrap();
    //         let acc_next = (acc_prev + p).to_affine();
    //         rnark_x_vec.push(Value::known(into_coordinates(&acc_next)[0]));
    //         rnark_y_vec.push(Value::known(into_coordinates(&acc_next)[1]));
    //     } else {
    //         rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-3].assign().unwrap()));
    //         rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-3].assign().unwrap()));
    //     }

    //     // push last element as the first rbit
    //     nark_x_vec.push(Value::known(into_coordinates(&p_single)[0]));
    //     nark_y_vec.push(Value::known(into_coordinates(&p_single)[1]));

    //     // correct initial assumption
    //     if r_le_bits[0] == one {
    //         rnark_x_vec.push(Value::known(rnark_x_vec[vec_len-2].assign().unwrap()));
    //         rnark_y_vec.push(Value::known(rnark_y_vec[vec_len-2].assign().unwrap()));
    //     } else {
    //         let acc_prev = C::Secondary::from_xy(rnark_x_vec[vec_len-2].assign().unwrap(), rnark_y_vec[vec_len-2].assign().unwrap()).unwrap();
    //         let acc_next = (acc_prev - p_single).to_affine();
    //         rnark_x_vec.push(Value::known(into_coordinates(&acc_next)[0]));
    //         rnark_y_vec.push(Value::known(into_coordinates(&acc_next)[1]));
    //     }

    //     let scalar_mul_calc = C::Secondary::from_xy(rnark_x_vec[vec_len-1].assign().unwrap(), rnark_y_vec[vec_len-1].assign().unwrap()).unwrap();
    //     let acc_prime_calc  = (scalar_mul_calc + acc).to_affine();
    //     let acc_prime_given = inputs.acc_prime_comm; 
    //     assert_eq!(acc_prime_calc, acc_prime_given);

    //     let inputs =
    //         ScalarMulConfigInputs::<C::Scalar> { 
    //             rbits_vec, nark_x_vec, nark_y_vec, rnark_x_vec, rnark_y_vec, 
    //             acc_x: Value::known(into_coordinates(&acc)[0]), 
    //             acc_y: Value::known(into_coordinates(&acc)[1]), 
    //             acc_prime_calc_x: Value::known(into_coordinates(&acc_prime_calc)[0]), 
    //             acc_prime_calc_y: Value::known(into_coordinates(&acc_prime_calc)[1]), 
    //             acc_prime_given_x: Value::known(into_coordinates(&acc_prime_given)[0]), 
    //             acc_prime_given_y: Value::known(into_coordinates(&acc_prime_given)[1])
    //         };

    //     Ok(inputs)
    // }

}

//     // todo do we include this in hash - vp_digest
//     pub fn hash_inputs(
//         &self,
//         unassigned_inputs: &CycleFoldInputs<C::Scalar, C::Secondary>
//     ) -> C::Scalar {
//         let spec = &self.hash_config;
//         let mut poseidon = PoseidonHash::from_spec(spec.clone());
//         let inputs = iter::empty()
//             //.chain([vp_digest]).flat_map(fe_to_limbs)
//             .chain([fe_from_bits_le(unassigned_inputs.r_le_bits.clone())])
//             .chain(
//                 unassigned_inputs.nark_witness_comms
//                     .iter()
//                     .flat_map(into_coordinates))
//             .chain(
//                 unassigned_inputs.cross_term_comms
//                     .iter()
//                     .flat_map(into_coordinates))
//             .chain(
//                 unassigned_inputs.acc_witness_comms
//                     .iter()
//                     .flat_map(into_coordinates))  
//             .chain(into_coordinates(&unassigned_inputs.acc_e_comm).into_iter())              
//             // .chain(
//             //     unassigned_inputs.acc_prime_witness_comms
//             //         .iter()
//             //         .flat_map(into_coordinates))
//             // .chain(into_coordinates(&unassigned_inputs.acc_prime_e_comm).into_iter())          
//             .collect_vec();
//         println!("hash_inputs: {:?}", inputs.len());
//         poseidon.update(inputs.as_slice());
//         fe_truncated(poseidon.squeeze(), NUM_HASH_BITS)
//     }

//     pub fn synthesize_circuit(
//         &self,
//         mut layouter: impl Layouter<C::Scalar>,
//         config: BaseConfig<C::Scalar>,
//     ) -> Result<(), Error> 
//     {
//         let tcc_chip = &self.tcc_chip;

//         // check scalar_mul 
//         self.compute_and_constrain(builder, &assigned_inputs)?;

//         let r = tcc_chip.gate_chip.bits_to_num(builder.main(), &assigned_inputs.r_le_bits[..NUM_CHALLENGE_BITS]);
        
//         let assigned_instances = &mut binding.assigned_instances;
//         assert_eq!(assigned_instances.len(), 1, "CycleFoldCircuit must have exactly 1 instance column");
//         assert!(assigned_instances[0].is_empty());

//         assigned_instances[0].push(inputs_hash);
//         // assigned_instances[0].extend(scalar_mul_outputs);

//         // let instances = self.instances();
//         // MockProver::run(14, &*binding, instances.clone()).unwrap().assert_satisfied();

//         Ok(())
//     }
// }

impl<C> Circuit<C::Scalar> for CycleFoldCircuit<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    type Config = BaseConfig<C::Scalar>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = BaseCircuitParams;

    fn without_witnesses(&self) -> Self {
        Self {
            primary_avp: self.primary_avp.clone(),
            hash_config: self.hash_config.clone(),
            inputs: self.inputs.clone(),
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
        let synthesize_ec_time = Instant::now();
        //self.synthesize_circuit(layouter.namespace(|| ""), config.clone())?;
        let duration_ec_synthesize = synthesize_ec_time.elapsed();
        println!("Time for synthesize_ec: {:?}", duration_ec_synthesize);
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
        //instances[0][0] = self.hash_inputs(inputs);
        instances
    }

    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}
