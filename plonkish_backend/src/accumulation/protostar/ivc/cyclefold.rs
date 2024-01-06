use halo2_base::{halo2_proofs::{plonk::{Circuit, ConstraintSystem}, dev::MockProver, 
    circuit::{SimpleFloorPlanner, Layouter}}, 
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
    gates::circuit::{builder::{BaseCircuitBuilder, self}, BaseCircuitParams, CircuitBuilderStage, BaseConfig}, AssignedValue, poseidon::hasher::spec::OptimizedPoseidonSpec};
use halo2_ecc::{ecc::EcPoint, bigint::ProperCrtUint};
use itertools::Itertools;
use core::{borrow::Borrow, marker::PhantomData};
use std::{iter, time::Instant};
use super::halo2::test::strawman::{self, T, RANGE_BITS, RATE, NUM_CHALLENGE_BITS, NUM_LIMBS, NUM_LIMB_BITS, R_F, R_P, SECURE_MDS};
use super::halo2::test::strawman::{Chip, PoseidonTranscriptChip, fe_to_limbs, into_coordinates};
use ivc::{ProtostarAccumulationVerifier, ProtostarAccumulationVerifierParam};
use crate::{util::{
    end_timer, 
    transcript::{TranscriptRead, TranscriptWrite},
    arithmetic::{PrimeFieldBits, CurveAffine, TwoChainCurve, fe_to_fe}, izip_eq, start_timer}, 
    accumulation::{PlonkishNarkInstance, protostar::{ProtostarAccumulatorInstance, ivc, ProtostarStrategy}}, frontend::halo2::CircuitExt, backend::PlonkishCircuit, poly::multilinear::MultilinearPolynomial};
use crate::Error;
use rand::RngCore;

// public inputs length for the CycleFoldInputs
pub const CF_IO_LEN: usize = 38;
pub struct PrimaryPPForCycleFold {
    pub num_witness_polys: usize,
    pub num_cross_terms: usize,
    pub strategy: ProtostarStrategy,
}

#[derive(Debug, Clone)]
pub struct CycleFoldInputs<F, C> 
{
    pub r: F,
    pub nark_witness_comms: Vec<C>,
    pub cross_term_comms: Vec<C>,
    pub acc_witness_comms: Vec<C>,
    pub acc_e_comm: C,
    pub acc_prime_witness_comms: Vec<C>,
    pub acc_prime_e_comm: C,
}

pub type AssignedCycleFoldInputs<AssignedBase, AssignedSecondary> =
    CycleFoldInputs<AssignedBase, AssignedSecondary>;

// impl<C> CycleFoldInputs<C> 
// where
//     C: TwoChainCurve,
//     C::Scalar: BigPrimeField + PrimeFieldBits,
//     C::Base: BigPrimeField + PrimeFieldBits,
// {
//     pub const DUMMY_H: C::Scalar = C::Scalar::ZERO;

//     pub fn new(
//         avp: Option<ProtostarAccumulationVerifierParam<C::Scalar>>,
//         builder_params: BaseCircuitParams
//     ) -> Self {
//         // take challenge from the transcipt proof too 
//         let primary_proof = Vec::new();
//         let poseidon_spec = OptimizedPoseidonSpec::new::<R_F, R_P, SECURE_MDS>();
//         let hash_config = poseidon_spec.clone();
//         let transcript_config = poseidon_spec.clone();  
//         let circuit_builder = BaseCircuitBuilder::<C::Scalar>::from_stage(CircuitBuilderStage::Mock).use_params(circuit_params.clone());
//         Self {
//             nark_witness_comms: Vec<Comm>,
//             acc_witness_comms: Vec<Comm>,
//             acc_e_comm: Comm,
//             r: C::Scalar,
//             acc_prime_witness_comms: Vec<Comm>,
//             acc_prime_e_comm: Comm,
//         }
//     }
// }

#[derive(Debug, Clone)]
pub struct CycleFoldCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub tcc_chip: Chip<C>,
    pub avp: ProtostarAccumulationVerifierParam<C::Scalar>,
    pub hash_config: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    pub transcript_config: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    pub inputs: CycleFoldInputs<C::Base, C>,
    pub circuit_builder: BaseCircuitBuilder<C::Scalar>,
}

impl<C> CycleFoldCircuit<C> 
where
    C: TwoChainCurve, 
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub const DUMMY_H: C::Scalar = C::Scalar::ZERO;

    pub fn new(
        avp: Option<ProtostarAccumulationVerifierParam<C::Scalar>>,
        builder_params: BaseCircuitParams
    ) -> Self {
        let poseidon_spec = OptimizedPoseidonSpec::new::<R_F, R_P, SECURE_MDS>();
        let hash_config = poseidon_spec.clone();
        let transcript_config = poseidon_spec.clone();  

        let tcc_chip = Chip::<C>::create(range_chip);
        let circuit_builder = BaseCircuitBuilder::<C::Scalar>::from_stage(CircuitBuilderStage::Mock).use_params(circuit_params.clone());
        
        Self {
            tcc_chip,
            avp: avp.clone().unwrap_or_default(),
            hash_config,
            transcript_config,
            inputs: CycleFoldInputs::default(),
            circuit_builder,
        }
    }

    pub fn init(&mut self, vp_digest: C::Scalar) {
        assert_eq!(&self.avp.num_instances, &[38]);
        self.avp.vp_digest = vp_digest;
    }

    pub fn update_cyclefold_inputs<
        Comm: AsRef<C::Secondary>, 
    >(
        &mut self,
        primary_proof: Vec<u8>,
        primary_pp_for_cyclefold: PrimaryPPForCycleFold,
        primary_instances: [C::Base; 2],
        acc: ProtostarAccumulatorInstance<C::Base, Comm>,
        acc_prime: ProtostarAccumulatorInstance<C::Base, Comm>,
        transcript: &mut impl TranscriptRead<Comm, C::Base>,
    ) {

        let instances =
            [&primary_instances[0], &primary_instances[1]].map(Value::as_ref);
        
        let proof = primary_proof.clone();

        for instance in instances.iter() {
            transcript.common_field_element(instance)?;
        }

        let mut nark_witness_comms = Vec::with_capacity(primary_pp_for_cyclefold.num_witness_polys);
        for num_witness_polys in num_witness_polys.iter()
        {
            nark_witness_comms.extend(transcript.read_commitments(*num_witness_polys)?);
        }

        // abosrb acc into transcript
        acc.instances
            .iter()
            .try_for_each(|instances| transcript.common_field_elements(instances))?;

            transcript.common_commitments(&acc.witness_comms)?;
            transcript.common_field_elements(&acc.challenges)?;
            transcript.common_field_element(&acc.u)?;
            transcript.common_commitment(&acc.e_comm)?;

        if let Some(compressed_e_sum) = acc.compressed_e_sum.as_ref() {
            transcript.common_field_element(compressed_e_sum)?;
        }


        let cross_term_comms = match primary_pp_for_cyclefold.strategy {
            NoCompressing => {
                let cross_term_comms = transcript.read_commitments(primary_pp_for_cyclefold.num_cross_terms)?;
                cross_term_comms
            }
            Compressing => {
                let zeta_cross_term_comm = vec![transcript.read_commitment()];
                zeta_cross_term_comm
            }
        };
 
        let r = transcript.squeeze_challenge();

        self.inputs = CycleFoldInputs::<C::Base, Comm>{
            r,
            nark_witness_comms,
            cross_term_comms,
            acc_witness_comms: acc.witness_comms,
            acc_e_comm: acc.e_comm,
            acc_prime_witness_comms: acc_prime.witness_comms,
            acc_prime_e_comm: acc_prime.e_comm,
        };
    }

    pub fn assign_cyclefold_inputs(
        &mut self,
    ) -> Result<AssignedCycleFoldInputs<
            ProperCrtUint<C::Scalar>, 
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
            Error> 
    {
        let tcc_chip = &self.tcc_chip;
        let builder = self.circuit_builder.pool(0);
        let inputs = &self.inputs;

        let r = tcc_chip.assign_witness_base(builder, inputs.r)?;
        let nark_witness_comms = inputs.nark_witness_comms
            .iter()
            .map(|comm| tcc_chip.assign_witness_primary(builder, comm))
            .try_collect::<_, Vec<_>, _>()?; 
        let cross_term_comms = inputs.cross_term_comms
            .iter()
            .map(|comm| tcc_chip.assign_witness_primary(builder, comm))
            .try_collect::<_, Vec<_>, _>()?; 

        let acc_e_comm = tcc_chip.assign_witness_primary(builder, inputs.acc_e_comm)?;
        let acc_witness_comms = inputs.acc_witness_comms
            .iter()
            .map(|comm| tcc_chip.assign_witness_primary(builder, comm))
            .try_collect::<_, Vec<_>, _>()?; 
        
        let acc_prime_e_comm = tcc_chip.assign_witness_primary(builder, inputs.acc_prime_e_comm)?;
        let acc_prime_witness_comms = inputs.acc_prime_witness_comms
            .iter()
            .map(|comm| tcc_chip.assign_witness_primary(builder, comm))
            .try_collect::<_, Vec<_>, _>()?; 

        Ok(AssignedCycleFoldInputs {
            r,
            nark_witness_comms,
            cross_term_comms,
            acc_witness_comms,
            acc_e_comm,
            acc_prime_witness_comms,
            acc_prime_e_comm,
        })

    }

    pub fn compute_and_constrain(
        &mut self, 
        assigned_inputs: &AssignedCycleFoldInputs<
            ProperCrtUint<C::Scalar>, 
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        ) -> Result<(), Error> 
    {
        let tcc_chip = &self.tcc_chip;
        let builder = self.circuit_builder.pool(0);

        let r = assigned_inputs.r;
        let r_nark_witness_comms = assigned_inputs
            .nark_witness_comms
            .iter()
            .map(|comm| tcc_chip.scalar_mul_primary(builder, comm, &[r]))
            .try_collect::<_, Vec<_>, _>()?;

        let acc_prime_witness_comms = 
            izip_eq!(&assigned_inputs.acc_witness_comms, &r_nark_witness_comms)
            .map(|(lhs, rhs)| 
            tcc_chip.add_primary(builder, lhs, rhs))
            .try_collect::<_, Vec<_>, _>()?;

        let acc_prime_e_comm = if cross_term_comms.is_empty() {
            assigned_inputs.acc_e_comm.clone()
        } else {
            let timer = start_timer(|| format!("cyclefold_compute_e_comm-cross_term_comms.len()-{}", cross_term_comms.len()));
            let mut e_comm = assigned_inputs.cross_term_comms.last().unwrap().clone();
                for item in assigned_inputs.cross_term_comms.iter().rev().skip(1).chain([&assigned_inputs.acc_e_comm]) {
                    e_comm = tcc_chip.scalar_mul_primary(builder, &e_comm, &[r])?;
                    e_comm = tcc_chip.add_primary(builder, &e_comm, item)?;
                }
                end_timer(timer);
                e_comm
        };

        // constrains scalar_mul natively in circuit
        izip_eq!(&acc_prime_witness_comms, &assigned_inputs.acc_prime_witness_comms)
            .map(|(lhs, rhs)| {
                tcc_chip.constrain_equal_primary(builder, lhs, rhs)?;
            });

        tcc_chip.constrain_equal_primary(builder, &acc_prime_e_comm, &assigned_inputs.acc_prime_e_comm)?;

        Ok(())
    }

    pub fn flatten_inputs<Comm: AsRef<C::Secondary>>(
        &mut self,
        assigned_inputs: &CycleFoldInputs<C::Base, Comm>
    ) -> Result<Vec<C::Scalar>, Error> {
        let fe_to_limbs = |fe| fe_to_limbs(fe, NUM_LIMB_BITS);
        let inputs = iter::empty()
            .chain(fe_to_limbs(assigned_inputs.r))
            .chain(
                assigned_inputs.nark_witness_comms
                    .iter()
                    .map(AsRef::as_ref)
                    .flat_map(into_coordinates))
            .chain(
                assigned_inputs.cross_term_comms
                    .iter()
                    .map(AsRef::as_ref)
                    .flat_map(into_coordinates))
            .chain(
                assigned_inputs.acc_witness_comms
                    .iter()
                    .map(AsRef::as_ref)
                    .flat_map(into_coordinates))  
            .chain(into_coordinates(assigned_inputs.acc_e_comm.as_ref()))              
            .chain(
                assigned_inputs.acc_prime_witness_comms
                    .iter()
                    .map(AsRef::as_ref)
                    .flat_map(into_coordinates))
            .chain(into_coordinates(assigned_inputs.acc_prime_e_comm.as_ref()))              
            .copied()
            .collect_vec();

        Ok(inputs)
    }

    pub fn flatten_assigned_inputs(
        &mut self,
        assigned_inputs: &AssignedCycleFoldInputs<
            ProperCrtUint<C::Scalar>, 
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>>
    ) -> Result<Vec<AssignedValue<C::Scalar>>, Error> {
        let inputs = iter::empty()
            .chain(assigned_inputs.r.limbs())
            .chain(
                assigned_inputs.nark_witness_comms
                    .iter()
                    .flat_map(|point| vec![point.x(), point.y()].into_iter()),
            )
            .chain(
                assigned_inputs.cross_term_comms
                    .iter()
                    .flat_map(|point| vec![point.x(), point.y()].into_iter()),
            )
            .chain(
                assigned_inputs.acc_witness_comms
                    .iter()
                    .flat_map(|point| vec![point.x(), point.y()].into_iter()),
            )
            .chain(vec![assigned_inputs.acc_e_comm.x(), assigned_inputs.acc_e_comm.y()].into_iter())
            .chain(
                assigned_inputs.acc_prime_witness_comms
                    .iter()
                    .flat_map(|point| vec![point.x(), point.y()].into_iter()),
            )
            .chain(vec![assigned_inputs.acc_prime_e_comm.x(), assigned_inputs.acc_prime_e_comm.y()].into_iter())
            .copied()
            .collect_vec();

        Ok(inputs)
    }


    pub fn synthesize_circuit(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        config: BaseConfig<C::Scalar>,
    ) -> Result<(), Error> 
    {
        let builder = self.circuit_builder.pool(0);
        let assigned_inputs = self.assign_cyclefold_inputs()?;
        // check scalar_mul 
        self.compute_and_constrain(&assigned_inputs)?;
        let flattened_assigned_inputs = self.flatten_assigned_inputs(&assigned_inputs)?;
        assert_eq!(flattened_assigned_inputs.len(), CF_IO_LEN, "CycleFoldInputs must have exactly 38 elements");

        let assigned_instances = &mut self.circuit_builder.assigned_instances;
        assert_eq!(assigned_instances.len(), 1, "CycleFoldCircuit must have exactly 1 instance column");
        assert!(assigned_instances[0].is_empty());

        assigned_instances[0].extend(flattened_assigned_inputs);


        let instances = self.instances();
        MockProver::run(14, &self.circuit_builder, instances.clone()).unwrap().assert_satisfied();

        self.circuit_builder.synthesize(config.clone(), layouter.namespace(|| "cyclefold_circuit"));

        let copy_manager = builder.copy_manager.lock().unwrap();
        println!("cyclefold_circuit_copy_manager.advice_equalities {:?}", copy_manager.advice_equalities.len());
        println!("cyclefold_circuit_copy_manager.constant_equalities {:?}", copy_manager.constant_equalities.len());
        println!("cyclefold_circuit_copy_manager.assigned_constants {:?}", copy_manager.assigned_constants.len());
        println!("cyclefold_circuit_copy_manager.assigned_advices {:?}", copy_manager.assigned_advices.len());
        drop(copy_manager);

        self.circuit_builder.clear();
        //drop(binding);

        Ok(())
    }
}

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
            tcc_chip: self.tcc_chip.clone(),
            avp: self.avp.clone(),
            hash_config: self.hash_config.clone(),
            transcript_config: self.transcript_config.clone(),
            inputs: self.inputs.clone(),
            circuit_builder: self.circuit_builder.clone(),
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
        self.synthesize_circuit(layouter.namespace(|| ""), config.clone())?;
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
        let inputs = &self.inputs;
        let instances = self.flatten_inputs(inputs).unwrap();
        vec![instances]
    }

    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}

    // pub fn witness_collector_cyclefold<F1, F2>(
    //     circuit: &impl PlonkishCircuit<F1>,
    // ) -> Result<MultilinearPolynomial<F2>, Error> {
    //     let round = 0;
    //     let mut witness_polys = Vec::with_capacity(1);
    //     let num_witness_polys = witness_polys.len();
    //     let mut challenges = Vec::with_capacity(1);

    //     let timer = start_timer(|| format!("witness_collector-{round}"));
    //     let polys = circuit.synthesize(round, &challenges)?
    //                 .into_iter()
    //                 .map(|inner_vec| {
    //                     inner_vec.into_iter()
    //                         .map(fe_to_fe) 
    //                         .collect_vec()
    //                 })
    //                 .map(MultilinearPolynomial::new)
    //                 .collect_vec();
    
    //     assert_eq!(polys.len(), *num_witness_polys);
    //     end_timer(timer);

    //     Ok(polys)
    // }