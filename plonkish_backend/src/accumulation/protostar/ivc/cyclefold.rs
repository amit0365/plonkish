use halo2_base::{halo2_proofs::
    {plonk::{Circuit, Error, ConstraintSystem}, 
    dev::MockProver, 
    arithmetic::Field,
    halo2curves::group::prime::PrimeCurveAffine,
    circuit::{SimpleFloorPlanner, Layouter}}, 
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
    gates::circuit::{builder::{BaseCircuitBuilder, self}, BaseCircuitParams, CircuitBuilderStage, BaseConfig}, AssignedValue, poseidon::hasher::spec::OptimizedPoseidonSpec};
use halo2_ecc::{ecc::EcPoint, bigint::ProperCrtUint};
use itertools::Itertools;
use core::{borrow::Borrow, marker::PhantomData};
use std::{iter, time::Instant, cell::RefCell};
use super::halo2::test::strawman::{self, T, RANGE_BITS, RATE, NUM_CHALLENGE_BITS, NUM_LIMBS, NUM_LIMB_BITS, R_F, R_P, SECURE_MDS};
use super::halo2::test::strawman::{Chip, PoseidonTranscriptChip, fe_to_limbs, into_coordinates};
use ivc::{ProtostarAccumulationVerifierParam};
use crate::{util::{
    end_timer, 
    transcript::{TranscriptRead, TranscriptWrite},
    arithmetic::{PrimeFieldBits, CurveAffine, TwoChainCurve, fe_to_fe}, izip_eq, start_timer}, 
    accumulation::{PlonkishNarkInstance, protostar::{ProtostarAccumulatorInstance, ivc, ProtostarStrategy}}, frontend::halo2::CircuitExt, backend::PlonkishCircuit, poly::multilinear::MultilinearPolynomial};
use rand::RngCore;

// public inputs length for the CycleFoldInputs for compressing 
pub const CF_IO_LEN: usize = 42;

pub type AssignedCycleFoldInputs<AssignedBase, AssignedSecondary> =
    CycleFoldInputs<AssignedBase, AssignedSecondary>;

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

// impl<C> CycleFoldInputs<C::Base, C::Secondary> 
// where
//     C: TwoChainCurve,
//     C::Secondary: CurveAffine,
//     C::Scalar: BigPrimeField + PrimeFieldBits,
//     C::Base: BigPrimeField + PrimeFieldBits,
// {
//     pub fn default() -> Self {
//         Self {
//             r: C::Base::ZERO,
//             nark_witness_comms: vec![C::Secondary::identity()],
//             cross_term_comms: vec![C::Secondary::identity()],
//             acc_witness_comms: vec![C::Secondary::identity()],
//             acc_e_comm: C::Secondary::identity(),
//             acc_prime_witness_comms: vec![C::Secondary::identity()],
//             acc_prime_e_comm: C::Secondary::identity(),
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
    pub inputs: CycleFoldInputs<C::Base, C::Secondary>,
    pub circuit_builder: RefCell<BaseCircuitBuilder<C::Scalar>>,
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

        let circuit_builder = RefCell::new(BaseCircuitBuilder::<C::Scalar>::from_stage(CircuitBuilderStage::Mock).use_params(builder_params.clone()));
        let range_chip = circuit_builder.borrow().range_chip();
        let tcc_chip = Chip::<C>::create(range_chip);

        let inputs = CycleFoldInputs::<C::Base, C::Secondary>{
                        r: C::Base::ZERO,
                        nark_witness_comms: vec![C::Secondary::identity()],
                        cross_term_comms: vec![C::Secondary::identity()],
                        acc_witness_comms: vec![C::Secondary::identity()],
                        acc_e_comm: C::Secondary::identity(),
                        acc_prime_witness_comms: vec![C::Secondary::identity()],
                        acc_prime_e_comm: C::Secondary::identity(),
                    };

        Self {
            tcc_chip,
            avp: avp.clone().unwrap_or_default(),
            hash_config,
            transcript_config,
            inputs,
            circuit_builder,
        }
    }

    pub fn init(&mut self, vp_digest: C::Scalar) {
        assert_eq!(&self.avp.num_instances, &[CF_IO_LEN]);
        self.avp.vp_digest = vp_digest;
    }


    // pub fn update_cyclefold_inputs<
    //     Comm: AsRef<C::Secondary>, 
    // >(
    //     &mut self,
    //     r: C::Base,
    //     cross_term_comms: vec![C::identity()],
    //     primary_nark: ProtostarAccumulatorInstance<C::Base, Comm>,
    //     acc: ProtostarAccumulatorInstance<C::Base, Comm>,
    //     acc_prime: ProtostarAccumulatorInstance<C::Base, Comm>,
    // ) {
    //     self.inputs = CycleFoldInputs::<C::Base, C::Secondary>{
    //         r,
    //         nark_witness_comms: primary_nark.witness_comms.iter().map(AsRef::as_ref).cloned().collect_vec(),
    //         cross_term_comms: cross_term_comms.iter().map(AsRef::as_ref).cloned().collect_vec(),
    //         acc_witness_comms: acc.witness_comms.iter().map(AsRef::as_ref).cloned().collect_vec(),
    //         acc_e_comm: *acc.e_comm.as_ref(),
    //         acc_prime_witness_comms: acc_prime.witness_comms.iter().map(AsRef::as_ref).cloned().collect_vec(),
    //         acc_prime_e_comm: *acc_prime.e_comm.as_ref(),
    //     };
    // }

    pub fn update_cyclefold_inputs<Comm: AsRef<C::Secondary>>(
        &mut self,
        r: C::Base,
        cross_term_comms: Vec<Comm>,
        primary_nark: ProtostarAccumulatorInstance<C::Base, Comm>,
        acc: ProtostarAccumulatorInstance<C::Base, Comm>,
        acc_prime: ProtostarAccumulatorInstance<C::Base, Comm>,
    ) {
        let convert_vec_comms = |comms: &[Comm]| comms.iter().map(AsRef::as_ref).cloned().collect_vec();
        self.inputs = CycleFoldInputs::<C::Base, C::Secondary> {
            r,
            nark_witness_comms: convert_vec_comms(&primary_nark.witness_comms),
            cross_term_comms: convert_vec_comms(&cross_term_comms),
            acc_witness_comms: convert_vec_comms(&acc.witness_comms),
            acc_e_comm: *acc.e_comm.as_ref(),
            acc_prime_witness_comms: convert_vec_comms(&acc_prime.witness_comms),
            acc_prime_e_comm: *acc_prime.e_comm.as_ref(),
        };
    }
    

    pub fn assign_cyclefold_inputs(
        &self,
        circuit_builder: &mut BaseCircuitBuilder<C::Scalar>,
    ) -> Result<AssignedCycleFoldInputs<
            ProperCrtUint<C::Scalar>, 
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
            Error> 
    {
        let tcc_chip = &self.tcc_chip;
        let builder = circuit_builder.pool(0);
        let inputs = &self.inputs;

        let r = tcc_chip.assign_witness_base(builder, inputs.r)?;
        let nark_witness_comms = inputs.nark_witness_comms
            .iter()
            .map(|comm| tcc_chip.assign_witness_primary(builder, *comm))
            .try_collect::<_, Vec<_>, _>()?; 
        let cross_term_comms = inputs.cross_term_comms
            .iter()
            .map(|comm| tcc_chip.assign_witness_primary(builder, *comm))
            .try_collect::<_, Vec<_>, _>()?; 

        let acc_e_comm = tcc_chip.assign_witness_primary(builder, inputs.acc_e_comm)?;
        let acc_witness_comms = inputs.acc_witness_comms
            .iter()
            .map(|comm| tcc_chip.assign_witness_primary(builder, *comm))
            .try_collect::<_, Vec<_>, _>()?; 
        
        let acc_prime_e_comm = tcc_chip.assign_witness_primary(builder, inputs.acc_prime_e_comm)?;
        let acc_prime_witness_comms = inputs.acc_prime_witness_comms
            .iter()
            .map(|comm| tcc_chip.assign_witness_primary(builder, *comm))
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
        &self, 
        circuit_builder: &mut BaseCircuitBuilder<C::Scalar>,
        assigned_inputs: &AssignedCycleFoldInputs<
            ProperCrtUint<C::Scalar>, 
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        ) -> Result<(), Error> 
    {
        let tcc_chip = &self.tcc_chip;
        let builder = circuit_builder.pool(0);

        let r = &assigned_inputs.r;
        let r_nark_witness_comms = assigned_inputs
            .nark_witness_comms
            .iter()
            .map(|comm| tcc_chip.scalar_mul_primary(builder, comm, &r))
            .try_collect::<_, Vec<_>, _>()?;

        let acc_prime_witness_comms = 
            izip_eq!(&assigned_inputs.acc_witness_comms, &r_nark_witness_comms)
            .map(|(lhs, rhs)| 
            tcc_chip.add_primary(builder, lhs, rhs))
            .try_collect::<_, Vec<_>, _>()?;

        let acc_prime_e_comm = if assigned_inputs.cross_term_comms.is_empty() {
            assigned_inputs.acc_e_comm.clone()
        } else {
            let timer = start_timer(|| format!("cyclefold_compute_e_comm-cross_term_comms.len()-{}", assigned_inputs.cross_term_comms.len()));
            let mut e_comm = assigned_inputs.cross_term_comms.last().unwrap().clone();
                for item in assigned_inputs.cross_term_comms.iter().rev().skip(1).chain([&assigned_inputs.acc_e_comm]) {
                    e_comm = tcc_chip.scalar_mul_primary(builder, &e_comm, &r)?;
                    e_comm = tcc_chip.add_primary(builder, &e_comm, item)?;
                }
                end_timer(timer);
                e_comm
        };

        // constrains scalar_mul natively in circuit
        izip_eq!(&acc_prime_witness_comms, &assigned_inputs.acc_prime_witness_comms)
            .map(|(lhs, rhs)| {
                tcc_chip.constrain_equal_primary(builder, lhs, rhs);
            });

        tcc_chip.constrain_equal_primary(builder, &acc_prime_e_comm, &assigned_inputs.acc_prime_e_comm)?;

        Ok(())
    }

    // pub fn flatten_inputs(
    //     assigned_inputs: &CycleFoldInputs<C::Scalar, C::Secondary>
    // ) -> Result<Vec<C::Base>, Error> {
    //     let fe_to_limbs = |fe| fe_to_limbs::<C::Scalar, C::Base>(fe, NUM_LIMB_BITS);
    //     let inputs = iter::empty()
    //         .chain(fe_to_limbs(assigned_inputs.r))
    //         .chain(
    //             assigned_inputs.nark_witness_comms
    //                 .iter()
    //                 .flat_map(into_coordinates))
    //         .chain(
    //             assigned_inputs.cross_term_comms
    //                 .iter()
    //                 .flat_map(into_coordinates))
    //         .chain(
    //             assigned_inputs.acc_witness_comms
    //                 .iter()
    //                 .flat_map(into_coordinates))  
    //         .chain(into_coordinates(&assigned_inputs.acc_e_comm))              
    //         .chain(
    //             assigned_inputs.acc_prime_witness_comms
    //                 .iter()
    //                 .flat_map(into_coordinates))
    //         .chain(into_coordinates(&assigned_inputs.acc_prime_e_comm))              
    //         .collect_vec();

    //     Ok(inputs)
    // }

    pub fn flatten_assigned_inputs(
        &self,
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
        let mut builder = self.circuit_builder.borrow_mut();
        let assigned_inputs = self.assign_cyclefold_inputs(&mut builder)?;
        // check scalar_mul 
        self.compute_and_constrain(&mut builder, &assigned_inputs)?;
        let flattened_assigned_inputs = self.flatten_assigned_inputs(&assigned_inputs)?;
        assert_eq!(flattened_assigned_inputs.len(), CF_IO_LEN, "CycleFoldInputs must have exactly 38 elements");

        let assigned_instances = &mut builder.assigned_instances;
        assert_eq!(assigned_instances.len(), 1, "CycleFoldCircuit must have exactly 1 instance column");
        assert!(assigned_instances[0].is_empty());

        assigned_instances[0].extend(flattened_assigned_inputs);


        let instances = self.instances();
        MockProver::run(14, &*builder, instances.clone()).unwrap().assert_satisfied();

        builder.synthesize(config.clone(), layouter.namespace(|| "cyclefold_circuit"));

        // let copy_manager = builder.copy_manager.lock().unwrap();
        // println!("cyclefold_circuit_copy_manager.advice_equalities {:?}", copy_manager.advice_equalities.len());
        // println!("cyclefold_circuit_copy_manager.constant_equalities {:?}", copy_manager.constant_equalities.len());
        // println!("cyclefold_circuit_copy_manager.assigned_constants {:?}", copy_manager.assigned_constants.len());
        // println!("cyclefold_circuit_copy_manager.assigned_advices {:?}", copy_manager.assigned_advices.len());
        // drop(copy_manager);


        builder.clear();
        drop(builder);

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
        // let inputs = &self.inputs;
        // let instances = CycleFoldCircuit::<C>::flatten_inputs(inputs).unwrap();
        // vec![instances]
        unimplemented!()
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