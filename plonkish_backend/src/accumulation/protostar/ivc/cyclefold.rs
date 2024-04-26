use halo2_base::{halo2_proofs::
    {plonk::{Circuit, Error, ConstraintSystem}, 
    dev::MockProver, 
    arithmetic::Field,
    halo2curves::group::prime::PrimeCurveAffine,
    circuit::{SimpleFloorPlanner, Layouter}}, 
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
    gates::{circuit::{builder::{BaseCircuitBuilder, self}, BaseCircuitParams, CircuitBuilderStage, BaseConfig}, GateInstructions, flex_gate::threads::SinglePhaseCoreManager}, AssignedValue, poseidon::hasher::{spec::OptimizedPoseidonSpec, PoseidonSponge, PoseidonHash}};
use halo2_ecc::{ecc::EcPoint, bigint::ProperCrtUint};
use itertools::Itertools;
use core::{borrow::Borrow, marker::PhantomData};
use std::{iter, time::Instant, cell::RefCell};
use super::halo2::test::strawman::{self, T, RANGE_BITS, RATE, NUM_CHALLENGE_BITS, NUM_LIMBS, NUM_LIMB_BITS, R_F, R_P, SECURE_MDS, NUM_HASH_BITS};
use super::halo2::test::strawman::{Chip, PoseidonTranscriptChip, fe_to_limbs, into_coordinates};
use ivc::ProtostarAccumulationVerifierParam;
use crate::{util::{
    end_timer, 
    transcript::{TranscriptRead, TranscriptWrite},
    arithmetic::{PrimeFieldBits, CurveAffine, TwoChainCurve, fe_to_fe, fe_from_bits_le, fe_to_bits_le, fe_truncated}, izip_eq, start_timer}, 
    accumulation::{PlonkishNarkInstance, protostar::{ProtostarAccumulatorInstance, ivc, ProtostarStrategy::{Compressing, NoCompressing}}}, frontend::halo2::CircuitExt, backend::PlonkishCircuit, poly::multilinear::MultilinearPolynomial};
use rand::RngCore;

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
    pub tcc_chip: Chip<C>,
    pub primary_avp: ProtostarAccumulationVerifierParam<C::Scalar>,
    pub hash_config: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    pub transcript_config: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    pub inputs: CycleFoldInputs<C::Scalar, C::Secondary>,
    pub circuit_builder: RefCell<BaseCircuitBuilder<C::Scalar>>,
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
        let poseidon_spec = OptimizedPoseidonSpec::new::<R_F, R_P, SECURE_MDS>();
        let hash_config = poseidon_spec.clone();
        let transcript_config = poseidon_spec.clone(); 

        let num_witness_comm = primary_avp.num_folding_witness_polys();
        let num_cross_comms = match primary_avp.strategy {
            NoCompressing => primary_avp.num_cross_terms,
            Compressing => 1
        };

        let circuit_builder = RefCell::new(BaseCircuitBuilder::<C::Scalar>::from_stage(CircuitBuilderStage::Mock).use_params(builder_params.clone()));
        let range_chip = circuit_builder.borrow().range_chip();
        let tcc_chip = Chip::<C>::create(range_chip);

        let inputs = 
            CycleFoldInputs::<C::Scalar, C::Secondary>{
                r_le_bits: fe_to_bits_le(C::Scalar::ZERO).into_iter().take(NUM_CHALLENGE_BITS).collect_vec(), 
                nark_witness_comms: vec![C::Secondary::identity(); num_witness_comm],
                cross_term_comms: vec![C::Secondary::identity(); num_cross_comms],
                acc_witness_comms: vec![C::Secondary::identity(); num_witness_comm],
                acc_e_comm: C::Secondary::identity(),
                acc_prime_witness_comms: vec![C::Secondary::identity(); num_witness_comm],
                acc_prime_e_comm: C::Secondary::identity(),
            };

        Self {
            tcc_chip,
            primary_avp: primary_avp.clone(),
            hash_config,
            transcript_config,
            inputs,
            circuit_builder,
        }
    }

    pub fn init(&mut self, vp_digest: C::Scalar) {
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
    

    pub fn assign_cyclefold_inputs(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
    ) -> Result<AssignedCycleFoldInputs<
        AssignedValue<C::Scalar>,
        EcPoint<C::Scalar, AssignedValue<C::Scalar>>>, Error> 
    {
        let tcc_chip = &self.tcc_chip;
        let inputs = &self.inputs;

        let r_le_bits = inputs.r_le_bits
            .iter()
            .map(|bit| tcc_chip.assign_witness(builder, *bit))
            .try_collect::<_, Vec<_>, _>()?;
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
            r_le_bits,
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
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        assigned_inputs: &AssignedCycleFoldInputs<
            AssignedValue<C::Scalar>, 
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
        ) -> Result<(), Error> 
    {
        let tcc_chip = &self.tcc_chip;
        let r_le_bits = &assigned_inputs.r_le_bits;
        let r_nark_witness_comms = assigned_inputs
            .nark_witness_comms
            .iter()
            .map(|comm| tcc_chip.scalar_mul_primary(builder, comm, &r_le_bits))
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
                    e_comm = tcc_chip.scalar_mul_primary(builder, &e_comm, &r_le_bits)?;
                    e_comm = tcc_chip.add_primary(builder, &e_comm, item)?;
                }
                end_timer(timer);
                e_comm
        };

        izip_eq!(&acc_prime_witness_comms, &assigned_inputs.acc_prime_witness_comms)
            .map(|(lhs, rhs)| {
                tcc_chip.constrain_equal_primary(builder, lhs, rhs);
            }).collect_vec();

        tcc_chip.constrain_equal_primary(builder, &acc_prime_e_comm, &assigned_inputs.acc_prime_e_comm)?;

        Ok(())
    }

    
    pub fn hash_inputs(
        &self,
        vp_digest: C::Scalar,
        unassigned_inputs: &CycleFoldInputs<C::Scalar, C::Secondary>
    ) -> C::Scalar {
        let spec = &self.hash_config;
        let mut poseidon = PoseidonHash::from_spec(spec.clone());
        let inputs = iter::empty()
            .chain([vp_digest])
            .chain([fe_from_bits_le(unassigned_inputs.r_le_bits.clone())])
            .chain(
                unassigned_inputs.nark_witness_comms
                    .iter()
                    .flat_map(into_coordinates))
            .chain(
                unassigned_inputs.cross_term_comms
                    .iter()
                    .flat_map(into_coordinates))
            .chain(
                unassigned_inputs.acc_witness_comms
                    .iter()
                    .flat_map(into_coordinates))  
            .chain(into_coordinates(&unassigned_inputs.acc_e_comm).into_iter())                     
            .collect_vec();
        poseidon.update(inputs.as_slice());
        fe_truncated(poseidon.squeeze(), NUM_HASH_BITS)
    }


    pub fn hash_assigned_inputs(
        &self,
        builder: &mut SinglePhaseCoreManager<C::Scalar>,
        r: &AssignedValue<C::Scalar>,
        vp_digest: &AssignedValue<C::Scalar>,
        assigned_inputs: &AssignedCycleFoldInputs<
            AssignedValue<C::Scalar>, 
            EcPoint<C::Scalar, AssignedValue<C::Scalar>>>,
    ) -> Result<AssignedValue<C::Scalar>, Error> {
        let inputs = iter::empty()
            .chain([vp_digest])
            .chain([r])
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
            .copied()
            .collect_vec();
        let mut poseidon_chip = PoseidonSponge::<C::Scalar, T, RATE>::new::<R_F, R_P, SECURE_MDS>(builder.main());
        poseidon_chip.update(&inputs);
        let hash = poseidon_chip.squeeze(builder.main(), &self.tcc_chip.gate_chip);
        // change to strict
        let hash_le_bits = self.tcc_chip.gate_chip.num_to_bits(builder.main(), hash, RANGE_BITS);
        Ok(self.tcc_chip.gate_chip.bits_to_num(builder.main(), &hash_le_bits[..NUM_HASH_BITS]))
    }


    pub fn synthesize_circuit(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        config: BaseConfig<C::Scalar>,
    ) -> Result<(), Error> 
    {
        let tcc_chip = &self.tcc_chip;
        let mut binding = self.circuit_builder.borrow_mut();
        let builder = binding.pool(0);
        let assigned_inputs = self.assign_cyclefold_inputs(builder)?;
        self.compute_and_constrain(builder, &assigned_inputs)?;

        let r = tcc_chip.gate_chip.bits_to_num(builder.main(), &assigned_inputs.r_le_bits[..NUM_CHALLENGE_BITS]);
        let vp_digest = tcc_chip.assign_witness(builder, self.primary_avp.vp_digest)?;
        let inputs_hash = self.hash_assigned_inputs(builder, &r, &vp_digest,  &assigned_inputs)?;
        
        let assigned_instances = &mut binding.assigned_instances;
        assert_eq!(assigned_instances.len(), 1, "CycleFoldCircuit must have exactly 1 instance column");
        assert!(assigned_instances[0].is_empty());

        assigned_instances[0].push(inputs_hash);

        // let instances = self.instances();
        // MockProver::run(17, &*binding, instances.clone()).unwrap().assert_satisfied();

        binding.synthesize(config.clone(), layouter.namespace(|| "cyclefold_circuit"));
        let total_lookup = binding.statistics().total_lookup_advice_per_phase;
        // println!("cyclefold_circuit_advice_lookup {:?}", total_lookup);
        let copy_manager = binding.pool(0).copy_manager.lock().unwrap();
        // println!("cyclefold_circuit_copy_manager.advice_equalities {:?}", copy_manager.advice_equalities.len());
        // println!("cyclefold_circuit_copy_manager.constant_equalities {:?}", copy_manager.constant_equalities.len());
        // println!("cyclefold_circuit_copy_manager.assigned_advices {:?}", copy_manager.assigned_advices.len());
        drop(copy_manager);

        binding.clear();
        drop(binding);

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
            primary_avp: self.primary_avp.clone(),
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
        // println!("Time for synthesize_ec: {:?}", duration_ec_synthesize);
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
        instances[0][0] = self.hash_inputs(self.primary_avp.vp_digest, &self.inputs);
        instances
    }

    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}
