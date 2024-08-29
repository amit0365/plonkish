use itertools::Itertools;
use rand::{rngs::OsRng, RngCore};
use std::{iter, marker::PhantomData, os::macos::raw::stat, time::Instant};
use halo2_base::{halo2_proofs::{circuit::{floor_planner::V1, AssignedCell, Layouter, SimpleFloorPlanner, Value}, dev::MockProver, halo2curves::bn256, plonk::{Circuit, ConstraintSystem}}, utils::{BigPrimeField, FromUniformBytes, PrimeField}};
use halo2_gadgets::poseidon::{primitives::{ConstantLength, Hash, Spec}, spec::PoseidonSpec, PoseidonSpongeChip, Pow5Chip, Pow5Config}; 
use halo2_base::halo2_proofs::plonk::Error;
use halo2_base::halo2_proofs::halo2curves::ff::PrimeFieldBits;
use halo2_base::halo2_proofs::arithmetic::Field;
use crate::{accumulation::protostar::ivc::{halo2::{chips::{main_chip::{EcPointNative, NonNativeNumber, NUM_LIMBS_NON_NATIVE, NUM_LIMBS_PRIMARY_NON_NATIVE, NUM_LIMB_BITS_NON_NATIVE, NUM_LIMB_BITS_PRIMARY_NON_NATIVE, NUM_MAIN_ADVICE}, poseidon::hash_chip::PoseidonConfig, range_check::{RangeCheckChip, RangeCheckConfig}, transcript::{NUM_HASH_BITS, RANGE_BITS}}, cyclefold::CF_IO_LEN, test::TrivialCircuit, ProtostarAccumulationVerifier, StepCircuit}, ProtostarAccumulationVerifierParam}, frontend::halo2::CircuitExt, util::{arithmetic::{fe_from_bits_le, fe_to_fe, fe_to_limbs, fe_truncated, into_coordinates}, izip_eq}};
use crate::accumulation::protostar::{ivc::halo2::chips::{main_chip::{EcPointNonNative, Number}, transcript::{native::AssignedProtostarAccumulatorInstance, nonnative::PoseidonTranscriptChip}}, ProtostarStrategy::Compressing};
use crate::{
    accumulation::{protostar::{ivc::halo2::chips::{poseidon::hash_chip::PoseidonChip, scalar_mul::sm_chip_primary::{ScalarMulChip, ScalarMulChipConfig}, main_chip::{MainChip, MainChipConfig}, transcript::native::PoseidonNativeTranscriptChip}, ProtostarAccumulatorInstance}, PlonkishNarkInstance}, 
    util::arithmetic::{powers, TwoChainCurve}
};
use poseidon2::circuit::{primitives::{ConstantLength as ConstantLength2, Hash as Hash2}, pow5::{Pow5Chip as Poseidon2Pow5Chip, Pow5Config as Poseidon2Pow5Config}};
//use poseidon::{Spec as PoseidonSpec, Poseidon as PoseidonInlineHash};
use poseidon2::circuit::spec::PoseidonSpec as Poseidon2ChipSpec;
use halo2_gadgets::poseidon::spec::PoseidonSpec as PoseidonChipSpec;
use crate::accumulation::protostar::ivc::halo2::chips::poseidon::hash_chip::{Poseidon2Chip, Poseidon2Config};
use crate::accumulation::protostar::ivc::halo2::chips::{T as T2, R as R2};

pub const T: usize = 8;
pub const RATE: usize = 7;
pub const NUM_RANGE_COLS: usize = (T + 1) / 2;

pub const PRIMARY_HASH_LENGTH: usize = 29; //35 - 4limbs
pub const CF_HASH_LENGTH: usize = 13;

pub const N_BYTES: usize = 16;
pub const R_F: usize = 8;
pub const R_P: usize = 56;
pub const SECURE_MDS: usize = 0;
pub const NUM_INSTANCES: usize = 1;


#[derive(Clone, Debug)]
pub struct PrimaryCircuitConfig<C> 
    where
    C: TwoChainCurve,
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    poseidon_config: Pow5Config<C::Scalar, T, RATE>,
    main_config: MainChipConfig,
    sm_chip_config: ScalarMulChipConfig<C>,
    range_check_config: RangeCheckConfig,
    // transcript_config: PoseidonTranscriptChipConfig,
    // avp_config: AVPConfig,
}

impl<C: TwoChainCurve> PrimaryCircuitConfig<C> 
    where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    pub fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self {

        let state = (0..T).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let partial_sbox = meta.advice_column();

        let rc_a = (0..T).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        let rc_b = (0..T).map(|_| meta.fixed_column()).collect::<Vec<_>>();

        meta.enable_constant(rc_b[0]);

        let poseidon_config = Pow5Chip::configure::<PoseidonChipSpec>(
            meta,
            state.clone().try_into().unwrap(),
            partial_sbox,
            rc_a.clone().try_into().unwrap(),
            rc_b.clone().try_into().unwrap(),
        );

        let mut main_advice = state.clone();
        main_advice.push(partial_sbox);
        let mut main_fixed = rc_a;
        main_fixed.extend(rc_b);

        for col in main_fixed.iter() {
            meta.enable_constant(*col);
        }

        for col in main_advice.iter() {
            meta.enable_equality(*col);
        }  

        let main_config = MainChip::<C>::configure(meta, main_advice.clone().try_into().unwrap(), main_fixed.try_into().unwrap());
        let sm_advice = main_advice.iter().skip(2).cloned().collect_vec();
        for col in sm_advice.iter() {
            meta.enable_equality(*col);
        }

        let sm_chip_config = ScalarMulChipConfig::configure(meta, sm_advice.try_into().unwrap());

        let range_check_fixed = meta.fixed_column();
        let enable_lookup_selector = meta.complex_selector();
        let range_check_config = RangeCheckChip::<C>::configure(
            meta,
            main_advice[T],
            range_check_fixed,
            enable_lookup_selector,
        );

        Self {
            poseidon_config,
            main_config,
            sm_chip_config,
            range_check_config,
        }
    }
}

#[derive(Clone, Debug)]
pub struct PrimaryCircuit<C, Sc> 
    where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    is_primary: bool,
    step_circuit: Sc,
    pub hash_config: PoseidonSpec,//<C::Scalar, T, RATE>,
    pub cyclefold_hash_config: PoseidonSpec,//<C::Base, T2, R2>,
    // hash_config_base: PoseidonSpec,
    // transcript_config: PoseidonSpec,
    pub primary_avp: ProtostarAccumulationVerifierParam<C::Scalar>,
    pub cyclefold_avp: ProtostarAccumulationVerifierParam<C::Scalar>,
    h_prime: Value<C::Scalar>,
    cyclefold_inputs_hash: Value<C::Base>,
    acc: Value<ProtostarAccumulatorInstance<C::Scalar, C>>,
    acc_prime: Value<ProtostarAccumulatorInstance<C::Scalar, C>>,
    primary_instances: [Value<C::Scalar>; NUM_INSTANCES],
    primary_proof: Value<Vec<u8>>,
    cyclefold_instances: [Value<C::Base>; CF_IO_LEN],
    cyclefold_proof: Value<Vec<u8>>,
    acc_ec: Value<ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
    acc_prime_ec: Value<ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
}

impl<C, Sc> PrimaryCircuit<C, Sc> 
    where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    pub type Num = Number<C::Scalar>;
    pub type NonNatNum = NonNativeNumber<C::Scalar>;
    pub type Ecc = EcPointNonNative<C>;
    pub type NatEcc = EcPointNative<C>;

    pub fn new(
        is_primary: bool,
        step_circuit: Sc,
        primary_avp: Option<ProtostarAccumulationVerifierParam<C::Scalar>>,
        cyclefold_avp: Option<ProtostarAccumulationVerifierParam<C::Scalar>>,
    ) -> Self {
        // let poseidon_spec = OptimizedPoseidonSpec::<C::Scalar, T, RATE>::new::<R_F, R_P, SECURE_MDS>();
        // let hash_config = Spec::<C::Scalar, T, RATE>::new(R_F, R_P);
        // let cyclefold_hash_config = Spec::<C::Base, T2, R2>::new(R_F, R_P);
        let hash_config = PoseidonSpec;
        let cyclefold_hash_config = PoseidonSpec;
        // let poseidon_spec_base = OptimizedPoseidonSpec::<C::Base, T, RATE>::new::<R_F, R_P, SECURE_MDS>();
        // let hash_config_base = poseidon_spec_base.clone();
        // let transcript_config = poseidon_spec.clone();

        Self {
                is_primary,
                step_circuit,
                hash_config,
                cyclefold_hash_config,
                // hash_config_base,
                // transcript_config,
                primary_avp: primary_avp.clone().unwrap_or_default(),
                cyclefold_avp: cyclefold_avp.clone().unwrap_or_default(),
                h_prime: Value::known(C::Scalar::ZERO),
                cyclefold_inputs_hash: Value::known(C::Base::ZERO),
                acc: Value::known(primary_avp.clone().unwrap_or_default().init_accumulator()),
                acc_prime: Value::known(primary_avp.clone().unwrap_or_default().init_accumulator()),
                primary_instances: [Value::known(C::Scalar::ZERO); NUM_INSTANCES],
                primary_proof: Value::known(PoseidonNativeTranscriptChip::<C>::dummy_proof(&primary_avp.clone().unwrap_or_default())),
                cyclefold_instances: [Value::known(C::Base::ZERO); CF_IO_LEN],
                cyclefold_proof: Value::known(PoseidonTranscriptChip::<C>::dummy_proof(&cyclefold_avp.clone().unwrap_or_default())),
                acc_ec: Value::known(cyclefold_avp.clone().unwrap_or_default().init_accumulator()),
                acc_prime_ec: Value::known(cyclefold_avp.clone().unwrap_or_default().init_accumulator()),
            }
    }

        pub fn hash_cyclefold_inputs<Comm: AsRef<C>>(
            &self,
            //spec: &PoseidonSpec,
            vp_digest: C::Scalar,
            r_le_bits: Vec<C::Scalar>,
            primary_nark_witness_comm: Vec<Comm>,
            cross_term_comms: Vec<Comm>,
            acc: &ProtostarAccumulatorInstance<C::Scalar, Comm>,
        ) -> C::Base {
            let mut poseidon = Hash::<_, PoseidonSpec, ConstantLength<CF_HASH_LENGTH>, T, RATE>::init(); // PoseidonHash::from_spec(spec.clone());
            //let mut poseidon = PoseidonInlineHash::<C::Base, T2, R2>::new_with_spec(self.cyclefold_hash_config.clone());
            let inputs = iter::empty()
                //.chain([fe_to_fe(vp_digest)])
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
                .collect_vec();

            // let message: [C::Base; CF_HASH_LENGTH] =
            // match inputs.try_into() {
            //     Ok(arr) => arr,
            //     Err(_) => panic!("Failed to convert Vec to Array"),
            // };
            // assert_eq!(CF_HASH_LENGTH, message.len());
            // poseidon.update(&message);
            // let hash = poseidon.squeeze();     
            let hash = poseidon.hash(inputs.try_into().unwrap());
            fe_truncated(hash, NUM_HASH_BITS)
        }

        pub fn hash_state<Comm: AsRef<C>>(
            &self,
            //spec: &PoseidonSpec,
            vp_digest: C::Scalar,
            step_idx: usize,
            initial_input: &[C::Scalar],
            output: &[C::Scalar],
            acc: &ProtostarAccumulatorInstance<C::Scalar, Comm>,
        ) -> C::Scalar {
            let mut poseidon = Hash::<_, PoseidonSpec, ConstantLength<PRIMARY_HASH_LENGTH>, T, RATE>::init();
            //let mut poseidon = PoseidonInlineHash::<C::Scalar, T, RATE>::new_with_spec(self.hash_config.clone());
            let fe_to_limbs = |fe| fe_to_limbs(fe, NUM_LIMB_BITS_NON_NATIVE, NUM_LIMBS_NON_NATIVE);
            let inputs = iter::empty()
                .chain([vp_digest, C::Scalar::from(step_idx as u64)])
                .chain(initial_input.iter().copied())
                .chain(output.iter().copied())
                .chain([acc.instances[0][0]])
                .chain(acc.witness_comms
                        .iter()
                        .map(AsRef::as_ref)
                        .flat_map(into_coordinates).into_iter().map(fe_to_limbs).flatten(),
                )
                .chain(acc.challenges.iter().copied())
                .chain([acc.u])
                .chain(into_coordinates(acc.e_comm.as_ref()).into_iter().map(fe_to_limbs).flatten())
                .chain(acc.compressed_e_sum.into_iter())
                .collect_vec();
            // let message: [C::Scalar; PRIMARY_HASH_LENGTH] =
            // match inputs.try_into() {
            //     Ok(arr) => arr,
            //     Err(_) => panic!("Failed to convert Vec to Array"),
            // };
            // assert_eq!(PRIMARY_HASH_LENGTH, message.len());
            // poseidon.update(&message);
            // let hash = poseidon.squeeze();
            let hash = poseidon.hash(inputs.try_into().unwrap());
            fe_truncated(hash, NUM_HASH_BITS)
        }

        pub fn hash_assigned_state<
            const L: usize,
        >(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            main_chip: &MainChip<C>,
            mut poseidon_chip: &mut PoseidonChip<C, PoseidonChipSpec, T, RATE, L>,
            vp_digest: &Self::Num,
            step_idx: &Self::Num,
            initial_input: &[Self::Num],
            output: &[Self::Num],
            acc: &AssignedProtostarAccumulatorInstance<
                Self::Num,
                Self::Ecc,
            >,
        ) -> Result<Self::Num, Error> {
            let inputs = iter::empty()
                .chain([vp_digest, step_idx])
                .chain(initial_input)
                .chain(output)
                .chain([&acc.instances[0][0]])
                .chain(
                    acc.witness_comms
                        .iter()
                        .flat_map(|point| point.x.limbs.iter().chain(point.y.limbs.iter())))
                .chain(acc.challenges.iter())
                .chain([&acc.u])
                .chain(acc.e_comm.x.limbs.iter().chain(acc.e_comm.y.limbs.iter()))
                .chain(
                    acc.compressed_e_sum
                        .as_ref()
                        .into_iter())
                .collect_vec();

            let input_cells = inputs.iter().map(|x| x.0.clone()).collect_vec();
            let hash = poseidon_chip.hash(layouter.namespace(|| "hash"), input_cells.try_into().unwrap())?;
            // change to strict - Witness count: 29272
            // let hash_le_bits = main_chip.num_to_bits(layouter, RANGE_BITS, &Number(hash))?;
            // main_chip.bits_to_num(layouter, &hash_le_bits[..NUM_HASH_BITS])
            // Witness count: 28170
            let bits_to_num = main_chip.bits_and_num_limbs_hash(layouter, RANGE_BITS, NUM_HASH_BITS, &Number(hash))?;
            Ok(bits_to_num)
        }

    pub fn update_from_cyclefold<
        Comm_ec: AsRef<C::Secondary>
    >(
        &mut self,
        cyclefold_proof: Vec<u8>,
        cyclefold_instances: [C::Base; CF_IO_LEN],
        acc_ec: ProtostarAccumulatorInstance<C::Base, Comm_ec>,
        acc_prime_ec: ProtostarAccumulatorInstance<C::Base, Comm_ec>,
    ) {
        // self.h_prime_ec = Value::known(Chip::<C>::hash_state_ec(
        //     self.hash_config.borrow(),
        //     self.primary_avp.vp_digest,
        //     &acc_prime_ec,
        // ));
        self.cyclefold_proof = Value::known(cyclefold_proof);
        self.cyclefold_instances = cyclefold_instances.map(Value::known);
        self.acc_ec = Value::known(acc_ec.unwrap_comm());
        self.acc_prime_ec = Value::known(acc_prime_ec.unwrap_comm());
    }

    pub fn update_both_running_instances<
        Comm: AsRef<C>, 
        Comm_ec: AsRef<C::Secondary>
    >(
        &mut self,
        r_le_bits: Vec<C::Scalar>,
        primary_nark_witness_comm: Vec<Comm>,
        cross_term_comms: Vec<Comm>,
        acc: ProtostarAccumulatorInstance<C::Scalar, Comm>,
        acc_prime: ProtostarAccumulatorInstance<C::Scalar, Comm>,
        primary_instances: [C::Scalar; NUM_INSTANCES],
        primary_proof: Vec<u8>,
        acc_ec: ProtostarAccumulatorInstance<C::Base, Comm_ec>,
        acc_prime_ec: ProtostarAccumulatorInstance<C::Base, Comm_ec>,
    ) {
        if (self.is_primary && acc_prime.u != C::Scalar::ZERO)//
            || (!self.is_primary && acc.u != C::Scalar::ZERO)
            {
                self.step_circuit.next();
            }
            self.cyclefold_inputs_hash = Value::known(self.hash_cyclefold_inputs(
                // &self.hash_config_base,
                self.primary_avp.vp_digest,
                r_le_bits,
                primary_nark_witness_comm,
                cross_term_comms,
                &acc,
            ));
            self.h_prime = Value::known(self.hash_state(
                // &self.hash_config,
                self.primary_avp.vp_digest,
                self.step_circuit.step_idx() + 1,
                self.step_circuit.initial_input(),
                self.step_circuit.output(),
                &acc_prime,
            ));

            self.acc = Value::known(acc.unwrap_comm());
            self.acc_ec = Value::known(acc_ec.unwrap_comm());
            self.acc_prime = Value::known(acc_prime.unwrap_comm());
            self.acc_prime_ec = Value::known(acc_prime_ec.unwrap_comm());
            self.primary_instances = primary_instances.map(Value::known);
            self.primary_proof = Value::known(primary_proof);
    }

    pub fn init(&mut self, vp_digest: C::Scalar) {
        //assert_eq!(&self.primary_avp.num_instances, &[NUM_INSTANCES]);
        self.primary_avp.vp_digest = vp_digest;
    }

    pub fn update_acc(&mut self) {
        self.acc = Value::known(self.primary_avp.init_accumulator());
        self.acc_prime = Value::known(self.primary_avp.init_accumulator());
        self.acc_ec = Value::known(self.cyclefold_avp.init_accumulator());
        self.acc_prime_ec = Value::known(self.cyclefold_avp.init_accumulator());
    }

    fn check_initial_condition(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        main_chip: &MainChip<C>,
        is_base_case: &Self::Num,
        initial_input: &[Self::Num],
        input: &[Self::Num],
    ) -> Result<(), Error> {
        let zero = main_chip.assign_fixed(layouter, &C::Scalar::ZERO, 0).unwrap();
        for (lhs, rhs) in input.iter().zip(initial_input.iter()) {
            let lhs = main_chip.select(layouter, is_base_case, lhs, &zero)?;
            let rhs = main_chip.select(layouter, is_base_case, rhs, &zero)?;
            main_chip.constrain_equal(layouter, &lhs, &rhs)?;
        }

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    fn check_state_hash<
        const L: usize,
    >(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        main_chip: &MainChip<C>,
        poseidon_chip: &mut PoseidonChip<C, PoseidonChipSpec, T, RATE, L>,
        is_base_case: Option<&Self::Num>,
        h: &Self::Num,
        vp_digest: &Self::Num,
        step_idx: &Self::Num,
        initial_input: &[Self::Num],
        output: &[Self::Num],
        acc: &AssignedProtostarAccumulatorInstance<
            Self::Num,
            Self::Ecc,
        >,
    ) -> Result<(), Error> {

        let lhs = h;
        let zero = main_chip.assign_witness(layouter, &C::Scalar::ZERO, 0).unwrap();
        let rhs = self.hash_assigned_state(
            layouter,
            main_chip,
            poseidon_chip,
            vp_digest,
            step_idx,
            initial_input,
            output,
            acc,
        )?;
        let rhs = if let Some(is_base_case) = is_base_case {
            main_chip.select(layouter, is_base_case, &zero, &rhs)?
        } else {
            rhs
        };

        // lhs = h == 0 initalised 
        let lhs_is_zero = main_chip.is_zero(layouter, lhs)?;
        let rhs = main_chip.select(layouter, &lhs_is_zero, &zero, &rhs)?;
        //main_chip.constrain_equal(layouter, lhs, &rhs)?; //todo

        Ok(())
    }

    fn check_folding_ec(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        main_chip: &MainChip<C>,
        acc_prime: &AssignedProtostarAccumulatorInstance<
            Self::NonNatNum,
            Self::NatEcc,
        >,
        acc_prime_result: &AssignedProtostarAccumulatorInstance<
            Self::NonNatNum,
            Self::NatEcc,
        >
    ) -> Result<(), Error> {

        let default_compressed_e_sum = main_chip.assign_fixed_base(layouter, &C::Base::ZERO)?;
        izip_eq!(&acc_prime.instances[0], &acc_prime_result.instances[0])
            .map(|(lhs, rhs)| {
             let _ = main_chip.constrain_equal_base(layouter, lhs, rhs);
            }).collect_vec();
        izip_eq!(&acc_prime.witness_comms, &acc_prime_result.witness_comms)
            .map(|(lhs, rhs)| {
             let _ = main_chip.constrain_equal_secondary(layouter, lhs, rhs);
            }).collect_vec();
        izip_eq!(&acc_prime.challenges, &acc_prime_result.challenges)
            .map(|(lhs, rhs)| {
             let _ = main_chip.constrain_equal_base(layouter, lhs, rhs);
            }).collect_vec();

        main_chip.constrain_equal_base(layouter, &acc_prime.u, &acc_prime_result.u)?;
        main_chip.constrain_equal_secondary(layouter, &acc_prime.e_comm, &acc_prime_result.e_comm)?;
        main_chip.constrain_equal_base(layouter, &acc_prime.compressed_e_sum.as_ref().unwrap_or(&default_compressed_e_sum), &acc_prime_result.compressed_e_sum.as_ref().unwrap_or(&default_compressed_e_sum))?;

        Ok(())
    }

    // fn check_folding_ec_hash(
    //     &self,
    //     builder: &mut SinglePhaseCoreManager<C::Scalar>,
    //     is_base_case: Option<&AssignedValue<C::Scalar>>,
    //     vp_digest: &AssignedValue<C::Scalar>,
    //     h_prime: &AssignedValue<C::Scalar>,
    //     acc_prime: &AssignedProtostarAccumulatorInstance<
    //         ProperCrtUint<C::Scalar>,
    //         EcPoint<C::Scalar, AssignedValue<C::Scalar>>,
    //     >,
    // ) -> Result<(), Error> {
    //     let tcc_chip = &self.tcc_chip;
    //     let hash_chip = &self.hash_chip;
    //     let lhs = h_prime;
    //     let rhs = hash_chip.hash_assigned_acc_prime(
    //         builder,
    //         vp_digest,
    //         acc_prime,
    //     )?;
    //     let rhs = if let Some(is_base_case) = is_base_case {
    //         let zero = builder.main().load_zero();
    //         tcc_chip.select_gatechip(builder, is_base_case, &zero, &rhs)?
    //     } else {
    //         rhs
    //     };

    //     // todo check this fails because before prove_steps lhs = h == 0 initalised 
    //     // since axiom api doesn't handle option
    //     if *lhs.value() != C::Scalar::ZERO {
    //         tcc_chip.constrain_equal(builder, lhs, &rhs)?;
    //     }
    //     Ok(())
    // }

}

impl<C, Sc> Circuit<C::Scalar> for PrimaryCircuit<C, Sc> 
    where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{

    type Config = PrimaryCircuitConfig<C>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
        // Self { 
        //     is_primary: false,
        //     step_circuit: self.step_circuit.without_witnesses(),
        //     hash_config: self.hash_config.clone(),
        //     cyclefold_hash_config: self.cyclefold_hash_config.clone(),
        //     // transcript_config: self.transcript_config,
        //     primary_avp: self.primary_avp.clone(),
        //     cyclefold_avp: self.cyclefold_avp.clone(),
        //     h_prime: Value::unknown(),
        //     cyclefold_inputs_hash: Value::unknown(),
        //     acc: Value::unknown(),
        //     acc_prime: Value::unknown(),
        //     primary_instances: [Value::unknown(); NUM_INSTANCES],
        //     primary_proof: Value::unknown(),
        //     cyclefold_instances: [Value::unknown(); CF_IO_LEN],
        //     cyclefold_proof: Value::unknown(),
        //     acc_ec: Value::unknown(),
        //     acc_prime_ec: Value::unknown(),
        //  }
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        PrimaryCircuitConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {

        let Self {
            primary_avp,
            cyclefold_avp,
            ..
        } = &self;

        let (input, output) =
            StepCircuit::synthesize(&self.step_circuit, config.main_config.clone(), layouter.namespace(|| ""))?;

        let range_chip = RangeCheckChip::<C>::construct(config.range_check_config);
        let mut main_chip = MainChip::<C>::new(config.main_config.clone(), range_chip);
        main_chip.initialize(&mut layouter)?;
        main_chip.load_range_check_table(&mut layouter, config.range_check_config.lookup_u8_table)?;
        let pow5_chip = Pow5Chip::construct(config.poseidon_config.clone());
        let sm_chip = ScalarMulChip::<C>::new(config.sm_chip_config.clone());
        let mut hash_chip_primary = PoseidonChip::<C, PoseidonChipSpec, T, RATE, PRIMARY_HASH_LENGTH>::construct(PoseidonConfig { pow5_config: config.poseidon_config.clone()});
        // let mut hash_chip_secondary = PoseidonChip::<C, PoseidonSpec, T, RATE, CF_HASH_LENGTH>::construct(PoseidonConfig { pow5_config: config.poseidon_config.clone()});
        
        let acc_verifier = ProtostarAccumulationVerifier::new(primary_avp.clone(), main_chip.clone(), sm_chip.clone());
        let zero = main_chip.assign_fixed(&mut layouter, &C::Scalar::ZERO, 0)?;
        let one = main_chip.assign_fixed(&mut layouter, &C::Scalar::ONE, 1)?;
        let vp_digest = main_chip.assign_witness(&mut layouter, &primary_avp.vp_digest, 0)?;
        let step_idx = main_chip.assign_witness(
            &mut layouter,
            &C::Scalar::from(self.step_circuit.step_idx() as u64),
            1,
        )?;

        let mut h_prime_val = C::Scalar::ZERO;
        self.h_prime.map(|val| h_prime_val = val);
        let step_idx_plus_one = main_chip.add(&mut layouter, &step_idx, &one)?;
        let h_prime = main_chip.assign_witness(&mut layouter, &h_prime_val, 4)?;
        let initial_input = self
            .step_circuit
            .initial_input()
            .iter()
            .map(|value| main_chip.assign_witness(&mut layouter, value, 5))
            .try_collect::<_, Vec<_>, _>()?;

        let is_base_case = main_chip.is_equal(&mut layouter, &step_idx, &zero)?;
        self.check_initial_condition(&mut layouter, &main_chip, &is_base_case, &initial_input, &input)?;
        let cyclefold_instances = self.cyclefold_instances
            .iter()
            .map(|instance| Value::as_ref(instance))
            .collect_vec();  

        let mut cyclefold_inputs_hash_val = C::Base::ZERO;
        self.cyclefold_inputs_hash.map(|val| cyclefold_inputs_hash_val = val);
        let cyclefold_inputs_hash = main_chip.assign_witness_base(&mut layouter, cyclefold_inputs_hash_val)?;

        let mut cyclefold_inputs_hash_from_instances_val = C::Base::ZERO;
        self.cyclefold_instances[0].map(|val| cyclefold_inputs_hash_from_instances_val = val);
        let cyclefold_inputs_hash_from_instances = main_chip.assign_witness_base(&mut layouter, cyclefold_inputs_hash_from_instances_val)?;
        let cyclefold_inputs_hash_from_instances_select = main_chip.select_base(&mut layouter, &is_base_case, &cyclefold_inputs_hash, &cyclefold_inputs_hash_from_instances)?;
        main_chip.constrain_equal_base(&mut layouter, &cyclefold_inputs_hash, &cyclefold_inputs_hash_from_instances_select)?;

        let acc = acc_verifier.assign_accumulator(&mut layouter, self.acc.as_ref())?;
        let assigned_acc_prime_comms_checked = acc_verifier.assign_comm_outputs_from_accumulator(&mut layouter, self.acc_prime.as_ref())?;
        let (nark, acc_prime) = {
            let instances =
                [&self.primary_instances[0]].map(Value::as_ref);  
            let proof = self.primary_proof.clone();
            let native_transcript_chip = 
                &mut PoseidonNativeTranscriptChip::<C>::new(&mut layouter, pow5_chip.clone(), PoseidonSpec, main_chip.clone(), proof);

            acc_verifier.verify_accumulation_from_nark(&mut layouter, &acc, instances, native_transcript_chip, assigned_acc_prime_comms_checked)? 
        };

        let acc_prime = {
            let acc_default = acc_verifier.assign_default_accumulator(&mut layouter)?;
            acc_verifier.select_accumulator(&mut layouter, &is_base_case, &acc_default, &acc_prime)?
        };

        // Witness count: 14563 - 7762 = 6801
        // check if nark.instances[0][0] = Hash(inputs, acc)
        self.check_state_hash::<PRIMARY_HASH_LENGTH>(
            &mut layouter,
            &main_chip,
            &mut hash_chip_primary,
            Some(&is_base_case),
            &nark.instances[0][0],
            &vp_digest,
            &step_idx,
            &initial_input,
            &input,
            &acc,
        )?;

        // checks if folding was done correctly
        // h_prime = Hash(inputs, acc_prime)
        self.check_state_hash::<PRIMARY_HASH_LENGTH>(
            &mut layouter,
            &main_chip,
            &mut hash_chip_primary,
            None,
            &h_prime,
            &vp_digest,
            &step_idx_plus_one,
            &initial_input,
            &output,
            &acc_prime,
        )?;

        // Witness count: 27974 - 13411 = 14563
        let acc_verifier_ec = ProtostarAccumulationVerifier::new(cyclefold_avp.clone(), main_chip.clone(), sm_chip.clone());
        let acc_ec = acc_verifier_ec.assign_accumulator_ec(&mut layouter, self.acc_ec.as_ref())?;
        let acc_ec_prime_result = acc_verifier_ec.assign_accumulator_ec(&mut layouter, self.acc_prime_ec.as_ref())?;
        let (nark_ec, acc_ec_prime) = {     
            let proof = self.cyclefold_proof.clone();
            let transcript_chip = 
                &mut PoseidonTranscriptChip::<C>::new(&mut layouter, pow5_chip.clone(), PoseidonSpec, main_chip.clone(), proof);

            acc_verifier_ec.verify_accumulation_from_nark_ec(&mut layouter, &acc_ec, cyclefold_instances.try_into().unwrap(), transcript_chip)?
        };

        let (acc_ec_prime, acc_ec_prime_result) = {
            let acc_ec_default = acc_verifier_ec.assign_default_accumulator_ec(&mut layouter)?;
            let acc_ec_prime = acc_verifier_ec.select_accumulator_ec(&mut layouter, &is_base_case, &acc_ec_default, &acc_ec_prime)?;
            let acc_ec_prime_result = acc_verifier_ec.select_accumulator_ec(&mut layouter, &is_base_case, &acc_ec_default, &acc_ec_prime_result)?;
            (acc_ec_prime, acc_ec_prime_result)
        };

        self.check_folding_ec(
            &mut layouter,
            &main_chip,
            &acc_ec_prime,
            &acc_ec_prime_result,
        )?; 

        // assign public instances
        // main_chip.expose_public(layouter, &h_prime, 0)?;

        Ok(())
    }
}

impl<C, Sc> CircuitExt<C::Scalar> for PrimaryCircuit<C, Sc>
where
    C: TwoChainCurve,
    Sc: StepCircuit<C>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    fn instances(&self) -> Vec<Vec<C::Scalar>> {
        let mut instances = vec![vec![C::Scalar::ZERO; NUM_INSTANCES]];
        self.h_prime.map(|h_prime| instances[0][0] = h_prime);
        instances
    }

    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}

#[test]
fn primary_chip() {

    let k = 13;
    let primary_avp = ProtostarAccumulationVerifierParam::new(
        bn256::Fr::ZERO,
        Compressing,
        vec![NUM_INSTANCES],
        vec![1usize, 1usize],
        vec![vec![1usize], vec![5usize]],
        1,
    );

    let cyclefold_avp = ProtostarAccumulationVerifierParam::new(
        bn256::Fr::ZERO,
        Compressing,
        vec![CF_IO_LEN],
        vec![1usize, 1usize],
        vec![vec![1usize], vec![5usize]],
        1,
    );

    let circuit = PrimaryCircuit::<bn256::G1Affine, TrivialCircuit<bn256::G1Affine>>::new(true, TrivialCircuit::default(), Some(primary_avp), Some(cyclefold_avp));
    let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();
    println!("Witness count: {}", prover.witness_count);
    println!("Copy count: {}", prover.copy_count);
    prover.assert_satisfied();
    // assert_eq!(prover.verify(), Ok(()));

}

#[test]
fn primary_chip_layout() {
    use plotters::prelude::*;
    use halo2_base::halo2_proofs::dev::CircuitLayout;

    let root = BitMapBackend::new("PrimaryChip.png", (30240, 30680)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("Primary Chip Layout", ("sans-serif", 60))
        .unwrap();

    let k = 13;
    let primary_avp = ProtostarAccumulationVerifierParam::new(
        bn256::Fr::ZERO,
        Compressing,
        vec![NUM_INSTANCES],
        vec![1usize, 1usize],
        vec![vec![1usize], vec![5usize]],
        1,
    );

    let cyclefold_avp = ProtostarAccumulationVerifierParam::new(
        bn256::Fr::ZERO,
        Compressing,
        vec![CF_IO_LEN],
        vec![1usize, 1usize],
        vec![vec![1usize], vec![5usize]],
        1,
    );

    let circuit = PrimaryCircuit::<bn256::G1Affine, TrivialCircuit<bn256::G1Affine>>::new(true, TrivialCircuit::default(), Some(primary_avp), Some(cyclefold_avp));
    let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();
    println!("Witness count: {}", prover.witness_count);
    prover.assert_satisfied();

    let circuit_layout = CircuitLayout{
        hide_labels: false,
        mark_equality_cells: false,
        show_equality_constraints: false,
        view_width: Some(0..24),
        view_height: Some(0..(1<<k)),
    };

    circuit_layout.render(k, &circuit, &root)
    .unwrap();
}
