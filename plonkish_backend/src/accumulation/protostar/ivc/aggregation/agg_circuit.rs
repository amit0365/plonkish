use crate::{
    accumulation::protostar::{
        ivc::halo2::{
            preprocess, prove_decider, prove_steps, 
            test::strawman::{self, decider_transcript_param, Chip, PoseidonTranscriptChip, NUM_LIMBS, NUM_LIMB_BITS, RATE, R_F, R_P, SECURE_MDS, T}, 
            verify_decider, ProtostarIvcVerifierParam, StepCircuit
        },
        ProtostarAccumulatorInstance, ProtostarVerifierParam,
    },
    backend::{
        hyperplonk::{HyperPlonk, HyperPlonkVerifierParam},
        PlonkishBackend, PlonkishCircuit,
    },
    frontend::halo2::{layouter::InstanceExtractor, CircuitExt, Halo2Circuit},
    pcs::{
        multilinear::{Gemini, MultilinearHyrax, MultilinearIpa},
        univariate::UnivariateKzg,
        AdditiveCommitment, PolynomialCommitmentScheme,
    },
    poly::multilinear::MultilinearPolynomial,
    util::{
        arithmetic::{
            fe_to_fe, CurveAffine, Field, FromUniformBytes, MultiMillerLoop, PrimeFieldBits, TwoChainCurve
        }, chain, end_timer, start_timer, test::seeded_std_rng, transcript::InMemoryTranscript, DeserializeOwned, Itertools, Serialize
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
use super::ivc_agg::ProtostarIvcAggregator;
use std::{mem, rc::Rc};


#[derive(Clone)]
struct SecondaryAggregationCircuit {
    circuit_params: BaseCircuitParams,
    vp_digest: grumpkin::Fr,
    vp: ProtostarVerifierParam<bn256::Fr, HyperPlonk<Gemini<UnivariateKzg<Bn256>>>>,
    arity: usize,
    instances: Vec<grumpkin::Fr>,
    num_steps: Value<usize>,
    initial_input: Value<Vec<grumpkin::Fr>>,
    output: Value<Vec<grumpkin::Fr>>,
    acc: Value<ProtostarAccumulatorInstance<bn256::Fr, bn256::G1Affine>>,
    proof: Value<Vec<u8>>,
}

impl Circuit<grumpkin::Fr> for SecondaryAggregationCircuit {
    type Config = BaseConfig<grumpkin::Fr>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = BaseCircuitParams;

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure_with_params(meta: &mut ConstraintSystem<grumpkin::Fr>, params: BaseCircuitParams) -> Self::Config {
        BaseCircuitBuilder::configure_with_params(meta, params)
    }

    fn configure(meta: &mut ConstraintSystem<grumpkin::Fr>) -> Self::Config {
        unreachable!()
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<grumpkin::Fr>,
    ) -> Result<(), Error> {

        let mut circuit_builder = BaseCircuitBuilder::<grumpkin::Fr>::from_stage(CircuitBuilderStage::Mock).use_params(self.circuit_params.clone());
        let range_chip = circuit_builder.range_chip();
        let chip = Chip::<grumpkin::G1Affine>::create(range_chip);
        let builder = circuit_builder.pool(0);
        let ctx = builder.main();

        let aggregator = ProtostarIvcAggregator::new(
            self.vp_digest,
            self.vp.clone(),
            self.arity,
            chip.clone(),
            chip.clone(),
        );

        let mut transcript = PoseidonTranscriptChip::new(
            ctx,
            decider_transcript_param(),
            chip.clone(),
            self.proof.clone(),
        );

        let (num_steps, initial_input, output, h, lhs, rhs) = aggregator.aggregate_gemini_kzg_ivc(
            builder,
            self.num_steps,
            self.initial_input.clone(),
            self.output.clone(),
            self.acc.clone(),
            &mut transcript,
        )?;

        let zero = chip.assign_constant(builder, grumpkin::Fr::ZERO)?;
        // let lhs_is_identity = (lhs.x() & lhs.y()).into();
        // chip.constrain_equal(builder, lhs.is_identity(), &zero)?;
        // chip.constrain_equal(builder, rhs.is_identity(), &zero)?;

        let mut assigned_instances = circuit_builder.assigned_instances;
        assert_eq!(
            assigned_instances.len(),
            1,
            "Circuit must have exactly 1 instance column"
        );
        assert!(assigned_instances[0].is_empty());
        
        for (idx, witness) in chain![
            [num_steps],
            initial_input,
            output,
            [h, *lhs.x(), *lhs.y(), *rhs.x(), *rhs.y()]
        ]
        .enumerate()
        {
            assigned_instances[0].push(witness);
        }

        Ok(())
    }
}

impl CircuitExt<grumpkin::Fr> for SecondaryAggregationCircuit {
    fn instances(&self) -> Vec<Vec<grumpkin::Fr>> {
        vec![self.instances.clone()]
    }

    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}
#[derive(Clone)]
struct PrimaryAggregationCircuit {
    vp_digest: bn256::Fr,
    vp: ProtostarVerifierParam<grumpkin::Fr, HyperPlonk<MultilinearIpa<grumpkin::G1Affine>>>,
    primary_arity: usize,
    secondary_arity: usize,
    instances: Vec<bn256::Fr>,
    num_steps: Value<usize>,
    initial_input: Value<Vec<bn256::Fr>>,
    output: Value<Vec<bn256::Fr>>,
    acc_before_last: Value<ProtostarAccumulatorInstance<grumpkin::Fr, grumpkin::G1Affine>>,
    last_instance: Value<[grumpkin::Fr; 2]>,
    proof: Value<Vec<u8>>,
    secondary_aggregation_vp: HyperPlonkVerifierParam<grumpkin::Fr, MultilinearHyrax<grumpkin::G1Affine>>,
    secondary_aggregation_instances: Value<Vec<grumpkin::Fr>>,
    secondary_aggregation_proof: Value<Vec<u8>>,
}

impl Circuit<bn256::Fr> for PrimaryAggregationCircuit {
    type Config = BaseConfig<bn256::Fr>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = BaseCircuitParams;

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(meta: &mut ConstraintSystem<bn256::Fr>) -> Self::Config {
        BaseConfig::configure(meta, BaseCircuitParams::default())
    }
    
    //todo fix this with other synthesizes
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<bn256::Fr>,
    ) -> Result<(), Error> {

        let mut builder = BaseCircuitBuilder::<bn256::Fr>::from_stage(CircuitBuilderStage::Keygen);
        let range = builder.range_chip();
        let gate_chip = GateChip::<bn256::Fr>::new();
        let base_chip = FpChip::<bn256::Fr, bn256::Fq>::new(&range, NUM_LIMB_BITS, NUM_LIMBS);
        let native_chip = NativeFieldChip::new(&range);
        let ecc_chip = EccChip::new(&native_chip);
        let mut pool = mem::take(builder.pool(0));
        let chip = Chip::<bn256::G1Affine>::create(range);
        //let chip = strawman::Chip::<bn256::G1Affine>::create(range);
        let aggregator = ProtostarIvcAggregator::new(
            self.vp_digest,
            self.vp.clone(),
            self.primary_arity,
            chip.clone(),
            chip.clone(),
        );

        let mut transcript = strawman::PoseidonTranscriptChip::new(
            builder.main(0),
            strawman::decider_transcript_param(),
            chip.clone(),
            self.proof.clone(),
        );

        let (primary_num_steps, primary_initial_input, primary_output, h_ohs_from_last_nark) =
            aggregator.verify_ipa_grumpkin_ivc_with_last_nark(
                &mut pool,
                self.num_steps,
                self.initial_input.clone(),
                self.output.clone(),
                self.acc_before_last.clone(),
                self.last_instance,
                &mut transcript,
            )?;

        let (secondary_initial_input, secondary_output, pairing_acc) = {
            
            let mut transcript = strawman::PoseidonTranscriptChip::new(
                builder.main(0),
                strawman::decider_transcript_param(),
                chip.clone(),
                self.secondary_aggregation_proof.clone(),
            );

            let secondary_aggregation_instance = chip.verify_hyrax_hyperplonk(
                &mut pool,
                &self.secondary_aggregation_vp,
                self.secondary_aggregation_instances
                    .as_ref()
                    .map(Vec::as_slice),
                &mut transcript,
            )?;        
            let secondary_num_steps = chip.fit_base_in_scalar(&mut pool, &secondary_aggregation_instance[0])?;
            chip.constrain_equal(&mut pool, &primary_num_steps, &secondary_num_steps)?;

            let h = chip.fit_base_in_scalar(&mut pool, &secondary_aggregation_instance[1 + 2 * self.secondary_arity],
            )?;
            chip.constrain_equal(&mut pool, &h_ohs_from_last_nark, &h)?;

            let iter = &mut secondary_aggregation_instance.iter();
            let mut instances = |skip: usize, take: usize| {
                iter.skip(skip)
                    .take(take)
                    .map(|base| chip.to_repr_base(base))
                    .try_collect::<_, Vec<_>, _>()
            };
            (
                instances(1, self.secondary_arity)?,
                instances(0, self.secondary_arity)?,
                instances(1, 4 * strawman::NUM_LIMBS)?,
            )
        };
        
       
        // let cell_map = chip.clear(&mut layouter)?;
        let mut assigned_instances = builder.assigned_instances;
        for (idx, witness) in chain![
            [primary_num_steps],
            primary_initial_input,
            primary_output,
            secondary_initial_input.into_iter().flatten(),
            secondary_output.into_iter().flatten(),
            pairing_acc.into_iter().flatten(),
        ]
        .enumerate()
        {
            assigned_instances[0].push(witness);
            //layouter.constrain_instance(cell_map[&witness.id()].cell(), chip.instance, idx)?;
        }

        Ok(())
    }
}


impl CircuitExt<bn256::Fr> for PrimaryAggregationCircuit {
    fn instances(&self) -> Vec<Vec<bn256::Fr>> {
        vec![self.instances.clone()]
    }
    fn rand(k: usize, _: impl RngCore) -> Self {
        unimplemented!()
    }
}
/*

    1. Run MockProver for Secondary Circuit
    2. Run MockProver for Primary Circuit 


*/