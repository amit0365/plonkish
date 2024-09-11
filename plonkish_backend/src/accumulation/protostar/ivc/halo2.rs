pub mod test;
pub mod chips;
pub mod ivc_circuits;
use ethereum_types::U256;

use crate::{
    accumulation::{
        protostar::{
            ivc::{ProtostarAccumulationVerifierParam, halo2::ivc_circuits::cyclefold::{CycleFoldCircuit, self, CF_IO_LEN}},
            PlonkishNarkInstance, Protostar, ProtostarAccumulator, ProtostarAccumulatorInstance,
            ProtostarProverParam,
            ProtostarStrategy::{Compressing, NoCompressing},
            ProtostarVerifierParam,
        },
        AccumulationScheme,
    },
    backend::{
        hyperplonk::{verifier::point_offset, HyperPlonk, HyperPlonkVerifierParam},
        PlonkishBackend, PlonkishCircuit
    },
    frontend::halo2::{Halo2Circuit, CircuitExt},
    pcs::{
        multilinear::{
            Gemini, MultilinearHyrax, MultilinearHyraxParams, MultilinearIpa, MultilinearIpaParams,
        },
        univariate::{kzg::eval_sets, UnivariateKzg},
        AdditiveCommitment, Evaluation, PolynomialCommitmentScheme,
    },
    poly::multilinear::{
        rotation_eval_coeff_pattern, rotation_eval_point_pattern, zip_self, MultilinearPolynomial,
    },
    util::{
        arithmetic::{
            barycentric_weights, fe_to_fe, fe_truncated_from_le_bytes, powers, steps, CurveAffine,
            BooleanHypercube, Field, MultiMillerLoop, PrimeCurveAffine, PrimeField, TwoChainCurve, OverridenCurveAffine
        },
        chain, end_timer,
        expression::{CommonPolynomial, Expression, Query, Rotation},
        hash::{Hash as _, Keccak256},
        izip, izip_eq, start_timer,
        transcript::{InMemoryTranscript, TranscriptRead, TranscriptWrite},
        BitIndex, DeserializeOwned, Itertools, Serialize,
    },
};

use crate::accumulation::protostar::ivc::halo2::ivc_circuits::primary::{T, RATE};
use crate::accumulation::protostar::ivc::halo2::chips::{T as T2, R as R2};

use std::{
    borrow::{Borrow, BorrowMut, Cow},
    collections::{btree_map::Entry, BTreeMap, HashMap, BTreeSet},
    fmt::Debug,
    hash::Hash,
    iter::{self, once},
    marker::PhantomData,
    mem,
    rc::Rc, time::Instant,
};

use halo2_gadgets::poseidon::spec::PoseidonSpec;
use halo2_proofs::halo2curves::group::prime::{PrimeCurve, PrimeGroup};
use poseidon::Spec;
use poseidon2::circuit::spec::PoseidonSpec as Poseidon2ChipSpec;
use rand::{rngs::OsRng, RngCore};
use std::cell::RefCell;

use halo2_base::{
    Context,
    gates::{
        circuit::{builder::{RangeCircuitBuilder, BaseCircuitBuilder, self},
        CircuitBuilderStage, BaseCircuitParams, BaseConfig},
        flex_gate::{GateChip, GateInstructions, threads::SinglePhaseCoreManager}, RangeChip,
    },
    utils::{CurveAffineExt, ScalarField, BigPrimeField},
    QuantumCell::{Constant, Existing, Witness, WitnessFraction},
    AssignedValue,
    poseidon::hasher::{PoseidonSponge, PoseidonHasher, spec::OptimizedPoseidonSpec, PoseidonHash}, 
    halo2_proofs::dev::MockProver, virtual_region::copy_constraints::SharedCopyConstraintManager,
};

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Circuit, Selector, Error, ConstraintSystem},
};

use halo2_proofs::halo2curves::{
    bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta},
    group::{
        ff::{FromUniformBytes, PrimeFieldBits},
        Curve, Group
    },
    Coordinates, CurveExt,
};

use self::{chips::{main_chip::{EcPointNative, EcPointNonNative, MainChip, MainChipConfig, NonNativeNumber, Number}, scalar_mul::sm_chip_primary::ScalarMulChip, transcript::{native::{AssignedProtostarAccumulatorInstance, PoseidonNativeTranscriptChip}, nonnative::PoseidonTranscriptChip, NUM_HASH_BITS}}, ivc_circuits::primary::{PrimaryCircuit, NUM_INSTANCES}};

// use test::strawman::{self, T, RANGE_BITS, RATE, NUM_CHALLENGE_BITS, NUM_LIMBS, NUM_LIMB_BITS, R_F, R_P, SECURE_MDS, Chip};

// use self::chips::{poseidon::spec::PoseidonSpec, transcript::{native::PoseidonNativeTranscriptChip, nonnative::PoseidonTranscriptChip}};

// pub const NUM_INSTANCES: usize = 1;

// pub type AssignedCycleFoldInputsInPrimary<Assigned, AssignedSecondary> =
//     CycleFoldInputsInPrimary<Assigned, AssignedSecondary>;
    
// #[derive(Debug, Clone)]
// pub struct CycleFoldInputsInPrimary<F, C> 
// {   
//     pub r: F,
//     pub nark_witness_comms: Vec<C>,
//     pub cross_term_comms: Vec<C>,
//     pub acc_witness_comms: Vec<C>,
//     pub acc_e_comm: C,
//     pub acc_prime_witness_comms: Vec<C>,
//     pub acc_prime_e_comm: C,
// }

type AssignedPlonkishNarkInstance<AssignedBase, AssignedSecondary> =
    PlonkishNarkInstance<AssignedBase, AssignedSecondary>;

// type AssignedProtostarAccumulatorInstance<AssignedBase, AssignedSecondary> =
//     ProtostarAccumulatorInstance<AssignedBase, AssignedSecondary>;


pub trait StepCircuit<C: TwoChainCurve>: Clone + Debug + CircuitExt<C::Scalar> 
where
    C::Scalar: BigPrimeField,
    C::Base: BigPrimeField,
{   

    fn arity() -> usize;

    fn initial_input(&self) -> &[C::Scalar];

    fn input(&self) -> &[C::Scalar];

    fn output(&self) -> &[C::Scalar];

    fn step_idx(&self) -> usize;

    fn next(&mut self);

    #[allow(clippy::type_complexity)]
    fn synthesize(
        &self,
        config: MainChipConfig,
        layouter: impl Layouter<C::Scalar>,
    ) -> Result<
        (
            Vec<Number<C::Scalar>>,
            Vec<Number<C::Scalar>>,
        ),
        Error,
    >;
}

pub struct ProtostarAccumulationVerifier<C: TwoChainCurve> 
where
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    avp: ProtostarAccumulationVerifierParam<C::Scalar>,
    main_chip: MainChip<C>,
    sm_chip: ScalarMulChip<C>,
}

impl<C> ProtostarAccumulationVerifier<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    pub type Num = Number<C::Scalar>;
    pub type NonNatNum = NonNativeNumber<C::Scalar>;
    pub type Ecc = EcPointNonNative<C>;
    pub type NatEcc = EcPointNative<C>;

    pub fn new(avp: ProtostarAccumulationVerifierParam<C::Scalar>, main_chip: MainChip<C>, sm_chip: ScalarMulChip<C>) -> Self {
        Self {
            avp,
            main_chip,
            sm_chip,
        }
    }

    pub fn assign_default_accumulator(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<
        Self::Num, 
        Self::Ecc>,
        Error,
    > {
        let main_chip = &self.main_chip;
        let ProtostarAccumulationVerifierParam { num_instances, .. } = &self.avp;

        let instances = num_instances
            .iter()
            .enumerate()
            .map(|(idx, num_instances)| {
                iter::repeat_with(|| main_chip.assign_fixed(layouter, &C::Scalar::ZERO, idx))
                    .take(*num_instances)
                    .try_collect::<_, Vec<_>, _>()
            })
            .try_collect::<_, Vec<_>, _>()?;
        let witness_comms = iter::repeat_with(|| {
            main_chip.assign_constant_primary(layouter, C::identity())
            }).take(self.avp.num_folding_witness_polys())
            .try_collect::<_, Vec<_>, _>()?;
        let challenges =
            iter::repeat_with(|| main_chip.assign_fixed(layouter, &C::Scalar::ZERO, 0))
                .take(self.avp.num_folding_challenges())
                .try_collect::<_, Vec<_>, _>()?;
        let u = main_chip.assign_fixed(layouter, &C::Scalar::ZERO, 0)?;
        let e_comm = main_chip.assign_constant_primary(layouter, C::identity())?;
        let compressed_e_sum = match self.avp.strategy {
            NoCompressing => None,
            Compressing => Some(main_chip.assign_fixed(layouter, &C::Scalar::ZERO, 0)?),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }

    pub fn assign_default_accumulator_ec(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<
        Self::NonNatNum, Self::NatEcc>,
        Error,
    > {
        let main_chip = &self.main_chip;
        let ProtostarAccumulationVerifierParam { num_instances, .. } = &self.avp;

        let instances = num_instances
            .iter()
            .map(|num_instances| {
                iter::repeat_with(|| main_chip.assign_fixed_base(layouter, &C::Base::ZERO))
                    .take(*num_instances)
                    .try_collect::<_, Vec<_>, _>()
            })
            .try_collect::<_, Vec<_>, _>()?;
        let witness_comms = iter::repeat_with(|| {
            main_chip.assign_constant_secondary(layouter, C::Secondary::identity())
        })
        .take(self.avp.num_folding_witness_polys())
        .try_collect::<_, Vec<_>, _>()?;
        let challenges =
            iter::repeat_with(|| main_chip.assign_fixed_base(layouter, &C::Base::ZERO))
                .take(self.avp.num_folding_challenges())
                .try_collect::<_, Vec<_>, _>()?;
        let u = main_chip.assign_fixed_base(layouter, &C::Base::ZERO)?;
        let e_comm = main_chip.assign_constant_secondary(layouter, C::Secondary::identity())?;
        let compressed_e_sum = match self.avp.strategy {
            NoCompressing => None,
            Compressing => Some(main_chip.assign_fixed_base(layouter, &C::Base::ZERO)?),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }

    pub fn assign_comm_outputs_from_accumulator(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        acc: Value<&ProtostarAccumulatorInstance<C::Scalar, C>>,
    ) -> Result<Vec<Self::Ecc>, Error> {
        let main_chip = &self.main_chip;
        let avp = &self.avp;
        let witness_comms = acc
            .map(|acc| &acc.witness_comms)
            .transpose_vec(avp.num_folding_witness_polys())
            .into_iter()
            .map(|witness_comm| 
                {
                    let mut witness_comm_val = C::default();
                    witness_comm.map(|val| witness_comm_val = *val);
                    main_chip.assign_witness_primary(layouter, witness_comm_val)
                })
            .try_collect::<_, Vec<_>, _>()?;

        let mut acc_e_comm_val = C::default();
        acc.map(|acc| acc.e_comm).map(|val| acc_e_comm_val = val);
        let e_comm = main_chip.assign_witness_primary(layouter, acc_e_comm_val)?;
        
        let mut assigned_comm = witness_comms.clone();
        assigned_comm.push(e_comm);
        Ok(assigned_comm)
    }

    pub fn assign_accumulator(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        acc: Value<&ProtostarAccumulatorInstance<C::Scalar, C>>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<
        Self::Num, Self::Ecc>,
        Error,
    > {
        let main_chip = &self.main_chip;
        let avp = &self.avp;
        let instances = avp
            .num_instances
            .iter()
            .zip(
                acc.map(|acc| &acc.instances)
                    .transpose_vec(avp.num_instances.len()),
            )
            .map(|(num_instances, instances)| {
                instances
                    .transpose_vec(*num_instances)
                    .into_iter()
                    .enumerate()
                    .map(|(idx, instance)| 
                    {
                        let mut instance_val = C::Scalar::ZERO;
                        instance.map(|val| instance_val = *val);
                        main_chip.assign_witness(layouter, &instance_val, idx)
                    })
                    .try_collect::<_, Vec<_>, _>()
            }).try_collect::<_, Vec<_>, _>()?;

        let witness_comms = acc
            .map(|acc| &acc.witness_comms)
            .transpose_vec(avp.num_folding_witness_polys())
            .into_iter()
            .map(|witness_comm| 
                {
                    let mut witness_comm_val = C::default();
                    witness_comm.map(|val| witness_comm_val = *val);
                    main_chip.assign_witness_primary(layouter, witness_comm_val)
                })
            .try_collect::<_, Vec<_>, _>()?;

        let challenges = acc
            .map(|acc| &acc.challenges)
            .transpose_vec(avp.num_folding_challenges())
            .into_iter()
            .enumerate()
            .map(|(idx, challenge)|
                {
                    let mut challenge_val = C::Scalar::ZERO;
                    challenge.map(|val| challenge_val = *val);
                    main_chip.assign_witness(layouter, &challenge_val, idx)
                })
            .try_collect::<_, Vec<_>, _>()?;

        let mut acc_u_val = C::Scalar::ZERO;
        acc.map(|acc| acc.u).map(|val| acc_u_val = val);
        let u = main_chip.assign_witness(layouter, &acc_u_val, 0)?;

        let mut acc_e_comm_val = C::default();
        acc.map(|acc| acc.e_comm).map(|val| acc_e_comm_val = val);
        let e_comm = main_chip.assign_witness_primary(layouter, acc_e_comm_val)?;

        let mut acc_compressed_e_sum_val = C::Scalar::ZERO;
        acc.map(|acc| acc.compressed_e_sum.map(|val| acc_compressed_e_sum_val = val));
        let compressed_e_sum = match avp.strategy {
            NoCompressing => None,
            Compressing => Some(
                main_chip
                    .assign_witness(layouter, &acc_compressed_e_sum_val, 0)?,
            ),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }

    pub fn assign_accumulator_ec(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        acc: Value<&ProtostarAccumulatorInstance<C::Base, C::Secondary>>,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<Self::NonNatNum, Self::NatEcc>,
        Error,
    > {
        let main_chip = &self.main_chip;
        let avp = &self.avp;
        let instances = avp
            .num_instances
            .iter()
            .zip(
                acc.map(|acc| &acc.instances)
                    .transpose_vec(avp.num_instances.len()),
            )
            .map(|(num_instances, instances)| {
                instances
                    .transpose_vec(*num_instances)
                    .into_iter()
                    .map(|instance| 
                        {
                            let mut instance_val = C::Base::ZERO;
                            instance.map(|val| instance_val = *val);
                            main_chip.assign_witness_base(layouter, instance_val)
                        }
                    )
                    .try_collect::<_, Vec<_>, _>()
            }).try_collect::<_, Vec<_>, _>()?;
        
        let witness_comms = acc
            .map(|acc| &acc.witness_comms)
            .transpose_vec(avp.num_folding_witness_polys())
            .into_iter()
            .map(|witness_comm| 
                {
                    let mut witness_comm_val = C::Secondary::default();
                    witness_comm.map(|val| witness_comm_val = *val);
                    main_chip.assign_witness_secondary(layouter, witness_comm_val)
                })
            .try_collect::<_, Vec<_>, _>()?;

        let challenges = acc
            .map(|acc| &acc.challenges)
            .transpose_vec(avp.num_folding_challenges())
            .into_iter()
            .map(|challenge| 
                {
                    let mut challenge_val = C::Base::ZERO;
                    challenge.map(|val| challenge_val = *val);
                    main_chip.assign_witness_base(layouter, challenge_val)
                })
            .try_collect::<_, Vec<_>, _>()?;

        let mut acc_u_val = C::Base::ZERO;
        acc.map(|acc| acc.u).map(|val| acc_u_val = val);
        let u = main_chip.assign_witness_base(layouter, acc_u_val)?;

        let mut acc_e_comm_val = C::Secondary::default();
        acc.map(|acc| acc.e_comm).map(|val| acc_e_comm_val = val);
        let e_comm = main_chip.assign_witness_secondary(layouter, acc_e_comm_val)?;

        let mut acc_compressed_e_sum_val = C::Base::ZERO;
        acc.map(|acc| acc.compressed_e_sum.map(|val| acc_compressed_e_sum_val = val));
        let compressed_e_sum = match avp.strategy {
            NoCompressing => None,
            Compressing => Some(
                main_chip
                    .assign_witness_base(layouter, acc_compressed_e_sum_val)?
            ),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }

    #[allow(clippy::type_complexity)]
    pub fn verify_accumulation_from_nark(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            Self::Num,
            Self::Ecc,
        >,
        instances: [Value<&C::Scalar>; NUM_INSTANCES],
        transcript_chip: &mut PoseidonNativeTranscriptChip<C>,
        assigned_acc_prime_comms_checked: Vec<Self::Ecc>
        // cyclefold_instances: [Value<&C::Base>; CF_IO_LEN],
    ) -> Result<
        (
            AssignedPlonkishNarkInstance<Self::Num, Self::Ecc>,
            AssignedProtostarAccumulatorInstance<Self::Num, Self::Ecc>
        ),
        Error,
    > {
        let main_chip = &self.main_chip;
        let ProtostarAccumulationVerifierParam {
            strategy,
            num_witness_polys,
            num_challenges,
            num_cross_terms,
            //num_alpha_primes,
            ..
        } = &self.avp;
        let instances = instances
            .into_iter()
            .enumerate()
            .map(|(idx, instance)| 
                {
                    let mut instance_val = C::Scalar::ZERO;
                    instance.map(|val| instance_val = *val);
                    main_chip.assign_witness(layouter, &instance_val, idx)
                })
            .try_collect::<_, Vec<_>, _>()?;
        for instance in instances.iter() {
            transcript_chip.common_field_element(instance)?;
        }

        // let mut witness_comms = Vec::with_capacity(self.avp.num_folding_witness_polys());
        // let mut challenges = Vec::with_capacity(self.avp.num_folding_challenges());
        // for (num_witness_polys, num_powers_of_challenge) in
        //     num_witness_polys.iter().zip_eq(num_challenges.iter())
        // {
        //     witness_comms.extend(transcript.read_commitments(builder, *num_witness_polys)?);
        //     for num_powers in num_powers_of_challenge.iter() {
        //         let challenge = transcript.squeeze_challenge(builder)?;
        //         let powers_of_challenges =
        //             main_chip.powers(builder, challenge.as_ref(), *num_powers + 1)?;
        //         challenges.extend(powers_of_challenges.into_iter().skip(1));
        //     }
        // }

        let mut witness_comms = Vec::with_capacity(2);
        let mut challenges = Vec::with_capacity(3);
        
        // write comm only for test
        // 0x2a6148ae85b8df7365f051126ccac4df868497e62758daff76cb89aeea12bdb6,
        // 0x2390bb5e606ac7db700236a04d8da435940d1332e2a66332f0f87329fd47398c,
        let hex_str_x = "0x2a6148ae85b8df7365f051126ccac4df868497e62758daff76cb89aeea12bdb6";
        let decimal_value_x = U256::from_str_radix(&hex_str_x[2..], 16).unwrap();
        let hex_str_y = "0x2390bb5e606ac7db700236a04d8da435940d1332e2a66332f0f87329fd47398c";
        let decimal_value_y = U256::from_str_radix(&hex_str_y[2..], 16).unwrap();
        let bn254_random = C::from_xy(
            C::Base::from_str_vartime(&decimal_value_x.to_string()).unwrap(),
            C::Base::from_str_vartime(&decimal_value_y.to_string()).unwrap(),
        ).unwrap();

        // write comm only for test
        witness_comms.push(transcript_chip.write_commitment(layouter, &bn254_random)?);
        //witness_comms.push(transcript_chip.read_commitment(layouter)?);
        //let beta_prime = transcript_chip.squeeze_challenge(layouter.namespace(|| "challenge1"))?.challenge;
        //challenges.extend(main_chip.powers(layouter.namespace(|| "challenge1"), &beta_prime, 5)?.into_iter().skip(1).take(5).collect::<Vec<_>>());
        challenges.push(transcript_chip.squeeze_challenge(layouter)?.challenge);
        witness_comms.push(transcript_chip.write_commitment(layouter, &bn254_random)?);
        //witness_comms.push(transcript_chip.read_commitment(layouter)?);
        let challenge3 = transcript_chip.squeeze_challenge(layouter)?.challenge;
        challenges.extend(main_chip.powers(layouter, &challenge3, 40)?.into_iter().skip(1).take(39).collect::<Vec<_>>());
        // challenges.push(transcript_chip.squeeze_challenge(layouter.namespace(|| "challenge3"))?.challenge);
        let nark = PlonkishNarkInstance::new(vec![instances], challenges, witness_comms);
        transcript_chip.absorb_accumulator(layouter.namespace(|| "absorb_accumulator"), acc)?;

        let (cross_term_comms, compressed_cross_term_sums) = match strategy {
            NoCompressing => {
                let cross_term_comms = transcript_chip.read_commitments(layouter, *num_cross_terms)?;

                (cross_term_comms, None)
            }
            Compressing => {
                // let zeta_cross_term_comm = vec![transcript_chip.read_commitment(layouter)?];
                let zeta_cross_term_comm = vec![transcript_chip.write_commitment(layouter, &bn254_random)?];
                // let compressed_cross_term_sums =
                //     transcript_chip.read_field_elements(layouter, *num_cross_terms)?;
                let compressed_cross_term_sums =
                    transcript_chip.write_field_elements(layouter, &[C::Scalar::ONE; 10])?;
                (zeta_cross_term_comm, Some(compressed_cross_term_sums))
            }
        };

        let r = transcript_chip.squeeze_challenge(layouter)?;
        let r_le_bits = transcript_chip.challenge_to_le_bits(&r)?;

        // let assigned_cyclefold_instances = self.assign_cyclefold_instances_acc_prime(builder, cyclefold_instances)?;
        // let assigned_cyclefold_instances = self.assign_cyclefold_instances(builder, cyclefold_instances)?;
        // self.check_assigned_cyclefold_instances(builder, r.as_ref(), &nark, &cross_term_comms, &acc, &assigned_cyclefold_instances);

        let acc_prime = self.fold_accumulator_from_nark(
            layouter,
            acc,
            &nark,
            &cross_term_comms,
            compressed_cross_term_sums.as_deref(),
            r.as_ref(),
            &r_le_bits,
            assigned_acc_prime_comms_checked,
        )?;

        Ok((nark, acc_prime))
    }

    pub fn assign_cyclefold_instances_acc_prime(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        cyclefold_instances: [Value<&C::Base>; CF_IO_LEN]
    ) -> Result<Vec<Self::Ecc>, Error> 
    {
        let main_chip = &self.main_chip;
        let avp = &self.avp;
        let num_witness_comms = avp.num_folding_witness_polys();

        let coordinates = cyclefold_instances[1..]
            .iter()
            .map(|input| 
                {
                    let mut input_val = C::Base::ZERO;
                    input.map(|val| input_val = *val);
                    input_val
                })
            .collect_vec();

        let assigned_comms = coordinates.chunks(2).map(|chunk| {
            main_chip.assign_witness_primary(layouter, C::from_xy(chunk[0], chunk[1]).unwrap()).unwrap()
        }).collect_vec();

        Ok(assigned_comms)
    }

    // pub fn assign_cyclefold_instances(
    //     &self,
    //     layouter: &mut impl Layouter<C::Scalar>,
    //     cyclefold_instances: [Value<&C::Base>; CF_IO_LEN]
    // ) -> Result<AssignedCycleFoldInputsInPrimary<
    //     Self::Num, 
    //     Self::Ecc>
    //     Error> 
    // {
    //     let main_chip = &self.main_chip;
    //     let avp = &self.avp;
    //     let num_witness_comms = avp.num_folding_witness_polys();
    //     let num_cross_comms = match avp.strategy {
    //         NoCompressing => avp.num_cross_terms,
    //         Compressing => 1
    //     };

    //     // add fit base in scalar - 
    //     let r_limbs = cyclefold_instances[..NUM_LIMBS].iter()
    //         .map(|input| input.copied().assign().unwrap().clone())
    //         .collect_vec();

    //     let r_fe = fe_from_limbs(&r_limbs, NUM_LIMB_BITS);
    //     let r = main_chip.assign_witness(builder, r_fe)?;

    //     let coordinates = cyclefold_instances[NUM_LIMBS..]
    //         .iter()
    //         .map(|input| input.copied().assign().unwrap())
    //         .collect_vec();

    //     let assigned_comms = coordinates.chunks(2).map(|chunk| {
    //         main_chip.assign_witness_primary(builder, C::from_xy(chunk[0], chunk[1]).unwrap()).unwrap()
    //     }).collect_vec();

    //     let mut idx = 0;
    //     let nark_witness_comms = assigned_comms[idx..idx + num_witness_comms].to_vec();
    //         idx += num_witness_comms;
    //     let cross_term_comms = assigned_comms[idx..idx + num_cross_comms].to_vec();
    //         idx += num_cross_comms;
    //     let acc_witness_comms = assigned_comms[idx..idx + num_witness_comms].to_vec();
    //         idx += num_witness_comms;
    //     let acc_e_comm = &assigned_comms[idx];
    //         idx += 1;
    //     let acc_prime_witness_comms = assigned_comms[idx..idx + num_witness_comms].to_vec();
    //         idx += num_witness_comms;
    //     let acc_prime_e_comm = &assigned_comms[idx];

    //     Ok(AssignedCycleFoldInputsInPrimary {
    //         r,
    //         nark_witness_comms,
    //         cross_term_comms,
    //         acc_witness_comms,
    //         acc_e_comm: acc_e_comm.clone(),
    //         acc_prime_witness_comms,
    //         acc_prime_e_comm: acc_prime_e_comm.clone(),
    //     })
    // }

    // pub fn check_assigned_cyclefold_instances(
    //     &self,
    //     layouter: &mut impl Layouter<C::Scalar>,
    //     r: &Self::Num,
    //     nark: &AssignedPlonkishNarkInstance<
    //         Self::Num, 
    //         Self::Ecc>
    //     cross_term_comms: &[EcPoint<C::Scalar, ProperCrtUint<C::Scalar>>],
    //     acc: &AssignedProtostarAccumulatorInstance<
    //         Self::Num,
    //         Self::Ecc>
    //     assigned_cyclefold_instances: &AssignedCycleFoldInputsInPrimary<
    //         Self::Num, 
    //         Self::Ecc>
    // ) {
    //     let main_chip = &self.main_chip;
    //     main_chip.constrain_equal(builder, &assigned_cyclefold_instances.r, r);
    //     println!("r_constrained");
    //     izip_eq!(&assigned_cyclefold_instances.nark_witness_comms, &nark.witness_comms)
    //     .map(|(lhs, rhs)|
    //     main_chip.constrain_equal_primary_non_native(builder, &lhs, &rhs));
    //     println!("nark_witness_comms_constrained");
    //     izip_eq!(&assigned_cyclefold_instances.cross_term_comms, cross_term_comms)
    //     .map(|(lhs, rhs)|
    //     main_chip.constrain_equal_primary_non_native(builder, &lhs, &rhs));
    //     println!("cross_term_comms_constrained");
    //     main_chip.constrain_equal_primary_non_native(builder, &assigned_cyclefold_instances.acc_e_comm, &acc.e_comm);
    //     println!("acc_e_comm_constrained");
    //     izip_eq!(&assigned_cyclefold_instances.acc_witness_comms, &acc.witness_comms)
    //     .map(|(lhs, rhs)|
    //     main_chip.constrain_equal_primary_non_native(builder, &lhs, &rhs));
    //     println!("acc_witness_comms_constrained");
    // }

    #[allow(clippy::type_complexity)]
    pub fn verify_accumulation_from_nark_ec(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            Self::NonNatNum,
            Self::NatEcc
        >,
        instances: [Value<&C::Base>; CF_IO_LEN], 
        transcript_chip: &mut PoseidonTranscriptChip<C>,
    ) -> Result<
        (
            AssignedPlonkishNarkInstance<Self::NonNatNum, Self::NatEcc>,
            AssignedProtostarAccumulatorInstance<Self::NonNatNum, Self::NatEcc>,
        ),
        Error,
    > {
        let main_chip = &self.main_chip;
        let ProtostarAccumulationVerifierParam {
            strategy,
            num_witness_polys,
            num_challenges,
            num_cross_terms,
            //num_alpha_primes,
            ..
        } = &self.avp;
        // assert!(instances.len() == CF_IO_LEN);
        let instances = instances
            .into_iter()
            .map(|instance| 
                {
                    let mut instance_val = C::Base::ZERO;
                    instance.map(|val| instance_val = *val);
                    main_chip.assign_witness_base(layouter, instance_val)
                })
            .try_collect::<_, Vec<_>, _>()?;
        for instance in instances.iter() {
            transcript_chip.common_field_element(instance)?;
        }

        // let mut witness_comms = Vec::with_capacity(self.avp.num_folding_witness_polys());
        // let mut challenges = Vec::with_capacity(self.avp.num_folding_challenges());
        // for (num_witness_polys, num_powers_of_challenge) in
        //     num_witness_polys.iter().zip_eq(num_challenges.iter())
        // {
        //     witness_comms.extend(transcript.read_commitments(builder, *num_witness_polys)?);
        //     for num_powers in num_powers_of_challenge.iter() {
        //         let challenge = transcript.squeeze_challenge(builder)?;
        //         let powers_of_challenges =
        //             main_chip.powers_base(builder, challenge.as_ref(), *num_powers + 1)?;
        //         challenges.extend(powers_of_challenges.into_iter().skip(1));
        //     }
        // }

        let mut witness_comms = Vec::with_capacity(2);
        let mut challenges = Vec::with_capacity(3);
        
        // write comm only for test
        // 0x2bd9dcdba86889ed8988b66aa3f3eb49b3990420274d33b1eb66969b8ac0dd9a,
        // 0x2c678516c21eef9231dc569ce9d6e41269dc4c1e7c923c25b0664cea8cb74890,
        // let hex_str = "0x2c678516c21eef9231dc569ce9d6e41269dc4c1e7c923c25b0664cea8cb74890";
        // let decimal_value = U256::from_str_radix(&hex_str[2..], 16).unwrap();
        let grumpkin_random = C::Secondary::from_xy(
            C::Scalar::from_str_vartime("19834382608297447889961323302677467055070110053155139740545148874538063289754").unwrap(),
            C::Scalar::from_str_vartime("20084669131162155340423162249467328031170931348295785825029782732565818853520").unwrap(),
        ).unwrap();

        witness_comms.push(transcript_chip.write_commitment(layouter, &grumpkin_random)?);
        // let beta_prime = transcript_chip.squeeze_challenge(layouter.namespace(|| "transcript_chip"))?.scalar;
        // witness_comms.push(transcript_chip.read_commitment(layouter)?);
        // challenges.extend(main_chip.powers(layouter.namespace(|| "main_chip"), &beta_prime, 5)?.into_iter().skip(1).take(5).collect::<Vec<_>>());
        challenges.push(transcript_chip.squeeze_challenge(layouter)?.scalar);
        witness_comms.push(transcript_chip.write_commitment(layouter, &grumpkin_random)?);
        // witness_comms.push(transcript_chip.read_commitment(layouter)?);
        // challenges.push(transcript_chip.squeeze_challenge(layouter.namespace(|| "transcript_chip"))?.scalar);
        let challenge3 = transcript_chip.squeeze_challenge(layouter)?.scalar;
        challenges.extend(main_chip.powers_base(layouter, &challenge3, 6)?.into_iter().skip(1).take(5).collect::<Vec<_>>()); // num_alpha_primes

        let nark = AssignedPlonkishNarkInstance::new(vec![instances], challenges, witness_comms);
        transcript_chip.absorb_accumulator(acc)?;
        let (cross_term_comms, compressed_cross_term_sums) = match strategy {
            NoCompressing => {
                let cross_term_comms = 
                transcript_chip.read_commitments(layouter, *num_cross_terms)?;
                (cross_term_comms, None)
            }
            Compressing => {
                // let zeta_cross_term_comm = vec![transcript_chip.read_commitment(layouter)?];
                let zeta_cross_term_comm = vec![transcript_chip.write_commitment(layouter, &grumpkin_random)?];
                // let compressed_cross_term_sums =
                //     transcript_chip.read_field_elements(layouter, *num_cross_terms)?;
                let compressed_cross_term_sums =
                    transcript_chip.write_field_elements(layouter, &[C::Base::ONE; 9])?;
                (zeta_cross_term_comm, Some(compressed_cross_term_sums))
            }
        };

        let r = transcript_chip.squeeze_challenge(layouter)?;
        let r_le_bits = r.le_bits.clone();

        let acc_prime = self.fold_accumulator_from_nark_ec(
            layouter,
            acc,
            &nark,
            &cross_term_comms,
            compressed_cross_term_sums.as_deref(),
            r.as_ref(),
            &r_le_bits,
        )?;

        Ok((nark, acc_prime))
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    fn fold_accumulator_from_nark(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            Self::Num,
            Self::Ecc,
        >,
        nark: &AssignedPlonkishNarkInstance<
            Self::Num, 
            Self::Ecc
        >,
        cross_term_comms: &[Self::Ecc],
        compressed_cross_term_sums: Option<&[Self::Num]>,
        r: &Self::Num,
        r_le_bits: &[Self::Num],
        assigned_cyclefold_instances: Vec<Self::Ecc>
    ) -> Result<
        AssignedProtostarAccumulatorInstance<
        Self::Num, 
        Self::Ecc
        >,
        Error,
    > {
        let main_chip = &self.main_chip;
        let ProtostarAccumulationVerifierParam {
            strategy,
            num_cross_terms,
            ..
        } = self.avp;

        let powers_of_r = main_chip.powers(layouter, r, num_cross_terms + 1)?;
        
        // skip folding witness_comms
        let r_nark_instances = nark
            .instances
            .iter()
            .map(|instances| {
                instances
                    .iter()
                    .map(|instance| main_chip.mul(layouter, r, instance))
                    .try_collect::<_, Vec<_>, _>()
            })
            .try_collect::<_, Vec<_>, _>()?;

        let r_nark_challenges = nark
            .challenges
            .iter()
            .map(|challenge| main_chip.mul(layouter, r, challenge))
            .try_collect::<_, Vec<_>, _>()?;

        let acc_prime = {
            let instances = izip_eq!(&acc.instances, &r_nark_instances)
                .map(|(lhs, rhs)| {
                    izip_eq!(lhs, rhs)
                        .map(|(lhs, rhs)| main_chip.add(layouter, lhs, rhs))
                        .try_collect::<_, Vec<_>, _>()
                })
                .try_collect::<_, Vec<_>, _>()?;
            let witness_comms = assigned_cyclefold_instances[..assigned_cyclefold_instances.len() - 1].to_vec();
            let challenges = izip_eq!(&acc.challenges, &r_nark_challenges)
                .map(|(lhs, rhs)| main_chip.add(layouter, lhs, rhs))
                .try_collect::<_, Vec<_>, _>()?;

            let u = main_chip.add(layouter, &acc.u, r)?;
            let e_comm = if cross_term_comms.is_empty() {
                acc.e_comm.clone()
            } else {
                assigned_cyclefold_instances.last().unwrap().clone()
            };

            let compressed_e_sum = match strategy {
                NoCompressing => None,
                Compressing => {
                    let rhs = main_chip.inner_product(
                        layouter,
                        &powers_of_r[1..],
                        compressed_cross_term_sums.unwrap(),
                    )?;
                    Some(main_chip.add(
                        layouter,
                        acc.compressed_e_sum.as_ref().unwrap(),
                        &rhs,
                    )?)
                }
            };

            ProtostarAccumulatorInstance {
                instances,
                witness_comms,
                challenges,
                u,
                e_comm,
                compressed_e_sum,
            }
        };

        Ok(acc_prime)
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    fn fold_accumulator_from_nark_ec(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        acc: &AssignedProtostarAccumulatorInstance<
            Self::NonNatNum,
            Self::NatEcc,
        >,
        nark: &AssignedPlonkishNarkInstance<
            Self::NonNatNum, 
            Self::NatEcc
        >,
        cross_term_comms: &[Self::NatEcc],
        compressed_cross_term_sums: Option<&[Self::NonNatNum]>,
        r: &Self::NonNatNum,
        r_le_bits: &[Self::Num],
    ) -> Result<
        AssignedProtostarAccumulatorInstance<Self::NonNatNum, Self::NatEcc>,
        Error,
    > {
        let main_chip = &self.main_chip;
        let ProtostarAccumulationVerifierParam {
            strategy,
            num_cross_terms,
            ..
        } = self.avp;

        let powers_of_r = main_chip.powers_base(layouter, r, num_cross_terms + 1)?;
        let acc_prime = {
            let instances = izip_eq!(&acc.instances, &nark.instances)
                .map(|(lhs, rhs)| {
                    izip_eq!(lhs, rhs)
                        .map(|(lhs, rhs)| {
                            let no_mod = main_chip.mul_add_base(layouter, r, lhs, rhs)?;
                            main_chip.mod_reduce(layouter, no_mod)
                        })
                        .try_collect::<_, Vec<_>, _>()
                })
                .try_collect::<_, Vec<_>, _>()?;
            let witness_comms = izip_eq!(&nark.witness_comms, &acc.witness_comms)
                .map(|(lhs, rhs)| {
                    self.sm_chip.assign(layouter.namespace(|| "acc_prime_witness_comms"), r_le_bits.to_vec(), lhs, rhs)
                })
                .try_collect::<_, Vec<_>, _>()?;
            let challenges = izip_eq!(&acc.challenges, &nark.challenges)
                .map(|(lhs, rhs)| {
                    let no_mod = main_chip.mul_add_base(layouter, r, lhs, rhs)?;
                    main_chip.mod_reduce(layouter, no_mod)
                })
                .try_collect::<_, Vec<_>, _>()?;
            let no_mod_u = main_chip.add_base(layouter, &acc.u, r)?;
            let u = main_chip.mod_reduce(layouter, no_mod_u)?;
            let e_comm = if cross_term_comms.is_empty() {
                acc.e_comm.clone()
            } else {
                let mut e_comm = cross_term_comms.last().unwrap().clone();
                for item in cross_term_comms.iter().rev().skip(1).chain([&acc.e_comm]) {
                    e_comm = self.sm_chip.assign(layouter.namespace(|| "acc_prime_witness_comms"), r_le_bits.to_vec(), &e_comm, item)?;
                }
                e_comm
            };

            let compressed_e_sum = match strategy {
                NoCompressing => None,
                Compressing => {
                    let rhs_no_mod = main_chip.inner_product_base(
                        layouter,
                        &powers_of_r[1..],
                        compressed_cross_term_sums.unwrap(),
                    )?;
                    let rhs = main_chip.mod_reduce(layouter, rhs_no_mod)?;
                    let compressed_e_sum_no_mod = main_chip.add_base(
                        layouter,
                        acc.compressed_e_sum.as_ref().unwrap(),
                        &rhs,
                    )?;
                    Some(main_chip.mod_reduce(
                        layouter,
                        compressed_e_sum_no_mod,
                    )?)
                }
            };

            ProtostarAccumulatorInstance {
                instances,
                witness_comms,
                challenges,
                u,
                e_comm,
                compressed_e_sum,
            }
        };

        Ok(acc_prime)
    }

    fn select_accumulator(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        condition: &Self::Num,
        when_true: &AssignedProtostarAccumulatorInstance<
            Self::Num,
            Self::Ecc,
        >,
        when_false: &AssignedProtostarAccumulatorInstance<
            Self::Num,
            Self::Ecc,
        >,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<Self::Num, Self::Ecc>,
        Error,
    > {
        let main_chip = &self.main_chip;
        let instances = izip_eq!(&when_true.instances, &when_false.instances)
            .map(|(when_true, when_false)| {
                izip_eq!(when_true, when_false)
                    .map(|(when_true, when_false)| {
                        main_chip.select(layouter, condition, when_true, when_false)
                    })
                    .try_collect()
            })
            .try_collect()?;
        let witness_comms = izip_eq!(&when_true.witness_comms, &when_false.witness_comms)
            .map(|(when_true, when_false)| {
                main_chip.select_primary(layouter, condition, when_true, when_false)
            })
            .try_collect()?;
        let challenges = izip_eq!(&when_true.challenges, &when_false.challenges)
            .map(|(when_true, when_false)| {
                main_chip.select(layouter, condition, when_true, when_false)
            })
            .try_collect()?;
        let u = main_chip.select(layouter, condition, &when_true.u, &when_false.u)?;
        let e_comm = main_chip.select_primary(
            layouter,
            condition,
            &when_true.e_comm,
            &when_false.e_comm,
        )?;
        let compressed_e_sum = match self.avp.strategy {
            NoCompressing => None,
            Compressing => Some(main_chip.select(
                layouter,
                condition,
                when_true.compressed_e_sum.as_ref().unwrap(),
                when_false.compressed_e_sum.as_ref().unwrap(),
            )?),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }

    fn select_accumulator_ec(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        condition: &Self::Num,
        when_true: &AssignedProtostarAccumulatorInstance<
            Self::NonNatNum,
            Self::NatEcc,
        >,
        when_false: &AssignedProtostarAccumulatorInstance<
            Self::NonNatNum,
            Self::NatEcc,
        >,
    ) -> Result<
        AssignedProtostarAccumulatorInstance<Self::NonNatNum, Self::NatEcc>,
        Error,
    > {

        let main_chip = &self.main_chip;
        let instances = izip_eq!(&when_true.instances, &when_false.instances)
            .map(|(when_true, when_false)| {
                izip_eq!(when_true, when_false)
                    .map(|(when_true, when_false)| {
                        main_chip.select_base(layouter, condition, when_true, when_false)
                    })
                    .try_collect()
            })
            .try_collect()?;

        let witness_comms = izip_eq!(&when_true.witness_comms, &when_false.witness_comms)
            .map(|(when_true, when_false)| {
                main_chip.select_secondary(layouter, condition, when_true, when_false)
            })
            .try_collect()?;

        let challenges = izip_eq!(&when_true.challenges, &when_false.challenges)
            .map(|(when_true, when_false)| {
                main_chip.select_base(layouter, condition, when_true, when_false)
            })
            .try_collect()?;

        let u = main_chip.select_base(layouter, condition, &when_true.u, &when_false.u)?;
        let e_comm = main_chip.select_secondary(
            layouter,
            condition,
            &when_true.e_comm,
            &when_false.e_comm,
        )?;

        let compressed_e_sum = match self.avp.strategy {
            NoCompressing => None,
            Compressing => Some(main_chip.select_base(
                layouter,
                condition,
                when_true.compressed_e_sum.as_ref().unwrap(),
                when_false.compressed_e_sum.as_ref().unwrap(),
            )?),
        };

        Ok(ProtostarAccumulatorInstance {
            instances,
            witness_comms,
            challenges,
            u,
            e_comm,
            compressed_e_sum,
        })
    }
}

#[derive(Debug)]
pub struct ProtostarIvcProverParam<C, P1, P2, AT1, AT2>
where
    C: TwoChainCurve,
    HyperPlonk<P1>: PlonkishBackend<C::Scalar>,
    HyperPlonk<P2>: PlonkishBackend<C::Base>,
    AT1: InMemoryTranscript,
    AT2: InMemoryTranscript,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    primary_pp: ProtostarProverParam<C::Scalar, HyperPlonk<P1>>,
    primary_atp: AT1::Param,
    cyclefold_pp: ProtostarProverParam<C::Base, HyperPlonk<P2>>,
    cyclefold_atp: AT2::Param,
    _marker: PhantomData<(C, AT1, AT2)>,
}

#[derive(Debug)]
pub struct ProtostarIvcVerifierParam<C, P1, P2>
where
    C: TwoChainCurve,
    HyperPlonk<P1>: PlonkishBackend<C::Scalar>,
    HyperPlonk<P2>: PlonkishBackend<C::Base>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    vp_digest: C::Scalar,
    primary_vp: ProtostarVerifierParam<C::Scalar, HyperPlonk<P1>>,
    primary_hp: Poseidon2ChipSpec,
    primary_arity: usize,
    cyclefold_vp: ProtostarVerifierParam<C::Base, HyperPlonk<P2>>,
    cyclefold_hp: Poseidon2ChipSpec,
    cyclefold_arity: usize,
    _marker: PhantomData<C>,
}

impl<C, P1, P2> ProtostarIvcVerifierParam<C, P1, P2>
where
    C: TwoChainCurve,
    HyperPlonk<P1>: PlonkishBackend<C::Scalar>,
    HyperPlonk<P2>: PlonkishBackend<C::Base>,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,

{
    pub fn primary_arity(&self) -> usize {
        self.primary_arity
    }

    pub fn cyclefold_arity(&self) -> usize {
        self.cyclefold_arity
    }
}

#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn preprocess<C, P1, P2, S1, AT1, AT2>(
    primary_num_vars: usize,
    primary_param: P1::Param,
    primary_atp: AT1::Param,
    primary_step_circuit: S1,
    cyclefold_num_vars: usize,
    cyclefold_param: P2::Param,
    cyclefold_atp: AT2::Param,
    mut rng: impl RngCore,
) -> Result<
    (
        Halo2Circuit<C::Scalar, PrimaryCircuit<C, S1>>,
        Halo2Circuit<C::Base, CycleFoldCircuit<C::Secondary>>,
        ProtostarIvcProverParam<C, P1, P2, AT1, AT2>,
        ProtostarIvcVerifierParam<
            C,
            P1,
            P2,
        >,
    ),
    Error,
>
where
    C: TwoChainCurve,
    C::Scalar: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    P1: PolynomialCommitmentScheme<
        C::ScalarExt,
        Polynomial = MultilinearPolynomial<C::Scalar>,
        CommitmentChunk = C,
    >,
    P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
    P2: PolynomialCommitmentScheme<
        C::Base,
        Polynomial = MultilinearPolynomial<C::Base>,
        CommitmentChunk = C::Secondary,
    >,
    P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
    S1: StepCircuit<C>,
    AT1: InMemoryTranscript,
    AT2: InMemoryTranscript,
{
    // assert_eq!(Chip::<C>::NUM_HASH_BITS, Chip::<C::Secondary>::NUM_HASH_BITS);
    // let primary_param = P1::setup(1 << (primary_num_vars + 4), 0, &mut rng).unwrap();
    // let cyclefold_param = P2::setup(1 << (cyclefold_num_vars + 4), 0, &mut rng).unwrap(); // todo change this
    let primary_circuit = PrimaryCircuit::new(true, primary_step_circuit, None, None);
    let mut primary_circuit =
        Halo2Circuit::new::<HyperPlonk<P1>>(primary_num_vars, primary_circuit, ());

    let ( _, primary_vp_without_preprocess) = {
        let primary_circuit_info = primary_circuit.circuit_info_without_preprocess().unwrap();
            Protostar::<HyperPlonk<P1>>::preprocess(&primary_param, &primary_circuit_info).unwrap()
        };

    let cyclefold_circuit = CycleFoldCircuit::new(
        Some(ProtostarAccumulationVerifierParam::from(&*primary_vp_without_preprocess)));
    let mut cyclefold_circuit =
            Halo2Circuit::new::<HyperPlonk<P2>>(cyclefold_num_vars, cyclefold_circuit, ());
        
    let (cyclefold_pp, cyclefold_vp) = {
            let timer = start_timer(|| "preprocess cyclefold circuit_info");
            let cyclefold_circuit_info = cyclefold_circuit.circuit_info().unwrap();
            cyclefold_circuit.floor_planner_data();
            end_timer(timer);
            Protostar::<HyperPlonk<P2>>::preprocess(&cyclefold_param, &cyclefold_circuit_info).unwrap()
    };

    primary_circuit.update_witness(|circuit| {
            circuit.primary_avp = ProtostarAccumulationVerifierParam::from(&*primary_vp_without_preprocess);
            circuit.cyclefold_avp = ProtostarAccumulationVerifierParam::from(&*cyclefold_vp);
            circuit.update_acc();
    });

    let timer = start_timer(|| "preprocess primary circuit_info twice");
    let primary_circuit_info = primary_circuit.circuit_info().unwrap();
    primary_circuit.floor_planner_data();
    end_timer(timer);
    let (primary_pp, primary_vp) =
        Protostar::<HyperPlonk<P1>>::preprocess(&primary_param, &primary_circuit_info).unwrap();

    let num_bits = NUM_HASH_BITS; //Chip::<C>::NUM_HASH_BITS
    let vp_digest = fe_truncated_from_le_bytes(
        Keccak256::digest(bincode::serialize(&(&primary_vp, &cyclefold_vp)).unwrap()),
        num_bits,
    );
    primary_circuit.update_witness(|circuit| circuit.init(vp_digest));
    cyclefold_circuit.update_witness(|circuit| circuit.init(fe_to_fe(vp_digest)));

    let ivc_pp = ProtostarIvcProverParam {
        primary_pp: *primary_pp,
        primary_atp,
        cyclefold_pp: *cyclefold_pp,
        cyclefold_atp,
        _marker: PhantomData,
    };
    let ivc_vp = {
        ProtostarIvcVerifierParam {
            vp_digest,
            primary_vp: *primary_vp,
            primary_hp: primary_circuit.circuit().hash_config.clone(),
            primary_arity: S1::arity(),
            cyclefold_vp: *cyclefold_vp,
            cyclefold_hp: cyclefold_circuit.circuit().hash_config.clone(),
            // TODO CHECK THIS
            cyclefold_arity: CF_IO_LEN,
            _marker: PhantomData,
        }
    };

    Ok((primary_circuit, cyclefold_circuit, ivc_pp, ivc_vp))
}

#[allow(clippy::type_complexity)]
pub fn prove_steps<C, P1, P2, S1, AT1, AT2>(
    ivc_pp: &ProtostarIvcProverParam<C, P1, P2, AT1, AT2>,
    primary_circuit: &mut Halo2Circuit<C::Scalar, PrimaryCircuit<C, S1>>,
    cyclefold_circuit: &mut Halo2Circuit<C::Base, CycleFoldCircuit<C::Secondary>>,
    num_steps: usize,
    mut rng: impl RngCore,
) -> Result<
    (
        ProtostarAccumulator<C::Scalar, P1>,
        ProtostarAccumulator<C::Base, P2>,
    ),
    crate::Error,
>
where
    C: TwoChainCurve,
    C::Scalar: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
    P1: PolynomialCommitmentScheme<
        C::ScalarExt,
        Polynomial = MultilinearPolynomial<C::Scalar>,
        CommitmentChunk = C,
    >,
    P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
    P2: PolynomialCommitmentScheme<
        C::Base,
        Polynomial = MultilinearPolynomial<C::Base>,
        CommitmentChunk = C::Secondary,
    >,
    P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
    S1: StepCircuit<C>,
    AT1: TranscriptRead<P1::CommitmentChunk, C::Scalar>
        + TranscriptWrite<P1::CommitmentChunk, C::Scalar>
        + InMemoryTranscript,
    AT2: TranscriptRead<P2::CommitmentChunk, C::Base>
        + TranscriptWrite<P2::CommitmentChunk, C::Base>
        + InMemoryTranscript,

{
    let mut primary_acc = Protostar::<HyperPlonk<P1>>::init_accumulator(&ivc_pp.primary_pp)?;
    let mut primary_acc_ec = Protostar::<HyperPlonk<P2>>::init_accumulator_ec(&ivc_pp.cyclefold_pp)?;

    for step_idx in 0..num_steps {

        let primary_acc_ec_x = primary_acc_ec.instance.clone();        
        let primary_acc_x = primary_acc.instance.clone();

        let timer = start_timer(|| {
            format!(
                "prove_accumulation_from_nark-primary-{}",
                ivc_pp.primary_pp.pp.num_vars
            )
        });

        let (r_le_bits, r, primary_nark_x, cross_term_comms, primary_proof) = {
            let mut primary_transcript = AT1::new(ivc_pp.primary_atp.clone());
            let (r_le_bits, r, primary_nark_as_acc, cross_term_comms) = Protostar::<HyperPlonk<P1>>::prove_accumulation_from_nark(
                    &ivc_pp.primary_pp,
                    &mut primary_acc,
                    primary_circuit as &_,
                    &mut primary_transcript,
                    &mut rng,
                )?;
                (r_le_bits, r, primary_nark_as_acc.instance, cross_term_comms, primary_transcript.into_proof())
            };
        end_timer(timer);

        let primary_instances = primary_circuit.instances()[0].clone().try_into().unwrap();

        primary_circuit.update_witness(|circuit| {
                circuit.update_both_running_instances(
                    r_le_bits.clone(), 
                    primary_nark_x.witness_comms.clone(), 
                    cross_term_comms.clone(),
                    primary_acc_x.clone(),
                    primary_acc.instance.clone(),
                    primary_instances,
                    primary_proof.clone(),
                    primary_acc_ec_x.clone(),
                    primary_acc_ec.instance.clone(),
                );
            });

            cyclefold_circuit.update_witness(|circuit| {
                circuit.update_cyclefold_inputs(
                    r_le_bits.iter().map(|b| fe_to_fe(*b)).collect_vec(),
                    r,
                    cross_term_comms,
                    primary_nark_x,
                    primary_acc_x,
                    primary_acc.instance.clone(),
                );
            });

        if step_idx != num_steps - 1 {
            let timer = start_timer(|| {
                    format!(
                        "prove_accumulation_from_nark_ec-primary-{}",
                        ivc_pp.cyclefold_pp.pp.num_vars
                    )
            });
    
            let cyclefold_proof = {
                let mut cyclefold_transcript = AT2::new(ivc_pp.cyclefold_atp.clone());
                    Protostar::<HyperPlonk<P2>>::prove_accumulation_from_nark_ec(
                        &ivc_pp.cyclefold_pp,
                        &mut primary_acc_ec,
                        cyclefold_circuit as &_,
                        &mut cyclefold_transcript,
                        &mut rng,
                    )?;
                    cyclefold_transcript.into_proof()
                };



            primary_circuit.update_witness(|circuit| {
                circuit.update_from_cyclefold(
                    cyclefold_proof,
                    cyclefold_circuit.instances()[0].clone().try_into().unwrap(),
                    primary_acc_ec_x,
                    primary_acc_ec.instance.clone(),
                );
                // MockProver::run(14, circuit, vec![]).unwrap().assert_satisfied();
            });

        } else {
            return Ok((
                primary_acc,
                primary_acc_ec,
            ))
        }
    }
    unreachable!()
}

// pub fn prove_decider<C, P1, P2, AT1, AT2>(
//     ivc_pp: &ProtostarIvcProverParam<C, P1, P2, AT1, AT2>,
//     primary_acc: &ProtostarAccumulator<C::Scalar, P1>,
//     primary_transcript: &mut impl TranscriptWrite<P1::CommitmentChunk, C::Scalar>,
//     mut rng: impl RngCore,
// ) -> Result<(), crate::Error>
// where
//     C: TwoChainCurve,
//     C::Scalar: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
//     C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
//     P1: PolynomialCommitmentScheme<
//         C::ScalarExt,
//         Polynomial = MultilinearPolynomial<C::Scalar>,
//         CommitmentChunk = C,
//     >,
//     P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
//     P2: PolynomialCommitmentScheme<
//         C::Base,
//         Polynomial = MultilinearPolynomial<C::Base>,
//         CommitmentChunk = C::Secondary,
//     >,
//     P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
//     AT1: InMemoryTranscript,
//     AT2: InMemoryTranscript,
// {
//     // let timer = start_timer(|| format!("prove_decider-primary-{}", ivc_pp.primary_pp.pp.num_vars));
//     // Protostar::<HyperPlonk<P1>>::prove_decider(
//     //     &ivc_pp.primary_pp,
//     //     primary_acc,
//     //     primary_transcript,
//     //     &mut rng,
//     // )?;
//     // end_timer(timer);
//     Ok(())
// }

// #[allow(clippy::too_many_arguments)]
// pub fn verify_decider<C, P1, P2>(
//     ivc_vp: &ProtostarIvcVerifierParam<C, P1, P2>,
//     primary_acc: &ProtostarAccumulatorInstance<C::Scalar, P1::Commitment>,
//     primary_transcript: &mut impl TranscriptRead<P1::CommitmentChunk, C::Scalar>,
//     mut rng: impl RngCore,
// ) -> Result<(), crate::Error>
// where
//     C: TwoChainCurve,
//     C::Scalar: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
//     C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
//     P1: PolynomialCommitmentScheme<
//         C::ScalarExt,
//         Polynomial = MultilinearPolynomial<C::Scalar>,
//         CommitmentChunk = C,
//     >,
//     P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
//     P2: PolynomialCommitmentScheme<
//         C::Base,
//         Polynomial = MultilinearPolynomial<C::Base>,
//         CommitmentChunk = C::Secondary,
//     >,
//     P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
// {
//     // Protostar::<HyperPlonk<P1>>::verify_decider(
//     //     &ivc_vp.primary_vp,
//     //     primary_acc,
//     //     primary_transcript,
//     //     &mut rng,
//     // )?;
//     Ok(())
// }

// // todo change prove_decider_with_last_nark to prove_decider_ec
// // pub fn prove_decider<C, P1, P2, AT1, AT2>(
// //     ivc_pp: &ProtostarIvcProverParam<C, P1, P2, AT1, AT2>,
// //     primary_acc: &ProtostarAccumulator<C::Scalar, P1>,
// //     primary_transcript: &mut impl TranscriptWrite<P1::CommitmentChunk, C::Scalar>,
// //     secondary_acc: &mut ProtostarAccumulator<C::Base, P2>,
// //     secondary_circuit: &impl PlonkishCircuit<C::Base>,
// //     secondary_transcript: &mut impl TranscriptWrite<P2::CommitmentChunk, C::Base>,
// //     mut rng: impl RngCore,
// // ) -> Result<(), crate::Error>
// // where
// //     C: TwoChainCurve,
// //     C::Scalar: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
// //     C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
// //     P1: PolynomialCommitmentScheme<
// //         C::ScalarExt,
// //         Polynomial = MultilinearPolynomial<C::Scalar>,
// //         CommitmentChunk = C,
// //     >,
// //     P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
// //     P2: PolynomialCommitmentScheme<
// //         C::Base,
// //         Polynomial = MultilinearPolynomial<C::Base>,
// //         CommitmentChunk = C::Secondary,
// //     >,
// //     P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
// //     AT1: InMemoryTranscript,
// //     AT2: InMemoryTranscript,

// // {
// //     let timer = start_timer(|| format!("prove_decider-primary-{}", ivc_pp.primary_pp.pp.num_vars));
// //     Protostar::<HyperPlonk<P1>>::prove_decider(
// //         &ivc_pp.primary_pp,
// //         primary_acc,
// //         primary_transcript,
// //         &mut rng,
// //     )?;
// //     end_timer(timer);
// //     let timer = start_timer(|| {
// //         format!(
// //             "prove_decider_with_last_nark-secondary-{}",
// //             ivc_pp.secondary_pp.pp.num_vars
// //         )
// //     });
// //     Protostar::<HyperPlonk<P2>>::prove_decider_with_last_nark(
// //         &ivc_pp.secondary_pp,
// //         secondary_acc,
// //         secondary_circuit,
// //         secondary_transcript,
// //         &mut rng,
// //     )?;
// //     end_timer(timer);
// //     Ok(())
// // }

// // #[allow(clippy::too_many_arguments)]
// // pub fn verify_decider<C, P1, P2>(
// //     ivc_vp: &ProtostarIvcVerifierParam<C, P1, P2>,
// //     num_steps: usize,
// //     primary_initial_input: &[C::Scalar],
// //     primary_output: &[C::Scalar],
// //     primary_acc: &ProtostarAccumulatorInstance<C::Scalar, P1::Commitment>,
// //     primary_transcript: &mut impl TranscriptRead<P1::CommitmentChunk, C::Scalar>,
// //     secondary_initial_input: &[C::Base],
// //     secondary_output: &[C::Base],
// //     secondary_acc_before_last: impl BorrowMut<ProtostarAccumulatorInstance<C::Base, P2::Commitment>>,
// //     secondary_last_instances: &[Vec<C::Base>],
// //     secondary_transcript: &mut impl TranscriptRead<P2::CommitmentChunk, C::Base>,
// //     mut rng: impl RngCore,
// // ) -> Result<(), crate::Error>
// // where
// //     C: TwoChainCurve,
// //     C::Scalar: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
// //     C::Base: Hash + Serialize + DeserializeOwned + BigPrimeField + PrimeFieldBits,
// //     P1: PolynomialCommitmentScheme<
// //         C::ScalarExt,
// //         Polynomial = MultilinearPolynomial<C::Scalar>,
// //         CommitmentChunk = C,
// //     >,
// //     P1::Commitment: AdditiveCommitment<C::Scalar> + AsRef<C> + From<C>,
// //     P2: PolynomialCommitmentScheme<
// //         C::Base,
// //         Polynomial = MultilinearPolynomial<C::Base>,
// //         CommitmentChunk = C::Secondary,
// //     >,
// //     P2::Commitment: AdditiveCommitment<C::Base> + AsRef<C::Secondary> + From<C::Secondary>,
// // {
// //     if Chip::<C>::hash_state(
// //         &ivc_vp.primary_hp,
// //         ivc_vp.vp_digest,
// //         num_steps,
// //         primary_initial_input,
// //         primary_output,
// //         secondary_acc_before_last.borrow(),
// //     ) != fe_to_fe(secondary_last_instances[0][0])
// //     {
// //         return Err(crate::Error::InvalidSnark(
// //             "Invalid primary state hash".to_string(),
// //         ));
// //     }
// //     if Chip::<C::Secondary>::hash_state(
// //         &ivc_vp.secondary_hp,
// //         fe_to_fe(ivc_vp.vp_digest),
// //         num_steps,
// //         secondary_initial_input,
// //         secondary_output,
// //         primary_acc,
// //     ) != secondary_last_instances[0][1]
// //     {
// //         return Err(crate::Error::InvalidSnark(
// //             "Invalid secondary state hash".to_string(),
// //         ));
// //     }

// //     Protostar::<HyperPlonk<P1>>::verify_decider(
// //         &ivc_vp.primary_vp,
// //         primary_acc,
// //         primary_transcript,
// //         &mut rng,
// //     )?;
// //     Protostar::<HyperPlonk<P2>>::verify_decider_with_last_nark(
// //         &ivc_vp.secondary_vp,
// //         secondary_acc_before_last,
// //         secondary_last_instances,
// //         secondary_transcript,
// //         &mut rng,
// //     )?;
// //     Ok(())
// // }