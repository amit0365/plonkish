use crate::{
    accumulation::{
        protostar::{
            hyperplonk::{
                preprocessor::{batch_size, preprocess},
                prover::{
                    evaluate_compressed_cross_term_sums, evaluate_cross_term_polys,
                    evaluate_zeta_cross_term_poly, lookup_h_polys, powers_of_zeta_poly, PolynomialsHolder,
                },
            },
            ivc::ProtostarAccumulationVerifierParam,
            Protostar, ProtostarAccumulator, ProtostarAccumulatorInstance, ProtostarProverParam,
            ProtostarStrategy::{Compressing, NoCompressing},
            ProtostarVerifierParam,
        },
        AccumulationScheme, PlonkishNark, PlonkishNarkInstance,
    },
    backend::{
        hyperplonk::{
            prover::{
                instance_polys, lookup_compressed_polys, lookup_m_polys, lookup_m_polys_uncompressed, lookup_uncompressed_polys, permutation_z_polys, prove_sum_check
            },
            verifier::verify_sum_check,
            HyperPlonk, HyperPlonkVerifierParam,
        },
        PlonkishBackend, PlonkishCircuit, PlonkishCircuitInfo,
    },
    pcs::{AdditiveCommitment, Commitment, CommitmentChunk, PolynomialCommitmentScheme},
    poly::{multilinear::{concat_polys, MultilinearPolynomial}, Polynomial},
    util::{
        arithmetic::{fe_from_bits_le, fe_to_bits_le, powers, PrimeField}, end_timer, expression_new::paired::Paired, start_timer, transcript::{TranscriptRead, TranscriptWrite}, DeserializeOwned, Itertools, Serialize
    },
    Error,
};
use halo2_proofs::halo2curves::ff::PrimeFieldBits;
use rand::RngCore;
use core::time;
use std::{borrow::{Borrow, BorrowMut}, collections::HashMap, hash::Hash, iter::{self, once}};
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelRefIterator;
mod preprocessor;
pub mod prover;

pub const NUM_CHALLENGE_BITS: usize = 128;

impl<F, Pcs, const STRATEGY: usize> AccumulationScheme<F> for Protostar<HyperPlonk<Pcs>, STRATEGY>
where
    F: PrimeField + Hash + Serialize + DeserializeOwned,
    Pcs: PolynomialCommitmentScheme<F, Polynomial = MultilinearPolynomial<F>>,
    Pcs::Commitment: AdditiveCommitment<F>,
    Pcs::CommitmentChunk: AdditiveCommitment<F>,
{
    type Pcs = Pcs;
    type ProverParam = ProtostarProverParam<F, HyperPlonk<Pcs>>;
    type VerifierParam = ProtostarVerifierParam<F, HyperPlonk<Pcs>>;
    type Accumulator = ProtostarAccumulator<F, Pcs>;
    type AccumulatorInstance = ProtostarAccumulatorInstance<F, Pcs::Commitment>;

    fn setup(
        circuit_info: &PlonkishCircuitInfo<F>,
        rng: impl RngCore,
    ) -> Result<Pcs::Param, Error> {
        assert!(circuit_info.is_well_formed());

        let num_vars = circuit_info.k;
        let poly_size = 1 << num_vars;
        let batch_size = batch_size(circuit_info, STRATEGY.into());
        Pcs::setup(poly_size, batch_size, rng)
    }

    fn preprocess(
        param: &Pcs::Param,
        circuit_info: &PlonkishCircuitInfo<F>,
    ) -> Result<(Box<Self::ProverParam>, Box<Self::VerifierParam>), Error> {
        assert!(circuit_info.is_well_formed());
        preprocess(param, circuit_info, STRATEGY.into())
            // .map(|(prover_param, verifier_param)| (*prover_param, *verifier_param))
    }

    // fn preprocess_ec(
    //     param: &Pcs::Param,
    //     circuit_info: &PlonkishCircuitInfo<F>,
    // ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
    //     assert!(circuit_info.is_well_formed());

    //     preprocess_ec(param, circuit_info, STRATEGY.into())
    // }

    fn init_accumulator(pp: &Self::ProverParam) -> Result<Self::Accumulator, Error> {
        Ok(ProtostarAccumulator::init(
            pp.strategy,
            pp.pp.num_vars,
            &pp.pp.num_instances,
            pp.num_folding_witness_polys,
            pp.num_folding_challenges,
        ))
    }

    fn init_accumulator_ec(pp: &Self::ProverParam) -> Result<Self::Accumulator, Error> {
        Ok(ProtostarAccumulator::init_ec(
            pp.strategy,
            pp.pp.num_vars,
            &pp.pp.num_instances,
            pp.num_folding_witness_polys,
            pp.num_folding_challenges,
        ))
    }

    fn init_accumulator_from_nark(
        pp: &Self::ProverParam,
        nark: PlonkishNark<F, Self::Pcs>,
    ) -> Result<Self::Accumulator, Error> {
        Ok(ProtostarAccumulator::from_nark(
            pp.strategy,
            pp.pp.num_vars,
            nark,
        ))
    }

    // fn prove_nark(
    //     pp: &Self::ProverParam,
    //     circuit: &impl PlonkishCircuit<F>,
    //     transcript: &mut impl TranscriptWrite<CommitmentChunk<F, Pcs>, F>,
    //     _: impl RngCore,
    // ) -> Result<PlonkishNark<F, Pcs>, Error> {
    //     let ProtostarProverParam {
    //         pp,
    //         strategy,
    //         num_theta_primes,
    //         num_alpha_primes,
    //         num_folding_witness_polys,
    //         ..
    //     } = pp;

    //     let instances = circuit.instances();
    //     for (num_instances, instances) in pp.num_instances.iter().zip_eq(instances) {
    //         assert_eq!(instances.len(), *num_instances);
    //         for instance in instances.iter() {
    //             transcript.common_field_element(instance)?;
    //         }
    //     }


    //     // Round 0..n

    //     let mut witness_polys = Vec::with_capacity(pp.num_witness_polys.iter().sum());
    //     let mut witness_comms = Vec::with_capacity(witness_polys.len());
    //     let mut challenges = Vec::with_capacity(pp.num_challenges.iter().sum());
    //     for (round, (num_witness_polys, num_challenges)) in pp
    //         .num_witness_polys
    //         .iter()
    //         .zip_eq(pp.num_challenges.iter())
    //         .enumerate()
    //     {
    //         let timer = start_timer(|| format!("witness_collector-{round}"));
    //         let polys = circuit
    //             .synthesize(round, &challenges)?
    //             .into_iter()
    //             .map(MultilinearPolynomial::new)
    //             .collect_vec();
    //         assert_eq!(polys.len(), *num_witness_polys);
    //         end_timer(timer);

    //         witness_comms.extend(Pcs::batch_commit_and_write(&pp.pcs, &polys, transcript)?);
    //         witness_polys.extend(polys);
    //         challenges.extend(transcript.squeeze_challenges(*num_challenges));
    //     }

    //     // Round n
    //     let theta_primes = powers(transcript.squeeze_challenge())
    //         .skip(1)
    //         .take(*num_theta_primes)
    //         .collect_vec();

    //     let timer = start_timer(|| format!("lookup_compressed_polys-{}", pp.lookups.len()));
    //     let lookup_compressed_polys = {
    //         let instance_polys = instance_polys(pp.num_vars, instances);
    //         let polys = iter::empty()
    //             .chain(instance_polys.iter())
    //             .chain(pp.preprocess_polys.iter())
    //             .chain(witness_polys.iter())
    //             .collect_vec();
    //         let thetas = iter::empty()
    //             .chain(Some(F::ONE))
    //             .chain(theta_primes.iter().cloned())
    //             .collect_vec();
    //         lookup_compressed_polys(&pp.lookups, &polys, &challenges, &thetas)
    //     };
    //     end_timer(timer);

    //     let timer = start_timer(|| format!("lookup_m_polys-{}", pp.lookups.len()));
    //     let lookup_m_polys = lookup_m_polys(&lookup_compressed_polys)?;
    //     end_timer(timer);

    //     let lookup_m_comms = Pcs::batch_commit_and_write(&pp.pcs, &lookup_m_polys, transcript)?;

    //     // Round n+1

    //     let beta_prime = transcript.squeeze_challenge();

    //     let timer = start_timer(|| format!("lookup_h_polys-{}", pp.lookups.len()));
    //     let lookup_h_polys = lookup_h_polys(&lookup_compressed_polys, &lookup_m_polys, &beta_prime);
    //     end_timer(timer);

    //     let lookup_h_comms = {
    //         let polys = lookup_h_polys.iter().flatten();
    //         Pcs::batch_commit_and_write(&pp.pcs, polys, transcript)?
    //     };

    //     // Round n+2

    //     let (zeta, powers_of_zeta_poly, powers_of_zeta_comm) = match strategy {
    //         NoCompressing => (None, None, None),
    //         Compressing => {
    //             let zeta = transcript.squeeze_challenge();

    //             let timer = start_timer(|| "powers_of_zeta_poly");
    //             let powers_of_zeta_poly = powers_of_zeta_poly(pp.num_vars, zeta);
    //             end_timer(timer);

    //             let powers_of_zeta_comm =
    //                 Pcs::commit_and_write(&pp.pcs, &powers_of_zeta_poly, transcript)?;

    //             (
    //                 Some(zeta),
    //                 Some(powers_of_zeta_poly),
    //                 Some(powers_of_zeta_comm),
    //             )
    //         }
    //     };

    //     // Round n+3
    //     let alpha_primes = powers(transcript.squeeze_challenge())
    //         .skip(1)
    //         .take(*num_alpha_primes)
    //         .collect_vec();

    //     let nark = PlonkishNark::new(
    //         instances.to_vec(),
    //         iter::empty()
    //             .chain(challenges)
    //             .chain(theta_primes)
    //             .chain(Some(beta_prime))
    //             .chain(zeta)
    //             .chain(alpha_primes)
    //             .collect(),
    //         iter::empty()
    //             .chain(witness_comms)
    //             .chain(lookup_m_comms)
    //             .chain(lookup_h_comms)
    //             .chain(powers_of_zeta_comm)
    //             .collect(),
    //         iter::empty()
    //             .chain(witness_polys)
    //             .chain(lookup_m_polys)
    //             .chain(lookup_h_polys.into_iter().flatten())
    //             .chain(powers_of_zeta_poly)
    //             .collect(),
    //     );

    //     Ok(nark)
    // }

    fn prove_nark(
        pp: &Self::ProverParam,
        circuit: &impl PlonkishCircuit<F>,
        transcript: &mut impl TranscriptWrite<CommitmentChunk<F, Pcs>, F>,
        _: impl RngCore,
    ) -> Result<PlonkishNark<F, Pcs>, Error> {
        let ProtostarProverParam {
            pp,
            strategy,
            num_theta_primes,
            num_alpha_primes,
            ..
        } = pp;
        let timer = start_timer(|| "instances");
        let instances = circuit.instances();
        for (num_instances, instances) in pp.num_instances.iter().zip_eq(instances) {
            assert_eq!(instances.len(), *num_instances);
            for instance in instances.iter() {
                transcript.common_field_element(instance)?;
            }
        }

        let num_witness_polys = pp.num_witness_polys.iter().sum::<usize>();
        // num_challenges = 0 since all witness_polys are in one phase.
        // Round 0

        let mut witness_polys = Vec::with_capacity(pp.num_witness_polys.iter().sum());
        let mut challenges = Vec::with_capacity(pp.num_challenges.iter().sum());

        for (round, (num_witness_polys, num_challenges)) in pp
            .num_witness_polys
            .iter()
            .zip_eq(pp.num_challenges.iter())
            .enumerate()
        {
            let timer = start_timer(|| format!("witness_collector-{round}"));
            let polys = circuit
                .synthesize(round, &challenges)?
                .into_iter()
                .map(MultilinearPolynomial::new)
                .collect_vec();
            assert_eq!(polys.len(), *num_witness_polys);
            end_timer(timer);

            witness_polys.extend(polys);
            challenges.extend(transcript.squeeze_challenges(*num_challenges));
        }

        let timer = start_timer(|| format!("lookup_uncompressed_polys-{}", pp.lookups.len()));
        let lookup_uncompressed_polys = {
            let instance_polys = instance_polys(pp.num_vars, instances);
            let polys = iter::empty()
                .chain(instance_polys.iter())
                .chain(pp.preprocess_polys.iter())
                .chain(witness_polys.iter())
                .collect_vec();
            lookup_uncompressed_polys(&pp.lookups, &polys, &challenges)
        };
        end_timer(timer);

        let timer = start_timer(|| format!("lookup_m_polys-{}", pp.lookups.len()));
        let lookup_m_polys = lookup_m_polys_uncompressed(&lookup_uncompressed_polys)?;
        end_timer(timer);

        let mut phase1_poly = witness_polys.clone(); 
        phase1_poly.extend(lookup_m_polys.iter().cloned());


        let phase1_poly_concat = concat_polys(phase1_poly);
        println!("witness_polys_len {:?}", witness_polys.len());
        println!("lookup_m_polys_len {:?}", lookup_m_polys.len());
        println!("phase1_poly_concat_num_vars {:?}", phase1_poly_concat.num_vars());
        let phase1_comm = Pcs::commit_and_write(&pp.pcs, &phase1_poly_concat, transcript)?;

        // Round 1
        // reuse the challenge to compress vector lookups
        // todo add another challenge cant reuse
        let beta_prime = transcript.squeeze_challenge();
        let theta_primes = powers(beta_prime)
            .skip(2)
            .take(*num_theta_primes)
            .collect_vec();

        let timer = start_timer(|| format!("lookup_compressed_polys-{}", pp.lookups.len()));
        let lookup_compressed_polys = {
            let instance_polys = instance_polys(pp.num_vars, instances);
            let polys = iter::empty()
                .chain(instance_polys.iter())
                .chain(pp.preprocess_polys.iter())
                .chain(witness_polys.iter())
                .collect_vec();
            let thetas = iter::empty()
                .chain(Some(F::ONE))
                .chain(theta_primes.iter().cloned())
                .collect_vec();
            lookup_compressed_polys(&pp.lookups, &polys, &challenges, &thetas)
        };
        end_timer(timer);

        let timer = start_timer(|| format!("lookup_h_polys-{}", pp.lookups.len()));
        let lookup_h_polys = lookup_h_polys(&lookup_compressed_polys, &lookup_m_polys, &beta_prime);
        end_timer(timer);

        let lookup_h_poly_vec = lookup_h_polys.clone().into_iter().flatten().collect_vec();

        let powers_of_zeta_poly = match strategy {
            NoCompressing => Vec::new(),
            Compressing => {
                let timer = start_timer(|| "powers_of_zeta_poly");
                let powers_of_zeta_poly = powers_of_zeta_poly(pp.num_vars, beta_prime);
                end_timer(timer);

                vec![powers_of_zeta_poly]
            }
        };

        let phase2_poly = [lookup_h_poly_vec.clone(), powers_of_zeta_poly.clone()].concat();
        let phase2_poly_concat =  concat_polys(phase2_poly);
        let phase2_comm = Pcs::commit_and_write(&pp.pcs, &phase2_poly_concat, transcript)?;

        // Round 2
        let alpha_primes = powers(transcript.squeeze_challenge())
            .skip(1)
            .take(*num_alpha_primes)
            .collect_vec();

        Ok(PlonkishNark::new(
            instances.to_vec(),
            iter::empty()
                .chain(challenges)
                .chain(Some(beta_prime))
                .chain(theta_primes)
                .chain(alpha_primes)
                .collect(),
            iter::empty()
                .chain([phase1_comm])
                .chain([phase2_comm])
                .collect(),
            iter::empty()
                .chain(witness_polys)
                .chain(lookup_m_polys)
                .chain(lookup_h_polys.into_iter().flatten())
                .chain(powers_of_zeta_poly)
                .collect(),
        ))
    }

    fn prove_accumulation<const IS_INCOMING_ABSORBED: bool>(
        pp: &Self::ProverParam,
        mut accumulator: impl BorrowMut<Self::Accumulator>,
        incoming: &Self::Accumulator,
        transcript: &mut impl TranscriptWrite<CommitmentChunk<F, Pcs>, F>,
        _: impl RngCore,
    ) -> Result<((Vec<F>, F, Vec<<Pcs as PolynomialCommitmentScheme<F>>::Commitment>)), Error> {
        let ProtostarProverParam {
            pp,
            strategy,
            num_alpha_primes,
            num_theta_primes,
            cross_term_expressions,
            gate_expressions,
            lookup_expressions,
            ..
        } = pp;
        let accumulator = accumulator.borrow_mut();

        accumulator.instance.absorb_into(transcript)?;
        if !IS_INCOMING_ABSORBED {
            incoming.instance.absorb_into(transcript)?;
        }

        let num_fixed = pp.fixed_permutation_idx_for_preprocess_poly.len();
        let num_witness_polys = pp.num_witness_polys.iter().sum::<usize>();
        let num_challenges = pp.num_challenges.iter().sum::<usize>();
        let lookups_empty = if pp.lookups.is_empty() {
                true
            } else {
                false
            };

        let (r_le_bits, r, cross_term_comms) = match strategy {
            NoCompressing => {
                let timer = start_timer(|| {
                    format!("evaluate_cross_term_polys-{}", cross_term_expressions.len())
                });
                let cross_term_polys = evaluate_cross_term_polys(
                    cross_term_expressions,
                    pp.num_vars,
                    &pp.preprocess_polys,
                    accumulator,
                    incoming,
                );
                end_timer(timer);

                let cross_term_comms =
                    Pcs::batch_commit_and_write(&pp.pcs, &cross_term_polys, transcript)?;

                // Round 0

                let r = transcript.squeeze_challenge();
                let r_le_bits = fe_to_bits_le(r.clone());
                //assert_eq!(r_le_bits.len(), NUM_CHALLENGE_BITS);
                assert_eq!(r, fe_from_bits_le(r_le_bits.clone()));

                let timer = start_timer(|| "fold_uncompressed");
                accumulator.fold_uncompressed(incoming, &cross_term_polys, &cross_term_comms, &r);
                end_timer(timer);
                (r_le_bits, r, cross_term_comms)
            }
            Compressing => {
                let timer = start_timer(|| "evaluate_zeta_cross_term_poly");
                let zeta_values = [accumulator, incoming].map(|witness| {
                    let zeta = witness
                        .instance
                        .challenges
                        .iter()
                        .nth_back(*num_alpha_primes)
                        .unwrap();
                    *zeta
                });
                let holder = PolynomialsHolder::new(pp.num_vars, zeta_values);
                let beta_refs = holder.get_polys_refs();

                let zeta_cross_term_poly = evaluate_zeta_cross_term_poly(
                    pp.num_vars,
                    *num_alpha_primes,
                    accumulator,
                    incoming,
                );
                end_timer(timer);

                let timer = start_timer(|| {
                    let len = cross_term_expressions.len();
                    format!("evaluate_compressed_cross_term_sums-{len}")
                });
                let compressed_cross_term_sums = evaluate_compressed_cross_term_sums(
                    cross_term_expressions,
                    pp.num_vars,
                    &pp.preprocess_polys,
                    accumulator,
                    incoming,
                );
                end_timer(timer);

                let zeta_cross_term_comm =
                    Pcs::commit_and_write(&pp.pcs, &zeta_cross_term_poly, transcript)?;
                transcript.write_field_elements(&compressed_cross_term_sums)?;

                // Round 0
                let r = transcript.squeeze_challenge();
                let r_le_bits = fe_to_bits_le(r.clone()).iter().copied().take(NUM_CHALLENGE_BITS).collect_vec();
                assert_eq!(r, fe_from_bits_le(r_le_bits.clone()));

                // let timer = start_timer(|| "paired_data");
                // let paired_data = Paired::<'_, F>::new_data(pp.num_vars, num_fixed, lookups_empty, num_witness_polys, num_challenges, *num_theta_primes, *num_alpha_primes, &pp.preprocess_polys, beta_refs, &incoming, &accumulator);
                // end_timer(timer);

                // let timer = start_timer(|| "full_constraint");
                // let full_constraint = paired_data.full_constraint(gate_expressions.to_vec(), lookup_expressions.to_vec());
                // end_timer(timer);

                // let rows = 1 << pp.num_vars;
                // let usable_rows = 0..rows; // 0..num_rows - (cs.blinding_factors() + 1)

                // let timer = start_timer(|| "evaluate_compressed_polynomial");
                // let error_poly = Paired::<'_, F>::evaluate_compressed_polynomial(
                //     full_constraint,
                //     usable_rows, 
                //     rows,
                // );
                // end_timer(timer);

                let timer = start_timer(|| "fold_compressed");
                accumulator.fold_compressed(
                    incoming,
                    &zeta_cross_term_poly,
                    &zeta_cross_term_comm,
                    &compressed_cross_term_sums,
                    &r,
                );
                end_timer(timer);
                (r_le_bits, r, vec![zeta_cross_term_comm])
            }
        };

        Ok((r_le_bits, r, cross_term_comms))
    }

    fn prove_nark_ec(
        pp: &Self::ProverParam,
        circuit: &impl PlonkishCircuit<F>,
        transcript: &mut impl TranscriptWrite<CommitmentChunk<F, Pcs>, F>,
        _: impl RngCore,
    ) -> Result<PlonkishNark<F, Pcs>, Error> {
        let ProtostarProverParam {
            pp,
            strategy,
            num_theta_primes,
            num_alpha_primes,
            ..
        } = pp;

        let instances = circuit.instances();
        for (num_instances, instances) in pp.num_instances.iter().zip_eq(instances) {
            assert_eq!(instances.len(), *num_instances);
            for instance in instances.iter() {
                transcript.common_field_element(instance)?;
            }
        }

        let num_witness_polys = pp.num_witness_polys.iter().sum::<usize>();
        // num_challenges = 0 since all witness_polys are in one phase.
        // Round 0..n

        let mut witness_polys = Vec::with_capacity(pp.num_witness_polys.iter().sum());
        let mut witness_comms = Vec::with_capacity(witness_polys.len());
        let mut challenges = Vec::with_capacity(pp.num_challenges.iter().sum());
        for (round, (num_witness_polys, num_challenges)) in pp
            .num_witness_polys
            .iter()
            .zip_eq(pp.num_challenges.iter())
            .enumerate()
        {
            let timer = start_timer(|| format!("witness_collector-{round}"));
            let polys = circuit
                .synthesize(round, &challenges)?
                .into_iter()
                .map(MultilinearPolynomial::new)
                .collect_vec();
            assert_eq!(polys.len(), *num_witness_polys);
            end_timer(timer);

            // witness_comms.extend(Pcs::batch_commit_and_write(&pp.pcs, &polys, transcript)?);
            witness_polys.extend(polys);
            challenges.extend(transcript.squeeze_challenges(*num_challenges));
        }

        let witness_poly_concat =  concat_polys(witness_polys.clone());
        witness_comms.push(Pcs::commit_and_write(&pp.pcs, &witness_poly_concat, transcript)?);
        println!("witness_polys_len {:?}", witness_polys.len());
        println!("witness_poly_concat_num_vars {:?}", witness_poly_concat.num_vars());

        // Round n+2
        let (zeta, powers_of_zeta_poly, powers_of_zeta_comm) = match strategy {
            NoCompressing => (None, None, None),
            Compressing => {
                let zeta = transcript.squeeze_challenge();

                let timer = start_timer(|| "powers_of_zeta_poly");
                let powers_of_zeta_poly = powers_of_zeta_poly(pp.num_vars, zeta);
                end_timer(timer);

                let powers_of_zeta_comm =
                    Pcs::commit_and_write(&pp.pcs, &powers_of_zeta_poly, transcript)?;

                (
                    Some(zeta),
                    Some(powers_of_zeta_poly),
                    Some(powers_of_zeta_comm),
                )
            }
        };

        // Round n+3
        let alpha_primes = powers(transcript.squeeze_challenge())
            .skip(1)
            .take(*num_alpha_primes)
            .collect_vec();

        let nark = PlonkishNark::new(
            instances.to_vec(),
            iter::empty()
                .chain(challenges)
                .chain(zeta)
                .chain(alpha_primes)
                .collect(),
            iter::empty()
                .chain(witness_comms)
                .chain(powers_of_zeta_comm)
                .collect(),
            iter::empty()
                .chain(witness_polys)
                .chain(powers_of_zeta_poly)
                .collect(),
        );

        Ok(nark)

    }

    fn prove_accumulation_ec<const IS_INCOMING_ABSORBED: bool>(
        pp: &Self::ProverParam,
        mut accumulator: impl BorrowMut<Self::Accumulator>,
        incoming: &Self::Accumulator,
        transcript: &mut impl TranscriptWrite<CommitmentChunk<F, Pcs>, F>,
        _: impl RngCore,
    ) -> Result<(), Error> {
        let ProtostarProverParam {
            pp,
            strategy,
            num_alpha_primes,
            num_theta_primes,
            cross_term_expressions,
            gate_expressions,
            lookup_expressions,
            queried_selectors,
            selector_map,
            ..
        } = pp;
        let accumulator = accumulator.borrow_mut();

        accumulator.instance.absorb_into(transcript)?;
        if !IS_INCOMING_ABSORBED {
            incoming.instance.absorb_into(transcript)?;
        }

        let num_fixed = pp.fixed_permutation_idx_for_preprocess_poly.len();
        let num_witness_polys = pp.num_witness_polys.iter().sum::<usize>();
        let num_challenges = pp.num_challenges.iter().sum::<usize>();
        let lookups_empty = if pp.lookups.is_empty() { true } else { false };

        match strategy {
            NoCompressing => {
                let timer = start_timer(|| {
                    format!("evaluate_cross_term_polys-{}", cross_term_expressions.len())
                });
                let cross_term_polys = evaluate_cross_term_polys(
                    cross_term_expressions,
                    pp.num_vars,
                    &pp.preprocess_polys,
                    accumulator,
                    incoming,
                );
                end_timer(timer);

                let cross_term_comms =
                    Pcs::batch_commit_and_write(&pp.pcs, &cross_term_polys, transcript)?;

                // Round 0

                let r = transcript.squeeze_challenge();

                let timer = start_timer(|| "fold_uncompressed");
                accumulator.fold_uncompressed(incoming, &cross_term_polys, &cross_term_comms, &r);
                end_timer(timer);
            }
            Compressing => {
                let timer = start_timer(|| "evaluate_zeta_cross_term_poly");
                let zeta_values = [accumulator, incoming].map(|witness| {
                    let zeta = witness
                        .instance
                        .challenges
                        .iter()
                        .nth_back(*num_alpha_primes)
                        .unwrap();
                    *zeta
                });

                let zeta_cross_term_poly = evaluate_zeta_cross_term_poly(
                    pp.num_vars,
                    *num_alpha_primes,
                    accumulator,
                    incoming,
                );
                end_timer(timer);

                let holder = PolynomialsHolder::new(pp.num_vars, zeta_values);
                let beta_refs = holder.get_polys_refs();

                // let timer = start_timer(|| {
                //     let len = cross_term_expressions.len();
                //     format!("evaluate_compressed_cross_term_sums-{len}")
                // });
                // let compressed_cross_term_sums = evaluate_compressed_cross_term_sums(
                //     cross_term_expressions,
                //     pp.num_vars,
                //     &pp.preprocess_polys,
                //     accumulator,
                //     incoming,
                // );
                // end_timer(timer);

                let zeta_cross_term_comm =
                    Pcs::commit_and_write(&pp.pcs, &zeta_cross_term_poly, transcript)?;
                // transcript.write_field_elements(&compressed_cross_term_sums)?;

                // Round 0

                let r = transcript.squeeze_challenge();

                let paired_data = Paired::<'_, F>::new_data(pp.num_vars, num_fixed, lookups_empty, num_witness_polys, num_challenges, *num_theta_primes, *num_alpha_primes, &pp.preprocess_polys, beta_refs, &incoming, &accumulator);
                let ys_paired_vec = paired_data.ys_paired_vec();
                let gate_constraint_vec = paired_data.full_constraint_vec(gate_expressions.to_vec(), lookup_expressions.to_vec());

                let mut constraint_idx = 0;
                let mut total_constraints_vec = HashMap::new();
                let mut sorted_selectors: Vec<_> = queried_selectors.iter().collect();
                sorted_selectors.sort_by_key(|&(idx, _)| idx);
                println!("sorted_selectors: {:?}", sorted_selectors.len());

                for (selector_idx, num_constraints) in sorted_selectors {
                    let selector_constraints_vec: Vec<_> = gate_constraint_vec
                        .iter()
                        .skip(constraint_idx)
                        .take(*num_constraints)
                        .cloned()
                        .collect();
                    total_constraints_vec.insert(*selector_idx, selector_constraints_vec.clone());
                    constraint_idx += *num_constraints;
                }

                let num_vars = pp.num_vars;
                let rows = 1 << num_vars;
                let last_row: usize = 529;
                let usable_rows = 0..rows;
                let sm_rows = 0..129;
                let add_rows = 129..130;

                let timer = start_timer(|| "evaluate_compressed_polynomial");
                let ys_poly_gatewise: Vec<Vec<F>> = ys_paired_vec.into_par_iter().map(|constraint| 
                    Paired::<'_, F>::evaluate_ys_polynomial(
                    constraint.clone(),
                    0..last_row, 
                    num_vars,
                )).collect();
                let mut ys_poly_gatewise_full = vec![vec![F::ONE, F::ONE]];
                ys_poly_gatewise_full.extend(ys_poly_gatewise);
                end_timer(timer);

                let timer = start_timer(|| "evaluate_compressed_polynomial_allrows");
                let error_poly_selectorwise: Vec<Vec<Vec<F>>> = total_constraints_vec.into_par_iter().map(|(selector_idx, selector_constraints)| {
                    selector_constraints.into_par_iter().map(|constraint| 
                        Paired::<'_, F>::evaluate_compressed_polynomial_allrows(
                            constraint.clone(),
                            selector_map.get(&selector_idx).unwrap().clone(), 
                            num_vars,
                        )
                    ).collect::<Vec<Vec<F>>>()
                }).collect();
                end_timer(timer);

                // let timer = start_timer(|| "evaluate_compressed_polynomial");
                // let error_poly_sm: Vec<Vec<F>> = gate_constraint_vec[..3].into_par_iter().map(|constraint| 
                //     Paired::<'_, F>::evaluate_compressed_polynomial(
                //     constraint.clone(),
                //     1..390, 
                //     num_vars,
                // )).collect();

                // let error_poly_add: Vec<Vec<F>> = gate_constraint_vec[3..5].into_par_iter().map(|constraint| 
                //     Paired::<'_, F>::evaluate_compressed_polynomial(
                //     constraint.clone(),
                //     129..130, 
                //     num_vars,
                // )).collect();

                // let error_poly_aff: Vec<Vec<F>> = gate_constraint_vec[5..7].into_par_iter().map(|constraint| 
                //     Paired::<'_, F>::evaluate_compressed_polynomial(
                //     constraint.clone(),
                //     129..130, 
                //     num_vars,
                // )).collect();

                // let error_poly_num: Vec<Vec<F>> = gate_constraint_vec[7..10].into_par_iter().map(|constraint| 
                //     Paired::<'_, F>::evaluate_compressed_polynomial(
                //     constraint.clone(),
                //     1..390, 
                //     num_vars,
                // )).collect();

                // let error_poly_poseidon: Vec<Vec<F>> = gate_constraint_vec[10..].into_par_iter().map(|constraint| 
                //     Paired::<'_, F>::evaluate_compressed_polynomial(
                //     constraint.clone(),
                //     390..last_row, 
                //     num_vars,
                // )).collect();
                // end_timer(timer);

                let timer = start_timer(|| "error_poly_poseidon_combined");
                let mut error_poly_poseidon_combined: Vec<Vec<Vec<F>>> = vec![];
                for error_poly in error_poly_selectorwise[4..].iter() {
                    let error_poly_combined = error_poly.iter()
                        .zip(ys_poly_gatewise_full.clone()) // Pair up corresponding inner vectors
                        .map(|(inner_vec1, inner_vec2)| {
                            let mut r = vec![F::ZERO; inner_vec1.len() + inner_vec2.len() - 1];
                                for (k, value) in r.iter_mut().enumerate() {
                                    for (i, &pi) in inner_vec1.iter().enumerate() {
                                        if let Some(j) = k.checked_sub(i) {
                                            if let Some(&qj) = inner_vec2.get(j) {
                                                *value += pi * qj;
                                            }
                                        }
                                    }
                                }
                            r
                        }).collect_vec();
                    error_poly_poseidon_combined.push(error_poly_combined);
                }
                end_timer(timer);

                let timer = start_timer(|| "error_poly_sm_num");
                let error_poly_sm_num = [error_poly_selectorwise[0].clone(), error_poly_selectorwise[3].clone()].concat();
                let error_poly_sm_num_vec: Vec<Vec<F>> = error_poly_sm_num.clone().into_iter()
                    .zip(ys_poly_gatewise_full.clone()) // Pair up corresponding inner vectors
                    .map(|(inner_vec1, inner_vec2)| {
                        let mut r = vec![F::ZERO; inner_vec1.len() + inner_vec2.len() - 1];
                            for (k, value) in r.iter_mut().enumerate() {
                                for (i, &pi) in inner_vec1.iter().enumerate() {
                                    if let Some(j) = k.checked_sub(i) {
                                        if let Some(&qj) = inner_vec2.get(j) {
                                            *value += pi * qj;
                                        }
                                    }
                                }
                            }
                        r
                    }).collect_vec();
                end_timer(timer);

                let timer = start_timer(|| "error_poly_add_aff");
                let error_poly_add_aff = [error_poly_selectorwise[1].clone(), error_poly_selectorwise[2].clone()].concat();
                let error_poly_add_aff_vec: Vec<Vec<F>> = error_poly_add_aff.clone().into_iter()
                    .zip(ys_poly_gatewise_full) // Pair up corresponding inner vectors
                    .map(|(inner_vec1, inner_vec2)| {
                        let mut r = vec![F::ZERO; inner_vec1.len() + inner_vec2.len() - 1];
                            for (k, value) in r.iter_mut().enumerate() {
                                for (i, &pi) in inner_vec1.iter().enumerate() {
                                    if let Some(j) = k.checked_sub(i) {
                                        if let Some(&qj) = inner_vec2.get(j) {
                                            *value += pi * qj;
                                        }
                                    }
                                }
                            }
                        r
                    }).collect_vec();
                end_timer(timer);

                let timer = start_timer(|| "error_poly_combined");
                // let error_poly_gatewise_combined = [&error_poly_sm_num_vec[..], &error_poly_add_aff_vec[..], &error_poly_poseidon_combined.iter().flatten().cloned().collect::<Vec<_>>()].concat();                
                let error_poly_gatewise_combined = [&error_poly_sm_num_vec[..], &error_poly_add_aff_vec[..], &error_poly_poseidon_combined[0], &error_poly_poseidon_combined[1], &error_poly_poseidon_combined[2]].concat();                
                let inner_len = error_poly_gatewise_combined.par_iter().map(|v| v.len()).max().unwrap_or(0);
                let error_poly_sum: Vec<F> = (0..inner_len).into_par_iter().map(|i| {
                    error_poly_gatewise_combined.par_iter()
                        .map(|inner_vec| *inner_vec.get(i).unwrap_or(&F::ZERO))
                        .reduce(|| F::ZERO, |a, b| a + b) // Use reduce with a starting value for parallel sum.
                }).collect();
                end_timer(timer);

                transcript.write_field_elements(&error_poly_sum)?;

                let timer = start_timer(|| "fold_compressed");
                accumulator.fold_compressed(
                    incoming,
                    &zeta_cross_term_poly,
                    &zeta_cross_term_comm,
                    &error_poly_sum,
                    &r,
                );
                end_timer(timer);
            }
        };

        Ok(())
    }

    fn verify_accumulation_from_nark(
        vp: &Self::VerifierParam,
        mut accumulator: impl BorrowMut<Self::AccumulatorInstance>,
        instances: &[Vec<F>],
        transcript: &mut impl TranscriptRead<CommitmentChunk<F, Self::Pcs>, F>,
        _: impl RngCore,
    ) -> Result<(), Error> {
        let ProtostarVerifierParam {
            vp,
            strategy,
            num_theta_primes,
            num_alpha_primes,
            num_cross_terms,
            ..
        } = vp;
        let accumulator = accumulator.borrow_mut();

        for (num_instances, instances) in vp.num_instances.iter().zip_eq(instances) {
            assert_eq!(instances.len(), *num_instances);
            for instance in instances.iter() {
                transcript.common_field_element(instance)?;
            }
        }

        // Round 0..n

        let mut witness_comms = Vec::with_capacity(vp.num_witness_polys.iter().sum());
        let mut challenges = Vec::with_capacity(vp.num_challenges.iter().sum());
        for (num_polys, num_challenges) in
            vp.num_witness_polys.iter().zip_eq(vp.num_challenges.iter())
        {
            witness_comms.extend(Pcs::read_commitments(&vp.pcs, *num_polys, transcript)?);
            challenges.extend(transcript.squeeze_challenges(*num_challenges));
        }

        // Round n

        let theta_primes = powers(transcript.squeeze_challenge())
            .skip(1)
            .take(*num_theta_primes)
            .collect_vec();

        let lookup_m_comms = Pcs::read_commitments(&vp.pcs, vp.num_lookups, transcript)?;

        // Round n+1

        let beta_prime = transcript.squeeze_challenge();

        let lookup_h_comms = Pcs::read_commitments(&vp.pcs, 2 * vp.num_lookups, transcript)?;

        // Round n+2

        let (zeta, powers_of_zeta_comm) = match strategy {
            NoCompressing => (None, None),
            Compressing => {
                let zeta = transcript.squeeze_challenge();

                let powers_of_zeta_comm = Pcs::read_commitment(&vp.pcs, transcript)?;

                (Some(zeta), Some(powers_of_zeta_comm))
            }
        };

        // Round n+3

        let alpha_primes = powers(transcript.squeeze_challenge())
            .skip(1)
            .take(*num_alpha_primes)
            .collect_vec();

        let nark = PlonkishNarkInstance::new(
            instances.to_vec(),
            iter::empty()
                .chain(challenges)
                .chain(theta_primes)
                .chain(Some(beta_prime))
                .chain(zeta)
                .chain(alpha_primes)
                .collect(),
            iter::empty()
                .chain(witness_comms)
                .chain(lookup_m_comms)
                .chain(lookup_h_comms)
                .chain(powers_of_zeta_comm)
                .collect(),
        );
        let incoming = ProtostarAccumulatorInstance::from_nark(*strategy, nark);
        accumulator.absorb_into(transcript)?;

        match strategy {
            NoCompressing => {
                let cross_term_comms =
                    Pcs::read_commitments(&vp.pcs, *num_cross_terms, transcript)?;

                // Round n+4

                let r = transcript.squeeze_challenge();

                accumulator.fold_uncompressed(&incoming, &cross_term_comms, &r);
            }
            Compressing => {
                let zeta_cross_term_comm = Pcs::read_commitment(&vp.pcs, transcript)?;
                let compressed_cross_term_sums =
                    transcript.read_field_elements(*num_cross_terms)?;

                // Round n+4

                let r = transcript.squeeze_challenge();

                accumulator.fold_compressed(
                    &incoming,
                    &zeta_cross_term_comm,
                    &compressed_cross_term_sums,
                    &r,
                );
            }
        };

        Ok(())
    }

    fn prove_decider(
        pp: &Self::ProverParam,
        accumulator: &Self::Accumulator,
        transcript: &mut impl TranscriptWrite<CommitmentChunk<F, Pcs>, F>,
        _: impl RngCore,
    ) -> Result<(), Error> {
        let ProtostarProverParam { pp, .. } = pp;

        accumulator.instance.absorb_into(transcript)?;

        // Round 0

        let beta = transcript.squeeze_challenge();
        let gamma = transcript.squeeze_challenge();

        let timer = start_timer(|| format!("permutation_z_polys-{}", pp.permutation_polys.len()));
        let builtin_witness_poly_offset = pp.num_witness_polys.iter().sum::<usize>();
        let instance_polys = instance_polys(pp.num_vars, &accumulator.instance.instances);
        let u = accumulator.instance.u.clone();
        let preprocess_polys = pp.preprocess_polys.iter().map(|poly| poly.clone().into_evals()).collect_vec();

        let fixed_permutation_idx_offset = &pp.fixed_permutation_idx_for_preprocess_poly; 
        let fixed_preprocess_polys = preprocess_polys.clone().iter().enumerate()
            .map(|(idx, poly)| {
                MultilinearPolynomial::new(poly.iter().map(|poly_element| {
                    if fixed_permutation_idx_offset.contains(&idx) {
                        *poly_element * u
                    } else {
                        *poly_element
                    }
                }).collect_vec())
            })
            .collect_vec();

        let polys = iter::empty()
            .chain(&instance_polys)
            .chain(&pp.preprocess_polys)
            .chain(&accumulator.witness_polys[..builtin_witness_poly_offset])
            .chain(pp.permutation_polys.iter().map(|(_, poly)| poly))
            .collect_vec();

        let polys_for_permutation = iter::empty()
            .chain(&instance_polys)
            .chain(&fixed_preprocess_polys)
            .chain(&accumulator.witness_polys[..builtin_witness_poly_offset])
            .chain(pp.permutation_polys.iter().map(|(_, poly)| poly))
            .collect_vec();

        let permutation_z_polys = permutation_z_polys(
            pp.num_permutation_z_polys,
            &pp.permutation_polys,
            &polys_for_permutation,
            &beta,
            &gamma,
        );
        end_timer(timer);

        let permutation_z_comms =
            Pcs::batch_commit_and_write(&pp.pcs, &permutation_z_polys, transcript)?;

        // Round 1

        let alpha = transcript.squeeze_challenge();
        let y = transcript.squeeze_challenges(pp.num_vars);

        let polys = iter::empty()
            .chain(polys)
            .chain(&accumulator.witness_polys[builtin_witness_poly_offset..])
            .chain(permutation_z_polys.iter())
            .chain(Some(&accumulator.e_poly))
            .collect_vec();
        let challenges = iter::empty()
            .chain(accumulator.instance.challenges.iter().copied())
            .chain([accumulator.instance.u])
            .chain([beta, gamma, alpha])
            .collect();
        let (points, evals) = {
            prove_sum_check(
                pp.num_instances.len(),
                &pp.expression,
                accumulator.instance.claimed_sum(),
                &polys,
                challenges,
                y,
                transcript,
            )?
        };

        // PCS open

        let dummy_comm = Pcs::Commitment::default();
        let comms = iter::empty()
            .chain(iter::repeat(&dummy_comm).take(pp.num_instances.len()))
            .chain(&pp.preprocess_comms)
            .chain(&accumulator.instance.witness_comms[..builtin_witness_poly_offset])
            .chain(&pp.permutation_comms)
            .chain(&accumulator.instance.witness_comms[builtin_witness_poly_offset..])
            .chain(&permutation_z_comms)
            .chain(Some(&accumulator.instance.e_comm))
            .collect_vec();
        let timer = start_timer(|| format!("pcs_batch_open-{}", evals.len()));
        Pcs::batch_open(&pp.pcs, polys, comms, &points, &evals, transcript)?;
        end_timer(timer);

        Ok(())
    }

    fn verify_decider(
        vp: &Self::VerifierParam,
        accumulator: &Self::AccumulatorInstance,
        transcript: &mut impl TranscriptRead<CommitmentChunk<F, Pcs>, F>,
        _: impl RngCore,
    ) -> Result<(), Error> {
        let ProtostarVerifierParam { vp, .. } = vp;

        accumulator.absorb_into(transcript)?;

        // Round 0

        let beta = transcript.squeeze_challenge();
        let gamma = transcript.squeeze_challenge();

        let permutation_z_comms =
            Pcs::read_commitments(&vp.pcs, vp.num_permutation_z_polys, transcript)?;

        // Round 1

        let alpha = transcript.squeeze_challenge();
        let y = transcript.squeeze_challenges(vp.num_vars);

        let challenges = iter::empty()
            .chain(accumulator.challenges.iter().copied())
            .chain([accumulator.u])
            .chain([beta, gamma, alpha])
            .collect_vec();
        let (points, evals) = {
            verify_sum_check(
                vp.num_vars,
                &vp.expression,
                accumulator.claimed_sum(),
                accumulator.instances(),
                &challenges,
                &y,
                transcript,
            )?
        };

        // PCS verify

        let builtin_witness_poly_offset = vp.num_witness_polys.iter().sum::<usize>();
        let dummy_comm = Pcs::Commitment::default();
        let comms = iter::empty()
            .chain(iter::repeat(&dummy_comm).take(vp.num_instances.len()))
            .chain(&vp.preprocess_comms)
            .chain(&accumulator.witness_comms[..builtin_witness_poly_offset])
            .chain(vp.permutation_comms.iter().map(|(_, comm)| comm))
            .chain(&accumulator.witness_comms[builtin_witness_poly_offset..])
            .chain(&permutation_z_comms)
            .chain(Some(&accumulator.e_comm))
            .collect_vec();
        Pcs::batch_verify(&vp.pcs, comms, &points, &evals, transcript)?;

        Ok(())
    }
}

impl<F, Pcs, N> From<&ProtostarVerifierParam<F, HyperPlonk<Pcs>>>
    for ProtostarAccumulationVerifierParam<N>
where
    F: PrimeField,
    N: PrimeField,
    Pcs: PolynomialCommitmentScheme<F>,
    HyperPlonk<Pcs>: PlonkishBackend<F, VerifierParam = HyperPlonkVerifierParam<F, Pcs>>,
{
    fn from(vp: &ProtostarVerifierParam<F, HyperPlonk<Pcs>>) -> Self {
        let num_witness_polys = iter::empty()
            .chain([1])
            .chain([1])
            .collect();

        let num_challenges = {
            let mut num_challenges = iter::empty()
                .chain(vp.vp.num_challenges.iter().cloned())
                .map(|num_challenge| vec![1; num_challenge])
                .collect_vec();
            num_challenges.last_mut().unwrap().push(vp.num_theta_primes + 1);
            iter::empty()
                .chain(num_challenges)
                .chain([vec![vp.num_alpha_primes]])
                .collect()
        };
        println!("num_challenges {:?}", num_challenges);
        Self {
            vp_digest: N::ZERO,
            strategy: vp.strategy,
            num_instances: vp.vp.num_instances.clone(),
            num_witness_polys,
            num_challenges,
            num_cross_terms: vp.num_cross_terms,
        }
    }
}

// #[cfg(test)]
// pub(crate) mod test {
//     use crate::{
//         accumulation::{protostar::Protostar, test::run_accumulation_scheme},
//         backend::hyperplonk::{
//             //util::{rand_vanilla_plonk_circuit, rand_vanilla_plonk_with_lookup_circuit},
//             HyperPlonk,
//         },
//         pcs::{
//             multilinear::{Gemini, MultilinearIpa, MultilinearKzg}, // Zeromorph
//             univariate::UnivariateKzg,
//         },
//         util::{
//             test::{seeded_std_rng, std_rng},
//             transcript::Keccak256Transcript,
//             Itertools,
//         },
//     };
//     use halo2_base::halo2_proofs::halo2curves::{bn256::Bn256, grumpkin};
//     use std::iter;

//     macro_rules! tests {
//         ($name:ident, $pcs:ty, $num_vars_range:expr) => {
//             paste::paste! {
//                 #[test]
//                 fn [<$name _protostar_hyperplonk_vanilla_plonk>]() {
//                     run_accumulation_scheme::<_, Protostar<HyperPlonk<$pcs>>, Keccak256Transcript<_>, _>($num_vars_range, |num_vars| {
//                         let (circuit_info, _) = rand_vanilla_plonk_circuit(num_vars, std_rng(), seeded_std_rng());
//                         let circuits = iter::repeat_with(|| {
//                             let (_, circuit) = rand_vanilla_plonk_circuit(num_vars, std_rng(), seeded_std_rng());
//                             circuit
//                         }).take(3).collect_vec();
//                         (circuit_info, circuits)
//                     });
//                 }

//                 #[test]
//                 fn [<$name _protostar_hyperplonk_vanilla_plonk_with_lookup>]() {
//                     run_accumulation_scheme::<_, Protostar<HyperPlonk<$pcs>>, Keccak256Transcript<_>, _>($num_vars_range, |num_vars| {
//                         let (circuit_info, _) = rand_vanilla_plonk_with_lookup_circuit(num_vars, std_rng(), seeded_std_rng());
//                         let circuits = iter::repeat_with(|| {
//                             let (_, circuit) = rand_vanilla_plonk_with_lookup_circuit(num_vars, std_rng(), seeded_std_rng());
//                             circuit
//                         }).take(3).collect_vec();
//                         (circuit_info, circuits)
//                     });
//                 }
//             }
//         };
//         ($name:ident, $pcs:ty) => {
//             tests!($name, $pcs, 2..16);
//         };
//     }

//     // tests!(ipa, MultilinearIpa<grumpkin::G1Affine>);
//     // tests!(kzg, MultilinearKzg<Bn256>);
//     // tests!(gemini_kzg, Gemini<UnivariateKzg<Bn256>>);
//     // tests!(zeromorph_kzg, Zeromorph<UnivariateKzg<Bn256>>);
// }
