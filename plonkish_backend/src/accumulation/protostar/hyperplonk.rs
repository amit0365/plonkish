use crate::{
    accumulation::{
        protostar::{
            hyperplonk::{
                preprocessor::{batch_size, preprocess},
                prover::{
                    evaluate_compressed_cross_term_sums, evaluate_cross_term_polys,
                    lookup_h_polys, powers_of_zeta_poly, PolynomialsHolder,
                },
            },
            ivc::{halo2::chips::main_chip::LOOKUP_BITS, ProtostarAccumulationVerifierParam},
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
    poly::{multilinear::{concat_polys, concat_polys_raw, MultilinearPolynomial}, Polynomial},
    util::{
        arithmetic::{fe_from_bits_le, fe_to_bits_le, powers, repeat_elements, repeat_vector, PrimeField}, end_timer, expression_new::paired::{eval_polynomial, evaluate_betas_polynomial, evaluate_betas_polynomial_par, evaluate_betas_selectorwise, quotient_by_boolean_vanishing, split_polys, CombinedQuadraticErrorFull, Paired}, izip_eq, start_timer, transcript::{TranscriptRead, TranscriptWrite}, DeserializeOwned, Itertools, Serialize
    },
    Error,
};
use pprof::ProfilerGuard;
use sysinfo::{ProcessExt, System, SystemExt};
use halo2_proofs::halo2curves::ff::PrimeFieldBits;
use num_bigint::BigUint;
use prover::{evaluate_zeta_sqrt_cross_term_poly, expand_beta_polys, powers_of_zeta_sqrt_poly, powers_of_zeta_sqrt_poly_ec, PolynomialsRefsHolder};
use rand::RngCore;
use core::{error, time};
use std::{borrow::{Borrow, BorrowMut}, collections::HashMap, hash::Hash, iter::{self, once}, sync::{mpsc, Arc, Mutex}, thread, time::{Duration, Instant}};
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
            pp.last_rows.clone(),
            &pp.pp.num_instances,
            pp.num_folding_witness_polys,
            pp.num_folding_challenges,
        ))
    }

    fn init_accumulator_ec(pp: &Self::ProverParam) -> Result<Self::Accumulator, Error> {
        Ok(ProtostarAccumulator::init_ec(
            pp.strategy,
            pp.pp.num_vars,
            pp.last_rows.clone(),
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

    fn init_accumulator_from_nark_ec(
        pp: &Self::ProverParam,
        nark: PlonkishNark<F, Self::Pcs>,
    ) -> Result<Self::Accumulator, Error> {
        Ok(ProtostarAccumulator::from_nark_ec(
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
            last_rows,
            advice_copies,
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
        // Round 0

        let mut witness_polys = Vec::with_capacity(pp.num_witness_polys.iter().sum());
        let mut trimmed_witness_polys = Vec::with_capacity(pp.num_witness_polys.iter().sum());
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

            trimmed_witness_polys = polys.iter().zip(last_rows).map(|(poly, &last_row)| {
                MultilinearPolynomial::new(poly.iter().take(last_row).cloned().collect_vec())
            }).collect_vec();

            witness_polys.extend(polys.clone());
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
        // let phase1_comm = Pcs::commit_and_write(&pp.pcs, &phase1_poly_concat, transcript)?;

        // let timer = start_timer(|| "trimmed_phase1_poly_bits");
        // let trimmed_witness_bits: Vec<usize> = trimmed_witness_polys.par_iter().map(|poly| {
        //     poly.iter().fold(0, |sum, coeff| {
        //         sum + BigUint::from_bytes_le(coeff.to_repr().as_ref()).bits() as usize
        //     })
        // }).collect();

        // trimmed_witness_bits.iter().enumerate().for_each(|(i, sum_bits)| {
        //     println!("witness_poly {}: sum_bits: {:?}", i, sum_bits);
        // });
        // end_timer(timer);

        // let timer = start_timer(|| "lookup_m_poly_bits");
        // let trimmed_lookup_bits: Vec<usize> = lookup_m_polys.par_iter().map(|poly| {
        //     poly.iter().fold(0, |sum, coeff| {
        //         sum + BigUint::from_bytes_le(coeff.to_repr().as_ref()).bits() as usize
        //     })
        // }).collect();

        // trimmed_lookup_bits.iter().enumerate().for_each(|(i, sum_bits)| {
        //     println!("lookup_m_poly {}: sum_bits: {:?}", i, sum_bits);
        // });
        // end_timer(timer);

        let mut trimmed_phase1_poly = trimmed_witness_polys.clone();
        trimmed_phase1_poly.push(MultilinearPolynomial::new(lookup_m_polys[0].iter().take(1<<LOOKUP_BITS).cloned().collect_vec()));
        let trimmed_phase1_poly_concat = concat_polys_raw(trimmed_phase1_poly);
        let phase1_comm = Pcs::commit_dedup_and_write(&trimmed_phase1_poly_concat, advice_copies, &pp.reduced_bases, transcript)?;

        // Round 1
        let mut theta_primes = Vec::new(); // non-zero for vector lookups
        if *num_theta_primes > 0 { 
            theta_primes = powers(transcript.squeeze_challenge())
                .skip(1)
                .take(*num_theta_primes)
                .collect_vec();
        }

        // reusing beta_prime - used for both lookup challenge and powers of zeta
        let beta_prime = transcript.squeeze_challenge();
        let zeta = transcript.squeeze_challenge();

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
        //println!("lookup_h_poly_vec_sum {:?}", lookup_h_poly_vec[0].iter().sum::<F>());
        let lookup_h_poly = MultilinearPolynomial::new(lookup_h_poly_vec[0].iter().take(*last_rows.last().unwrap()).cloned().collect_vec());
        // println!("lookup_h_poly_trimmed_sum {:?}", lookup_h_poly.iter().sum::<F>());
        // println!("lookup_h_poly_trimmed_len {:?}", lookup_h_poly.evals().len());
        //assert!(lookup_h_poly.evals().iter().sum::<F>() == lookup_h_poly_vec[0].iter().sum::<F>());
        //let lookup_g_poly = MultilinearPolynomial::new(lookup_h_poly_vec[1].iter().take(1<<LOOKUP_BITS).cloned().collect_vec());
        // println!("lookup_g_poly_len {:?}", lookup_g_poly.evals().len());
        //assert!(lookup_h_poly.evals().iter().sum::<F>() == lookup_g_poly.evals().iter().sum::<F>()); //todo fails check

        // let timer = start_timer(|| "lookup_h_poly_bits");
        // let trimmed_lookup_bits: Vec<usize> = vec![lookup_h_poly.clone(), lookup_g_poly.clone()].par_iter().map(|poly| {
        //     poly.iter().fold(0, |sum, coeff| {
        //         sum + BigUint::from_bytes_le(coeff.to_repr().as_ref()).bits() as usize
        //     })
        // }).collect();

        // trimmed_lookup_bits.iter().enumerate().for_each(|(i, sum_bits)| {
        //     println!("lookup_h_poly {}: sum_bits: {:?}", i, sum_bits);
        // });
        // end_timer(timer);

        let powers_of_zeta_poly = match strategy {
            NoCompressing => Vec::new(),
            Compressing => {
                let timer = start_timer(|| "powers_of_zeta_poly");
                let powers_of_zeta_poly = powers_of_zeta_sqrt_poly(pp.num_vars, zeta);
                end_timer(timer);

                vec![powers_of_zeta_poly]
            }
        };

        // let timer = start_timer(|| "powers_of_zeta_poly_bits");
        // let trimmed_zeta_bits: Vec<usize> = powers_of_zeta_poly.par_iter().map(|poly| {
        //     poly.iter().fold(0, |sum, coeff| {
        //         sum + BigUint::from_bytes_le(coeff.to_repr().as_ref()).bits() as usize
        //     })
        // }).collect();

        // trimmed_zeta_bits.iter().enumerate().for_each(|(i, sum_bits)| {
        //     println!("powers_of_zeta_poly {}: sum_bits: {:?}", i, sum_bits);
        // });
        // end_timer(timer);

        let phase2_poly = [lookup_h_poly_vec.clone(), powers_of_zeta_poly.clone()].concat();
        //let trimmed_phase2_poly = [vec![lookup_h_poly.clone(), lookup_g_poly.clone()], powers_of_zeta_poly.clone()].concat();
        let trimmed_phase2_poly_concat =  concat_polys_raw(phase2_poly);
        let phase2_comm = Pcs::commit_and_write(&pp.pcs, &trimmed_phase2_poly_concat, transcript)?;

        // Round 2
        let alpha_primes = powers(transcript.squeeze_challenge())
            .skip(1)
            .take(*num_alpha_primes)
            .collect_vec();

        Ok(PlonkishNark::new(
            instances.to_vec(),
            iter::empty()
                .chain(challenges)
                .chain(theta_primes)
                .chain(Some(beta_prime))
                .chain(Some(zeta))
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
            num_fixed_columns,
            cross_term_expressions,
            gate_expressions,
            lookup_expressions,
            queried_selectors,
            selector_map,
            log_num_betas,
            ..
        } = pp;
        let accumulator = accumulator.borrow_mut();

        accumulator.instance.absorb_into(transcript)?;
        if !IS_INCOMING_ABSORBED {
            incoming.instance.absorb_into(transcript)?;
        }

        let num_fixed = num_fixed_columns;
        let num_witness_polys = pp.num_witness_polys.iter().sum::<usize>();
        let num_challenges = pp.num_challenges.iter().sum::<usize>();
        let lookups_empty = pp.lookups.is_empty();

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
                let zeta_values = [incoming, accumulator].map(|witness| {
                    let zeta = witness
                        .instance
                        .challenges
                        .iter()
                        .nth_back(*num_alpha_primes)
                        .unwrap();
                    *zeta
                });
                let holder = PolynomialsHolder::new(*log_num_betas, zeta_values);
                let (beta_refs, beta_prime_refs) = holder.get_polys_refs();
                let beta_polys_owned: Box<[MultilinearPolynomial<F>]> = Box::new([
                    MultilinearPolynomial::new(
                        beta_refs[0]
                            .clone()
                            .into_evals()
                            .into_iter()
                            .flat_map(|x| std::iter::repeat(x).take(1<<(log_num_betas/2)))
                            .collect(),
                    ),
                    MultilinearPolynomial::new(
                        beta_refs[1]
                            .clone()
                            .into_evals()
                            .into_iter()
                            .flat_map(|x| std::iter::repeat(x).take(1<<(log_num_betas/2)))
                            .collect(),
                    ),
                ]);
                    
                let beta_prime_polys_owned: Box<[MultilinearPolynomial<F>]> = Box::new([
                    MultilinearPolynomial::new(
                        beta_prime_refs[0]
                            .clone()
                            .into_evals()
                            .into_iter()
                            .flat_map(|x| std::iter::repeat(x).take(1<<(log_num_betas/2)))
                            .collect(),
                    ),
                    MultilinearPolynomial::new(
                        beta_prime_refs[1]
                            .clone()
                            .into_evals()
                            .into_iter()
                            .flat_map(|x| std::iter::repeat(x).take(1<<(log_num_betas/2)))
                            .collect(),
                    ),
                ]);

                // let zeta_cross_term_poly = evaluate_zeta_cross_term_poly(
                //     (pp.num_vars/2) + 1,
                //     *num_alpha_primes,
                //     accumulator,
                //     incoming,
                // );
                end_timer(timer);

                //todo fix this
                let zeta_cross_term = vec![F::ONE; 1 << ((pp.num_vars + 2)/2 + 1)];
                let zeta_cross_term_poly = MultilinearPolynomial::new(zeta_cross_term);
                let zeta_cross_term_comm =
                    Pcs::commit_and_write(&pp.pcs, &zeta_cross_term_poly, transcript)?;

                //calculate error poly
                let paired_data = Paired::<'_, F>::new_data(pp.num_vars, *num_fixed, lookups_empty, num_witness_polys, num_challenges, *num_theta_primes, *num_alpha_primes, &pp.preprocess_polys, &beta_polys_owned, &beta_prime_polys_owned, &incoming, &accumulator);
                let gate_constraint_vec = paired_data.full_constraint_beta_vec(gate_expressions.to_vec(), lookup_expressions.to_vec(), num_witness_polys);
                let num_vars = pp.num_vars;
                let mut constraint_idx = 0;
                let mut total_constraints_vec = HashMap::new();
                let mut sorted_selectors: Vec<_> = queried_selectors.iter().collect();
                sorted_selectors.sort_by_key(|&(idx, _)| idx);
                for (selector_idx, (num_constraints, degree_vec)) in &sorted_selectors {
                    let selector_constraints_vec: Vec<_> = gate_constraint_vec
                        .iter()
                        .skip(constraint_idx)
                        .take(*num_constraints)
                        .cloned()
                        .collect();
                    total_constraints_vec.insert(*selector_idx, selector_constraints_vec.clone());
                    constraint_idx += *num_constraints;
                }

                let timer = start_timer(|| "evaluate_error_poly_selectorwise");
                let error_poly_selectorwise: Vec<Vec<Vec<F>>> = total_constraints_vec.par_iter().map(|(selector_idx, selector_constraints)| {
                    selector_constraints.par_iter().enumerate().map(|(constraint_idx, constraint)| {
                        Paired::<'_, F>::evaluate_compressed_polynomial_full_parallel(
                            constraint,
                            selector_map.get(selector_idx).unwrap_or(&vec![]), 
                            num_vars,
                        )
                    }).collect::<Vec<Vec<F>>>()
                }).collect();
                end_timer(timer);
                
                let timer = start_timer(|| "sum_error_polys");
                let error_poly_flattened: Vec<Vec<F>> = error_poly_selectorwise
                    .iter()
                    .flat_map(|middle_vec| middle_vec.iter().cloned())
                    .collect();

                // Initialize the sum evaluations with zeros
                let mut error_poly_sum = [F::ZERO; 9];
                // Sum the evaluations pointwise
                for evals in error_poly_flattened {
                    for (i, &val) in evals.iter().enumerate() {
                        error_poly_sum[i] += val;
                    }
                }
                end_timer(timer);

                //println!("error_poly_sum {:?}", error_poly_sum);
                // sanity check, check this in folding verifier
                // assert_eq!(eval_polynomial(error_poly_sum.as_slice(), F::ZERO), F::ZERO); //nark_error = 0
                // assert_eq!(eval_polynomial(error_poly_sum.as_slice(), F::ONE), accumulator.instance().compressed_e_sum.unwrap()); //acc_error = e_comm

                transcript.write_field_elements(&error_poly_sum)?;

                // Round 0
                let r = transcript.squeeze_challenge();
                let r_le_bits = fe_to_bits_le(r).iter().copied().take(NUM_CHALLENGE_BITS).collect_vec();
                assert_eq!(r, fe_from_bits_le(r_le_bits.clone()));

                let timer = start_timer(|| "fold_compressed");
                accumulator.fold_compressed(
                    incoming,
                    &zeta_cross_term_poly,
                    &zeta_cross_term_comm,
                    &error_poly_sum,
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
            last_rows,
            advice_copies,
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
        let mut trimmed_witness_polys = Vec::with_capacity(num_witness_polys);

        // Round 0
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

            trimmed_witness_polys = polys.iter().zip(last_rows).map(|(poly, &last_row)| {
                MultilinearPolynomial::new(poly.iter().take(last_row).cloned().collect_vec())
            }).collect_vec();

            witness_polys.extend(polys);
            challenges.extend(transcript.squeeze_challenges(*num_challenges));
        }

        let witness_poly_concat =  concat_polys(witness_polys.clone());
        //witness_comms.push(Pcs::commit_and_write(&pp.pcs, &witness_poly_concat, transcript)?);
        println!("witness_polys_len {:?}", witness_polys.len());
        println!("witness_poly_concat_num_vars {:?}", witness_poly_concat.num_vars());

        // let timer = start_timer(|| "trimmed_phase1_poly_bits");
        // let trimmed_witness_bits: Vec<usize> = trimmed_witness_polys.par_iter().map(|poly| {
        //     poly.iter().fold(0, |sum, coeff| {
        //         sum + BigUint::from_bytes_le(coeff.to_repr().as_ref()).bits() as usize
        //     })
        // }).collect();

        // trimmed_witness_bits.iter().enumerate().for_each(|(i, sum_bits)| {
        //     println!("witness_poly {}: sum_bits: {:?}", i, sum_bits);
        // });
        // end_timer(timer);

        let trimmed_phase1_poly_concat = concat_polys_raw(trimmed_witness_polys);
        let phase1_comm = Pcs::commit_dedup_and_write(&trimmed_phase1_poly_concat, advice_copies, &pp.reduced_bases, transcript)?;
        witness_comms.push(phase1_comm);

        // Round n+2
        let (zeta, powers_of_zeta_poly, powers_of_zeta_comm) = match strategy {
            NoCompressing => (None, None, None),
            Compressing => {
                let zeta = transcript.squeeze_challenge();
                println!("zeta {:?}", zeta);
                let timer = start_timer(|| "powers_of_zeta_poly");
                let powers_of_zeta_poly = powers_of_zeta_sqrt_poly_ec(pp.num_vars, zeta);
                println!("powers_of_zeta_poly_num_vars {:?}", powers_of_zeta_poly.num_vars());
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
            log_num_betas,
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
                let timer = start_timer(|| "evaluate_zeta_sqrt_cross_term_poly");
                let zeta_cross_term_poly = evaluate_zeta_sqrt_cross_term_poly(
                    pp.num_vars,
                    *num_alpha_primes,
                    accumulator,
                    incoming,
                );
                end_timer(timer);

                // let (zeta_cross_term_poly0, zeta_cross_term_poly1) = zeta_cross_term_poly.evals().split_at(1 << (pp.num_vars/2));
                // assert_eq!(eval_polynomial(&zeta_cross_term_poly0, F::ZERO), F::ZERO);
                // assert_eq!(eval_polynomial(&zeta_cross_term_poly1, F::ZERO), F::ZERO);

                let beta_polys = [incoming, accumulator].map(|witness| {
                    witness
                        .witness_polys
                        .iter()
                        .last()
                        .unwrap()
                        .evals()
                        .split_at(1 << (pp.num_vars/2))
                });

                let (beta_polys_owned, beta_prime_polys_owned) = expand_beta_polys(&beta_polys, 1 << (pp.num_vars/2));
                let zeta_cross_term_comm =
                    Pcs::commit_and_write(&pp.pcs, &zeta_cross_term_poly, transcript)?;

                let paired_data = Paired::<'_, F>::new_data(pp.num_vars, num_fixed, lookups_empty, num_witness_polys, num_challenges, *num_theta_primes, *num_alpha_primes, &pp.preprocess_polys, &beta_polys_owned, &beta_prime_polys_owned, &incoming, &accumulator);
                let gate_constraint_vec = paired_data.full_constraint_beta_vec(gate_expressions.to_vec(), lookup_expressions.to_vec(), num_witness_polys);
                let num_vars = pp.num_vars;
                let mut constraint_idx = 0;
                let mut total_constraints_vec = HashMap::new();
                let mut sorted_selectors: Vec<_> = queried_selectors.iter().collect();
                sorted_selectors.sort_by_key(|&(idx, _)| idx);
                
                for (selector_idx, (num_constraints, degree_vec)) in &sorted_selectors {
                    let selector_constraints_vec: Vec<_> = gate_constraint_vec
                        .iter()
                        .skip(constraint_idx)
                        .take(*num_constraints)
                        .cloned()
                        .collect();
                    total_constraints_vec.insert(*selector_idx, selector_constraints_vec.clone());
                    constraint_idx += *num_constraints;
                }

                // let timer = start_timer(|| "split_beta_polys");
                // let [(beta0, beta1), (beta_sqrt0, beta_sqrt1)] = split_polys([beta_refs[0], beta_refs[1]]);
                // let betas_poly = evaluate_betas_selectorwise(beta0, beta1, beta_sqrt0, beta_sqrt1);
                // let mut beta_poly_selectorwise: Vec<Vec<Vec<CombinedQuadraticErrorFull<F>>>> = vec![
                //     vec![
                //         Vec::new();
                //         sorted_selectors.iter().map(|(_, (num_constraints, _))| *num_constraints).max().unwrap_or(0)
                //     ];
                //     sorted_selectors.len()
                // ];
                // let mut total_rows = 0;
                // let dummy_vec = vec![];
                // for (selector_idx, (num_constraints, _)) in &sorted_selectors {
                //     let rows = selector_map.get(selector_idx).unwrap_or(&dummy_vec);
                //     for constraint_idx in 0..*num_constraints {
                //         beta_poly_selectorwise[**selector_idx][constraint_idx] = (betas_poly[total_rows..total_rows + rows.len()].to_vec());
                //         total_rows += rows.len();
                //     }
                // }
                // end_timer(timer);
                let timer = start_timer(|| "evaluate_error_poly_selectorwise");
                let error_poly_selectorwise: Vec<Vec<Vec<F>>> = total_constraints_vec.iter().map(|(selector_idx, selector_constraints)| {
                    selector_constraints.par_iter().enumerate().map(|(constraint_idx, constraint)| {
                        let rows = selector_map.get(selector_idx);
                        if rows.is_none() {
                            vec![]
                        } else {
                            Paired::<'_, F>::evaluate_compressed_polynomial_full(
                                constraint,
                                rows.unwrap(), 
                                num_vars,
                                num_witness_polys,
                                lookups_empty,
                            )
                        }
                    }).collect::<Vec<Vec<F>>>()
                }).collect();
                end_timer(timer);

                // let rows = selector_map.get(&chosen_selector);
                // let timer = start_timer(|| "evaluate_error_poly_selectorwise");
                // let error_poly_selectorwise: Vec<Vec<Vec<F>>> = vec![
                //     full_constraint_vec.par_iter().enumerate().map(|(constraint_idx, constraint)| {
                //             Paired::<'_, F>::evaluate_compressed_polynomial_full_parallel(
                //                 constraint,
                //                 rows.unwrap(), 
                //                 num_vars,
                //             )
                //     }).collect::<Vec<Vec<F>>>()];
                // end_timer(timer);

                let timer = start_timer(|| "sum_error_polys");
                let error_poly_flattened = error_poly_selectorwise.into_iter().flatten().collect_vec();
                // Initialize the sum evaluations with zeros
                let mut error_poly_sum = [F::ZERO; 9];
                // Sum the evaluations coefficient wise
                for evals in error_poly_flattened {
                    for (i, &val) in evals.iter().enumerate() {
                        error_poly_sum[i] += val;
                    }
                }
                end_timer(timer);

                // sanity check, check this in folding verifier
                assert_eq!(eval_polynomial(error_poly_sum.as_slice(), F::ZERO), F::ZERO); //nark_error = 0
                assert_eq!(eval_polynomial(error_poly_sum.as_slice(), F::ONE), accumulator.instance().compressed_e_sum.unwrap()); //acc_error = e_comm
                transcript.write_field_elements(&error_poly_sum)?;
                                
                // Round 0
                let r = transcript.squeeze_challenge();
                println!("r {:?}", r);

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

    fn decide_strawman(
        pp: &Self::ProverParam,
        accumulator: &Self::Accumulator,
        transcript: &mut impl TranscriptWrite<CommitmentChunk<F, Pcs>, F>,
        _: impl RngCore,
    ) -> Result<(), Error> {
        let ProtostarProverParam { pp: pp_hp, .. } = pp;

        accumulator.instance.absorb_into(transcript)?;
        let builtin_witness_poly_offset = pp_hp.num_witness_polys.iter().sum::<usize>();
        let zeta_nth_back = pp.num_alpha_primes;
        let num_vars = pp_hp.num_vars;

        let (acc_pow, acc_pow_sqrt, acc_zeta, acc_zeta_sqrt, acc_u) =
        {
            let pow = accumulator.witness_polys.last().unwrap();
            let (pow_poly, pow_sqrt_poly) = pow.evals().split_at(1 << num_vars/2);
            let zeta = accumulator
                .instance
                .challenges
                .iter()
                .nth_back(zeta_nth_back)
                .unwrap();
            let lsqrt = 1 << num_vars/2;
            let zeta_sqrt = zeta.pow([lsqrt as u64]);
            (pow_poly, pow_sqrt_poly, zeta, zeta_sqrt, accumulator.instance.u)
        };

        // Check linear lookup constraint ∑ᵢ gᵢ == ∑ᵢ hᵢ
        let lookups_ok = {
                let lhs: F = accumulator.witness_polys.iter().nth_back(1).unwrap().iter().sum();
                let rhs: F = accumulator.witness_polys.iter().nth_back(2).unwrap().iter().sum();
                lhs == rhs
        };

        // Check beta constraint eᵢ ≡ β ⋅ βᵢ − βᵢ₊₁, β₀ ≡ 1
        // let beta_ok = {
        //     let beta_column = acc_pow;
        //     let beta_column_sqrt = acc_pow_sqrt;
        //     let error_column_concat = &accumulator.e_poly;
        //     let (error_column, error_column_sqrt) = error_column_concat.evals().split_at(1 << num_vars/2);
        //     let beta = acc_zeta;
        //     let beta_sqrt = acc_zeta_sqrt;
        
        //     let init_ok = acc_pow[0] == acc_u;
        //     let powers_ok = (2..(1 << num_vars/2) - 1)
        //         .into_iter()
        //         .all(|i| error_column[i - 1] == acc_pow[i - 1] * beta - acc_pow[i]*acc_u);
        //     println!("acc_pow[0] {:?}", acc_pow[0]);
        //     println!("acc_pow[1] {:?}", acc_pow[1]);
        //     println!("acc_pow[2] {:?}", acc_pow[2]);
        //     println!("first constraint {:?}", acc_pow[0] * beta - acc_pow[1]*acc_u);
        //     println!("error_column[0] {:?}", error_column[0]);
        //     println!("second constraint {:?}", acc_pow[1] * beta - acc_pow[2]*acc_u);
        //     println!("error_column[1] {:?}", error_column[1]);
        //     println!("beta {:?}", beta);
        //     println!("acc_u {:?}", acc_u);
        //     assert!(init_ok, "init_not_ok");
        //     assert!(powers_ok, "powers_not_ok");

        //     let init_sqrt_ok = acc_pow_sqrt[0] == F::ONE;
        //     let powers_sqrt_ok = (1..(1 << num_vars/2))
        //         .into_iter()
        //         .all(|i| error_column_sqrt[i - 1] == acc_pow_sqrt[i - 1] * beta_sqrt - acc_pow_sqrt[i]);
        //     assert!(init_sqrt_ok, "init_sqrt_not_ok");
        //     assert!(powers_sqrt_ok, "powers_sqrt_not_ok");

        //     powers_ok && init_ok && powers_sqrt_ok && init_sqrt_ok
        // };
        // assert!(beta_ok);

        // Round 0

        // let beta = transcript.squeeze_challenge();
        // let gamma = transcript.squeeze_challenge();

        // let timer = start_timer(|| format!("permutation_z_polys-{}", pp.permutation_polys.len()));
        // let builtin_witness_poly_offset = pp.num_witness_polys.iter().sum::<usize>();
        // let instance_polys = instance_polys(pp.num_vars, &accumulator.instance.instances);
        // let u = accumulator.instance.u.clone();
        // let preprocess_polys = pp.preprocess_polys.iter().map(|poly| poly.clone().into_evals()).collect_vec();

        // let fixed_permutation_idx_offset = &pp.fixed_permutation_idx_for_preprocess_poly; 
        // let fixed_preprocess_polys = preprocess_polys.clone().iter().enumerate()
        //     .map(|(idx, poly)| {
        //         MultilinearPolynomial::new(poly.iter().map(|poly_element| {
        //             if fixed_permutation_idx_offset.contains(&idx) {
        //                 *poly_element * u
        //             } else {
        //                 *poly_element
        //             }
        //         }).collect_vec())
        //     })
        //     .collect_vec();

        // let polys = iter::empty()
        //     .chain(&instance_polys)
        //     .chain(&pp.preprocess_polys)
        //     .chain(&accumulator.witness_polys[..builtin_witness_poly_offset])
        //     .chain(pp.permutation_polys.iter().map(|(_, poly)| poly))
        //     .collect_vec();

        // let polys_for_permutation = iter::empty()
        //     .chain(&instance_polys)
        //     .chain(&fixed_preprocess_polys)
        //     .chain(&accumulator.witness_polys[..builtin_witness_poly_offset])
        //     .chain(pp.permutation_polys.iter().map(|(_, poly)| poly))
        //     .collect_vec();

        // let permutation_z_polys = permutation_z_polys(
        //     pp.num_permutation_z_polys,
        //     &pp.permutation_polys,
        //     &polys_for_permutation,
        //     &beta,
        //     &gamma,
        // );
        // end_timer(timer);

        // let permutation_z_comms =
        //     Pcs::batch_commit_and_write(&pp.pcs, &permutation_z_polys, transcript)?;

        // Round 1

        // let alpha = transcript.squeeze_challenge();
        // let y = transcript.squeeze_challenges(pp.num_vars);

        // let polys = iter::empty()
        //     .chain(polys)
        //     .chain(&accumulator.witness_polys[builtin_witness_poly_offset..])
        //     //.chain(permutation_z_polys.iter())
        //     .chain(Some(&accumulator.e_poly))
        //     .collect_vec();
        // let challenges = iter::empty()
        //     .chain(accumulator.instance.challenges.iter().copied())
        //     .chain([accumulator.instance.u])
        //     //.chain([beta, gamma, alpha])
        //     .collect();
        // let (points, evals) = {
        //     prove_sum_check(
        //         pp.num_instances.len(),
        //         &pp.expression,
        //         accumulator.instance.claimed_sum(),
        //         &polys,
        //         challenges,
        //         y,
        //         transcript,
        //     )?
        // };

        //let witness_polys_comms = Pcs::batch_commit_and_write(&pp.pcs, &accumulator.witness_polys[builtin_witness_poly_offset..], transcript)?;
        // izip_eq!(
        //     accumulator.instance.witness_comms[..builtin_witness_poly_offset].iter(),
        //     accumulator.witness_polys[builtin_witness_poly_offset..].iter()
        // ).for_each(|(comm, poly)| {
        //     assert_eq!(comm, &Pcs::commit(&pp.pcs, poly).unwrap());
        // });

        //assert_eq!(accumulator.instance.e_comm, Pcs::commit(&pp_hp.pcs, &accumulator.e_poly).unwrap());

        // PCS open

        // let dummy_comm = Pcs::Commitment::default();
        // let comms = iter::empty()
        //     .chain(iter::repeat(&dummy_comm).take(pp.num_instances.len()))
        //     .chain(&pp.preprocess_comms)
        //     .chain(&accumulator.instance.witness_comms[..builtin_witness_poly_offset])
        //     .chain(&pp.permutation_comms)
        //     .chain(&accumulator.instance.witness_comms[builtin_witness_poly_offset..])
        //     .chain(&permutation_z_comms)
        //     .chain(Some(&accumulator.instance.e_comm))
        //     .collect_vec();
        // let timer = start_timer(|| format!("pcs_batch_open-{}", evals.len()));
        // Pcs::batch_open(&pp.pcs, polys, comms, &points, &evals, transcript)?;
        // end_timer(timer);

        Ok(())
    }

    fn decide_strawman_ec(
        pp: &Self::ProverParam,
        accumulator: &Self::Accumulator,
        transcript: &mut impl TranscriptWrite<CommitmentChunk<F, Pcs>, F>,
        _: impl RngCore,
    ) -> Result<(), Error> {
        let ProtostarProverParam { pp: pp_hp, .. } = pp;

        accumulator.instance.absorb_into(transcript)?;
        let builtin_witness_poly_offset = pp_hp.num_witness_polys.iter().sum::<usize>();
        let zeta_nth_back = pp.num_alpha_primes;
        let num_vars = pp_hp.num_vars;

        let (acc_pow, acc_pow_sqrt, acc_zeta, acc_zeta_sqrt, acc_u) =
        {
            let pow = accumulator.witness_polys.last().unwrap();
            let (pow_poly, pow_sqrt_poly) = pow.evals().split_at(1 << num_vars/2);
            let zeta = accumulator
                .instance
                .challenges
                .iter()
                .nth_back(zeta_nth_back)
                .unwrap();
            let lsqrt = 1 << num_vars/2;
            let zeta_sqrt = zeta.pow([lsqrt as u64]);
            (pow_poly, pow_sqrt_poly, zeta, zeta_sqrt, accumulator.instance.u)
        };

        // Check beta constraint eᵢ ≡ β ⋅ βᵢ − βᵢ₊₁, β₀ ≡ 1
        // let beta_ok = {
        //     let beta_column = acc_pow;
        //     let beta_column_sqrt = acc_pow_sqrt;
        //     let error_column_concat = &accumulator.e_poly;
        //     let (error_column, error_column_sqrt) = error_column_concat.evals().split_at(1 << num_vars/2);
        //     let beta = acc_zeta;
        //     let beta_sqrt = acc_zeta_sqrt;
        
        //     let init_ok = acc_pow[0] == acc_u;
        //     let powers_ok = (2..(1 << num_vars/2) - 1)
        //         .into_iter()
        //         .all(|i| error_column[i - 1] == acc_pow[i - 1] * beta - acc_pow[i]*acc_u);
        //     println!("acc_pow[0] {:?}", acc_pow[0]);
        //     println!("acc_pow[1] {:?}", acc_pow[1]);
        //     println!("acc_pow[2] {:?}", acc_pow[2]);
        //     println!("first constraint {:?}", acc_pow[0] * beta - acc_pow[1]*acc_u);
        //     println!("error_column[0] {:?}", error_column[0]);
        //     println!("second constraint {:?}", acc_pow[1] * beta - acc_pow[2]*acc_u);
        //     println!("error_column[1] {:?}", error_column[1]);
        //     println!("beta {:?}", beta);
        //     println!("acc_u {:?}", acc_u);
        //     assert!(init_ok, "init_not_ok");
        //     assert!(powers_ok, "powers_not_ok");

        //     let init_sqrt_ok = acc_pow_sqrt[0] == F::ONE;
        //     let powers_sqrt_ok = (1..(1 << num_vars/2))
        //         .into_iter()
        //         .all(|i| error_column_sqrt[i - 1] == acc_pow_sqrt[i - 1] * beta_sqrt - acc_pow_sqrt[i]);
        //     assert!(init_sqrt_ok, "init_sqrt_not_ok");
        //     assert!(powers_sqrt_ok, "powers_sqrt_not_ok");

        //     powers_ok && init_ok && powers_sqrt_ok && init_sqrt_ok
        // };
        // assert!(beta_ok);

        // Round 0

        // let beta = transcript.squeeze_challenge();
        // let gamma = transcript.squeeze_challenge();

        // let timer = start_timer(|| format!("permutation_z_polys-{}", pp.permutation_polys.len()));
        // let builtin_witness_poly_offset = pp.num_witness_polys.iter().sum::<usize>();
        // let instance_polys = instance_polys(pp.num_vars, &accumulator.instance.instances);
        // let u = accumulator.instance.u.clone();
        // let preprocess_polys = pp.preprocess_polys.iter().map(|poly| poly.clone().into_evals()).collect_vec();

        // let fixed_permutation_idx_offset = &pp.fixed_permutation_idx_for_preprocess_poly; 
        // let fixed_preprocess_polys = preprocess_polys.clone().iter().enumerate()
        //     .map(|(idx, poly)| {
        //         MultilinearPolynomial::new(poly.iter().map(|poly_element| {
        //             if fixed_permutation_idx_offset.contains(&idx) {
        //                 *poly_element * u
        //             } else {
        //                 *poly_element
        //             }
        //         }).collect_vec())
        //     })
        //     .collect_vec();

        // let polys = iter::empty()
        //     .chain(&instance_polys)
        //     .chain(&pp.preprocess_polys)
        //     .chain(&accumulator.witness_polys[..builtin_witness_poly_offset])
        //     .chain(pp.permutation_polys.iter().map(|(_, poly)| poly))
        //     .collect_vec();

        // let polys_for_permutation = iter::empty()
        //     .chain(&instance_polys)
        //     .chain(&fixed_preprocess_polys)
        //     .chain(&accumulator.witness_polys[..builtin_witness_poly_offset])
        //     .chain(pp.permutation_polys.iter().map(|(_, poly)| poly))
        //     .collect_vec();

        // let permutation_z_polys = permutation_z_polys(
        //     pp.num_permutation_z_polys,
        //     &pp.permutation_polys,
        //     &polys_for_permutation,
        //     &beta,
        //     &gamma,
        // );
        // end_timer(timer);

        // let permutation_z_comms =
        //     Pcs::batch_commit_and_write(&pp.pcs, &permutation_z_polys, transcript)?;

        // Round 1

        // let alpha = transcript.squeeze_challenge();
        // let y = transcript.squeeze_challenges(pp.num_vars);

        // let polys = iter::empty()
        //     .chain(polys)
        //     .chain(&accumulator.witness_polys[builtin_witness_poly_offset..])
        //     //.chain(permutation_z_polys.iter())
        //     .chain(Some(&accumulator.e_poly))
        //     .collect_vec();
        // let challenges = iter::empty()
        //     .chain(accumulator.instance.challenges.iter().copied())
        //     .chain([accumulator.instance.u])
        //     //.chain([beta, gamma, alpha])
        //     .collect();
        // let (points, evals) = {
        //     prove_sum_check(
        //         pp.num_instances.len(),
        //         &pp.expression,
        //         accumulator.instance.claimed_sum(),
        //         &polys,
        //         challenges,
        //         y,
        //         transcript,
        //     )?
        // };

        //let witness_polys_comms = Pcs::batch_commit_and_write(&pp.pcs, &accumulator.witness_polys[builtin_witness_poly_offset..], transcript)?;
        // izip_eq!(
        //     accumulator.instance.witness_comms[..builtin_witness_poly_offset].iter(),
        //     accumulator.witness_polys[builtin_witness_poly_offset..].iter()
        // ).for_each(|(comm, poly)| {
        //     assert_eq!(comm, &Pcs::commit(&pp.pcs, poly).unwrap());
        // });

        //assert_eq!(accumulator.instance.e_comm, Pcs::commit(&pp_hp.pcs, &accumulator.e_poly).unwrap());

        // PCS open

        // let dummy_comm = Pcs::Commitment::default();
        // let comms = iter::empty()
        //     .chain(iter::repeat(&dummy_comm).take(pp.num_instances.len()))
        //     .chain(&pp.preprocess_comms)
        //     .chain(&accumulator.instance.witness_comms[..builtin_witness_poly_offset])
        //     .chain(&pp.permutation_comms)
        //     .chain(&accumulator.instance.witness_comms[builtin_witness_poly_offset..])
        //     .chain(&permutation_z_comms)
        //     .chain(Some(&accumulator.instance.e_comm))
        //     .collect_vec();
        // let timer = start_timer(|| format!("pcs_batch_open-{}", evals.len()));
        // Pcs::batch_open(&pp.pcs, polys, comms, &points, &evals, transcript)?;
        // end_timer(timer);

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
            if vp.lookups {
                num_challenges.last_mut().unwrap().push(vp.num_theta_primes + 2);
            } else {
                num_challenges.last_mut().unwrap().push(vp.num_theta_primes + 1);
            }
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
//     use halo2_proofs::halo2curves::{bn256::Bn256, grumpkin};
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
