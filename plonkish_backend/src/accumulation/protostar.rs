use halo2_proofs::plonk;
use ivc::halo2::chips::main_chip::{MAIN_LOOKUP_BITS, SHA256_LOOKUP_BITS};

use crate::{
    accumulation::{
        protostar::ProtostarStrategy::{Compressing, NoCompressing},
        PlonkishNark, PlonkishNarkInstance,
    },
    backend::{hyperplonk::{prover::instance_polys, HyperPlonk}, PlonkishBackend, WitnessEncoding},
    pcs::{AdditiveCommitment, PolynomialCommitmentScheme},
    poly::{multilinear::MultilinearPolynomial, univariate::UnivariatePolynomial, Polynomial},
    util::{
        arithmetic::{inner_product, powers, CurveAffine, Field}, chain, expression::Expression, izip, izip_eq, parallel::parallelize_iter, transcript::Transcript, Deserialize, Itertools, Serialize
    },
    Error,
};
use std::{collections::HashMap, iter, marker::PhantomData, ops::Sub, slice::from_ref};
use rayon::prelude::*;
use rayon::iter::ParallelBridge;
pub mod hyperplonk;
pub mod ivc;

#[derive(Clone, Debug)]
pub struct Protostar<Pb, const STRATEGY: usize = { Compressing as usize }>(PhantomData<Pb>);

#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize)]
pub enum ProtostarStrategy {
    // As known as Sangria
    NoCompressing = 0,
    // Compressing verification as described in 2023/620 section 3.5 but without square-root optimization
    #[default]
    Compressing = 1,
    // TODO:
    // Compressing verification with square-root optimization applied as described in 2023/620 section 3.5
    // CompressingWithSqrtPowers = 2,
}

impl From<usize> for ProtostarStrategy {
    fn from(strategy: usize) -> Self {
        [NoCompressing, Compressing][strategy]
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProtostarProverParam<F, Pb>
where
    F: Field,
    Pb: PlonkishBackend<F>,
{
    pp: Box<Pb::ProverParam>,
    strategy: ProtostarStrategy,
    num_theta_primes: usize,
    num_alpha_primes: usize,
    num_fixed_columns: usize,
    num_folding_witness_polys: usize,
    num_folding_challenges: usize,
    cross_term_expressions: Vec<Expression<F>>,
    gate_expressions: Vec<plonk::Expression<F>>,
    lookup_expressions: Vec<Vec<(plonk::Expression<F>, plonk::Expression<F>)>>,
    queried_selectors: HashMap<usize, (usize, Vec<usize>)>,
    selector_map: HashMap<usize, Vec<usize>>,
    last_rows: Vec<usize>,
    advice_copies: Vec<Vec<usize>>,
    log_num_betas: usize,
    pub witness_count: usize,
    pub copy_count: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProtostarVerifierParam<F, Pb>
where
    F: Field,
    Pb: PlonkishBackend<F>,
{
    vp: Pb::VerifierParam,
    strategy: ProtostarStrategy,
    num_theta_primes: usize,
    num_alpha_primes: usize,
    num_fixed_columns: usize,
    num_folding_witness_polys: usize,
    num_folding_challenges: usize,
    num_cross_terms: usize,
    lookups: bool,
}

#[derive(Clone, Debug)]
pub struct ProtostarAccumulator<F, Pcs>
where
    F: Field,
    Pcs: PolynomialCommitmentScheme<F>,
{
    pub instance: ProtostarAccumulatorInstance<F, Pcs::Commitment>,
    pub witness_polys: Vec<Pcs::Polynomial>,
    pub e_poly: Pcs::Polynomial,
    pub instance_polys: Vec<Pcs::Polynomial>,
    //pub beta_poly: Pcs::Polynomial,
    _marker: PhantomData<Pcs>,
}

impl<F, Pcs> AsRef<ProtostarAccumulatorInstance<F, Pcs::Commitment>>
    for ProtostarAccumulator<F, Pcs>
where
    F: Field,
    Pcs: PolynomialCommitmentScheme<F>,
{
    fn as_ref(&self) -> &ProtostarAccumulatorInstance<F, Pcs::Commitment> {
        &self.instance
    }
}

impl<F, Pcs> ProtostarAccumulator<F, Pcs>
where
    F: Field,
    Pcs: PolynomialCommitmentScheme<F>,
{
    fn init(
        strategy: ProtostarStrategy,
        k: usize,
        last_rows: Vec<usize>,
        num_instances: &[usize],
        num_witness_polys: usize,
        num_challenges: usize,
        log_num_betas: usize,
    ) -> Self {
        let zero_poly = Pcs::Polynomial::from_evals(vec![F::ZERO; 1 << k]);
        let zero_poly_sqrt = Pcs::Polynomial::from_evals(vec![F::ZERO; 1 << (log_num_betas/2 + 1)]);
        let zero_poly_main_lookup_h = Pcs::Polynomial::from_evals(vec![F::ZERO; 1 << last_rows.last().unwrap()]);
        let zero_poly_sha256_lookup_h = Pcs::Polynomial::from_evals(vec![F::ZERO; 1 << last_rows[last_rows.len() - 2]]);
        let zero_poly_main_lookup_table = Pcs::Polynomial::from_evals(vec![F::ZERO; 1 << MAIN_LOOKUP_BITS]);
        let zero_poly_sha256_lookup_table = Pcs::Polynomial::from_evals(vec![F::ZERO; 1 << SHA256_LOOKUP_BITS]);
        Self {
            instance: ProtostarAccumulatorInstance::init(
                strategy,
                num_instances,
                num_witness_polys - 1, // todo not used
                num_challenges,
            ),
            witness_polys: iter::repeat_with(|| zero_poly.clone()) // all witness polys
                .take(num_witness_polys - 3)
                //.chain(iter::once(zero_poly_lookup_table.clone())) // lookup_m, somethings fails here so check lookup_m
                // .chain(iter::once(zero_poly.clone())) // lookup_h_sha256
                // .chain(iter::once(zero_poly.clone())) // lookup_h_main
                .chain(iter::once(zero_poly_sha256_lookup_table.clone()))// lookup_g_sha256
                .chain(iter::once(zero_poly_main_lookup_table.clone()))// lookup_g_main
                .chain(iter::once(zero_poly_sqrt.clone()))
                .collect_vec(),
            // witness_polys: iter::repeat_with(|| zero_poly.clone())
            //     .take(num_witness_polys - 1)
            //     .chain(iter::once(zero_poly_sqrt.clone()))
            //     .collect(),
            e_poly: zero_poly_sqrt.clone(),
            instance_polys: iter::repeat_with(|| zero_poly.clone())
                .take(num_instances.iter().sum())
                .collect(),
            _marker: PhantomData,
        }
    }

    fn init_ec(
        strategy: ProtostarStrategy,
        k: usize,
        last_rows: Vec<usize>,
        num_instances: &[usize],
        num_witness_polys: usize,
        num_challenges: usize,
        log_num_betas: usize,
    ) -> Self {
        let zero_poly = Pcs::Polynomial::from_evals(vec![F::ZERO; 1 << k]);
        let zero_poly_sqrt = Pcs::Polynomial::from_evals(vec![F::ZERO; 1 << (log_num_betas/2 + 1)]);

        Self {
            instance: ProtostarAccumulatorInstance::init_ec(
                strategy,
                num_instances,
                num_witness_polys,
                num_challenges,
            ),
            witness_polys: iter::repeat_with(|| zero_poly.clone())
                .take(num_witness_polys - 1)
                .chain(iter::once(zero_poly_sqrt.clone()))
                .collect(),
            e_poly: zero_poly_sqrt.clone(),
            instance_polys: iter::repeat_with(|| zero_poly.clone())
                .take(num_instances.iter().sum())
                .collect(),
            _marker: PhantomData,
        }
    }

    fn from_nark(strategy: ProtostarStrategy, k: usize, log_num_betas: usize, nark: PlonkishNark<F, Pcs>) -> Self {
        let witness_polys = nark.witness_polys;
        let instance_polys = Self::instance_polynomial(k, nark.instance.clone().instances);
        Self {
            instance: ProtostarAccumulatorInstance::from_nark(strategy, nark.instance),
            witness_polys,
            e_poly: Pcs::Polynomial::from_evals(vec![F::ZERO; 1 << (log_num_betas/2 + 1)]),
            instance_polys,
            _marker: PhantomData,
        }
    }

    fn from_nark_ec(strategy: ProtostarStrategy, k: usize, log_num_betas: usize, nark: PlonkishNark<F, Pcs>) -> Self {
        let witness_polys = nark.witness_polys;
        let instance_polys = Self::instance_polynomial(k, nark.instance.clone().instances);
        Self {
            instance: ProtostarAccumulatorInstance::from_nark(strategy, nark.instance),
            witness_polys,
            e_poly: Pcs::Polynomial::from_evals(vec![F::ZERO; 1 << (log_num_betas/2 + 1)]),
            instance_polys,
            _marker: PhantomData,
        }
    }

    fn instance_polynomial<'a>(
        num_vars: usize,
        instances: Vec<Vec<F>>,
    ) -> Vec<Pcs::Polynomial> {
        let row_mapping = HyperPlonk::<()>::row_mapping(num_vars);
        instances
            .into_iter()
            .map(|instances| {
                let mut poly = vec![F::ZERO; 1 << num_vars];
                for (b, instance) in row_mapping.iter().zip(instances.into_iter()) {
                    poly[*b] = instance;
                }
                poly
            })
            .map(Pcs::Polynomial::from_evals)
            .collect()
    }

    // why make a tuple of witness poly? *lhs += (r, rhs) ?
    // here cross_term_poly are ej*X^j, where X^j are powers of r ?
    // self.e_poly += (&power_of_r, poly) = ej*X^j, why this is a tuple not a product? maybe no need for product 
    fn fold_uncompressed(
        &mut self,
        rhs: &Self,
        cross_term_polys: &[Pcs::Polynomial],
        cross_term_comms: &[Pcs::Commitment],
        r: &F,
    ) where
        Pcs::Commitment: AdditiveCommitment<F>,
    {
        self.instance
            .fold_uncompressed(&rhs.instance, cross_term_comms, r);
        izip_eq!(&mut self.witness_polys, &rhs.witness_polys)
            .for_each(|(lhs, rhs)| *lhs += (r, rhs));
        izip!(powers(*r).skip(1), chain![cross_term_polys, [&rhs.e_poly]])
            .for_each(|(power_of_r, poly)| self.e_poly += (&power_of_r, poly));
    }

    fn fold_compressed(
        &mut self,
        rhs: &Self,
        zeta_cross_term_poly: &Pcs::Polynomial,
        zeta_cross_term_comm: &Pcs::Commitment,
        compressed_cross_term_sums: &[F],
        r: &F,
    ) where
        Pcs::Commitment: AdditiveCommitment<F>,
    {
        self.instance.fold_compressed(
            &rhs.instance,
            zeta_cross_term_comm,
            compressed_cross_term_sums,
            r,
        );

        izip_eq!(&mut self.witness_polys, &rhs.witness_polys)
        .for_each(|(lhs, rhs)| *lhs += (r, rhs));
        izip!(powers(*r).skip(1), [zeta_cross_term_poly, &rhs.e_poly])
            .for_each(|(power_of_r, poly)| self.e_poly += (&power_of_r, poly));
    }

    pub fn instance(&self) -> &ProtostarAccumulatorInstance<F, Pcs::Commitment> {
        &self.instance
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProtostarAccumulatorInstance<F, C> {
    pub instances: Vec<Vec<F>>,
    pub witness_comms: Vec<C>,
    pub challenges: Vec<F>,
    pub u: F,
    pub e_comm: C,
    pub compressed_e_sum: Option<F>,
}

impl<F, C> ProtostarAccumulatorInstance<F, C> {
    fn instances(&self) -> &[Vec<F>] {
        &self.instances
    }
}

impl<F, C> ProtostarAccumulatorInstance<F, C>
where
    F: Field,
    C: Default,
{
    fn init(
        strategy: ProtostarStrategy,
        num_instances: &[usize],
        num_witness_polys: usize,
        num_challenges: usize,
    ) -> Self {
        Self {
            instances: num_instances.iter().map(|n| vec![F::ZERO; *n]).collect(),
            // witness_comms: iter::repeat_with(C::default)
            //     .take(num_witness_polys)
            //     .collect(),
            witness_comms: vec![C::default(), C::default()],
            challenges: vec![F::ZERO; num_challenges],
            u: F::ZERO,
            e_comm: C::default(),
            compressed_e_sum: match strategy {
                NoCompressing => None,
                Compressing => Some(F::ZERO),
                // CompressingWithSqrtPowers => Some(F::ZERO),
            },
        }
    }

    fn init_ec(
        strategy: ProtostarStrategy,
        num_instances: &[usize],
        num_witness_polys: usize,
        num_challenges: usize,
    ) -> Self {
        Self {
            instances: num_instances.iter().map(|n| vec![F::ZERO; *n]).collect(),
            witness_comms: vec![C::default(), C::default()],
            challenges: vec![F::ZERO; num_challenges],
            u: F::ZERO,
            e_comm: C::default(),
            compressed_e_sum: match strategy {
                NoCompressing => None,
                Compressing => Some(F::ZERO),
                // CompressingWithSqrtPowers => Some(F::ZERO),
            },
        }
    }

    fn claimed_sum(&self) -> F {
        self.compressed_e_sum.unwrap_or(F::ZERO)
    }

    fn absorb_into<CommitmentChunk>(
        &self,
        transcript: &mut impl Transcript<CommitmentChunk, F>,
    ) -> Result<(), Error>
    where
        C: AsRef<[CommitmentChunk]>,
    {
        self.instances
            .iter()
            .try_for_each(|instances| transcript.common_field_elements(instances))?;
        self.witness_comms
            .iter()
            .try_for_each(|comm| transcript.common_commitments(comm.as_ref()))?;
        transcript.common_field_elements(&self.challenges)?;
        transcript.common_field_element(&self.u)?;
        transcript.common_commitments(self.e_comm.as_ref())?;
        if let Some(compressed_e_sum) = self.compressed_e_sum.as_ref() {
            transcript.common_field_element(compressed_e_sum)?;
        }
        Ok(())
    }

    fn from_nark(strategy: ProtostarStrategy, nark: PlonkishNarkInstance<F, C>) -> Self {
        Self {
            instances: nark.instances,
            witness_comms: nark.witness_comms,
            challenges: nark.challenges,
            u: F::ONE,
            e_comm: C::default(),
            compressed_e_sum: match strategy {
                NoCompressing => None,
                Compressing => Some(F::ZERO),
                // CompressingWithSqrtPowers => Some(F::ZERO),
            },
        }
    }

    // cross_term_comms - Ej = comm(ej), j = [1, d-1] 
    // d+1 powers of r required so, take(cross_term_comms.len() + 2)
    // seems instances are mi which are nark witness, and witness_commit are Ci which are nark instances
    fn fold_uncompressed(&mut self, rhs: &Self, cross_term_comms: &[C], r: &F)
    where
        C: AdditiveCommitment<F>,
    {
        let one = F::ONE;
        let powers_of_r = powers(*r).take(cross_term_comms.len() + 2).collect_vec();
        izip_eq!(&mut self.instances, &rhs.instances)
            .for_each(|(lhs, rhs)| izip_eq!(lhs, rhs).for_each(|(lhs, rhs)| *lhs += &(*rhs * r)));
        izip_eq!(&mut self.witness_comms, &rhs.witness_comms)
            .for_each(|(lhs, rhs)| *lhs = C::sum_with_scalar([&one, r], [lhs, rhs]));
        izip_eq!(&mut self.challenges, &rhs.challenges).for_each(|(lhs, rhs)| *lhs += &(*rhs * r));
        self.u += &(rhs.u * r);
        self.e_comm = {
            let comms = chain![[&self.e_comm], cross_term_comms, [&rhs.e_comm]];
            C::sum_with_scalar(&powers_of_r, comms)
        };
    }

    // compressed e_sum -> E = E + alpha*ej , ej are field elements so just inner product, use all powers of r except first since [1,d-1]
    // zeta_cross_term_comm -> E'_j = comm(e'_j), j = [1, d-1] , these error terms are for low degree acc which only run for two powers of alpha
    // self.u += &(rhs.u * r); this seems to be step 6 by acc prover where alpha = r, would need only r[..2] but why one extra power r[..3]? 
    fn fold_compressed(
        &mut self,
        rhs: &Self,
        zeta_cross_term_comm: &C,
        compressed_cross_term_sums: &[F],
        r: &F,
    ) where
        C: AdditiveCommitment<F>,
    {
        let one = F::ONE;
        let powers_of_r = powers(*r)
            .take(compressed_cross_term_sums.len().max(1) + 2)
            .collect_vec();
        izip_eq!(&mut self.instances, &rhs.instances)
            .for_each(|(lhs, rhs)| izip_eq!(lhs, rhs).for_each(|(lhs, rhs)| *lhs += &(*rhs * r)));
        izip_eq!(&mut self.witness_comms, &rhs.witness_comms)
            .for_each(|(lhs, rhs)| *lhs = C::sum_with_scalar([&one, r], [lhs, rhs]));
        izip_eq!(&mut self.challenges, &rhs.challenges).for_each(|(lhs, rhs)| *lhs += &(*rhs * r));
        self.u += &(rhs.u * r);
        self.e_comm = {
            let comms = [&self.e_comm, zeta_cross_term_comm, &rhs.e_comm];
            C::sum_with_scalar(&powers_of_r[..3], comms)
        };
        *self.compressed_e_sum.as_mut().unwrap() += &inner_product(
            &powers_of_r[1..],
            chain![
                compressed_cross_term_sums,
                [rhs.compressed_e_sum.as_ref().unwrap()]
            ],
        );
    }

}


impl<F, Comm> ProtostarAccumulatorInstance<F, Comm>
where
    F: Field,
{
    pub fn unwrap_comm<C: CurveAffine>(self) -> ProtostarAccumulatorInstance<F, C>
    where
        Comm: AsRef<C>,
    {
        ProtostarAccumulatorInstance {
            instances: self.instances,
            witness_comms: chain![self.witness_comms.iter().map(AsRef::as_ref).copied()].collect(),
            challenges: self.challenges,
            u: self.u,
            e_comm: *self.e_comm.as_ref(),
            compressed_e_sum: self.compressed_e_sum,
        }
    }
}
