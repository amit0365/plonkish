use crate::{
    accumulation::protostar::ivc::halo2::chips::main_chip::LOOKUP_BITS, backend::{hyperplonk::prover::{instance_polys, lookup_compressed_polys, lookup_m_polys_uncompressed, lookup_uncompressed_polys}, PlonkishCircuit, PlonkishCircuitInfo, WitnessEncoding}, poly::multilinear::MultilinearPolynomial, util::{
        arithmetic::{BatchInvert, Field},
        expression::{Expression, Query, Rotation},
        Itertools,
    }
};
use ark_std::iterable::Iterable;
use halo2_proofs::{
    circuit::Value,
    plonk::{
        self, Advice, Any, Assigned, Assignment, Challenge, Circuit, Column, ConstraintSystem, Error, Fixed, FloorPlanner, Instance, Selector
    },
};
use rand::RngCore;
use core::ops::RangeInclusive;
use std::{
    cell::RefCell, collections::{HashMap, HashSet}, iter, mem, time::Instant
};
use halo2_proofs::{
    circuit::{
        floor_planner::{folding::strategy, FloorPlannerData, FoldingPass, Folding, MeasurementPass, FoldingPlan},
        Layouter,
    },
};
use crate::util::arithmetic::PrimeField;
use crate::poly::Polynomial;
pub mod layouter;
pub mod circuit;
mod test;

pub trait CircuitExt<F: Field>: Circuit<F> {
    fn rand(k: usize, _: impl RngCore) -> Self;

    fn num_instance(&self) -> Vec<usize> {
        self.instances().iter().map(Vec::len).collect()
    }

    fn instances(&self) -> Vec<Vec<F>>;

    fn accumulator_indices() -> Option<Vec<(usize, usize)>> {
        None
    }

    /// Output the simple selector columns (before selector compression) of the circuit
    fn selectors(_: &Self::Config) -> Vec<Selector> {
        vec![]
    }
}

pub struct Halo2Circuit<F: Field, C: Circuit<F>> {
    k: u32,
    instances: Vec<Vec<F>>,
    circuit: C,
    cs: ConstraintSystem<F>,
    config: C::Config,
    constants: Vec<Column<Fixed>>,
    num_witness_polys: Vec<usize>,
    advice_idx_in_phase: Vec<usize>,
    challenge_idx: Vec<usize>,
    row_mapping: Vec<usize>,
    floor_planner_data: Option<FloorPlannerData>,
}

impl<F: Field, C: CircuitExt<F>> Halo2Circuit<F, C> {
    pub fn new<E: WitnessEncoding>(k: usize, circuit: C, circuit_params: C::Params) -> Self {
        let (cs, config) = {
            let mut cs = ConstraintSystem::default();
            let config = C::configure_with_params(&mut cs, circuit_params);
            (cs, config)
        };
        let constants = cs.constants().clone();

        let num_witness_polys = num_by_phase(&cs.advice_column_phase());
        let advice_idx_in_phase = idx_in_phase(&cs.advice_column_phase());
        let challenge_idx = idx_order_by_phase(&cs.challenge_phase(), 0);
        let row_mapping = E::row_mapping(k);

        Self {
            k: k as u32,
            instances: circuit.instances(),
            circuit,
            cs,
            config,
            constants,
            num_witness_polys,
            advice_idx_in_phase,
            challenge_idx,
            row_mapping,
            floor_planner_data: None,
        }
    }

    pub fn circuit(&self) -> &C {
        &self.circuit
    }

    pub fn update_witness(&mut self, f: impl FnOnce(&mut C)) {
        f(&mut self.circuit);
        self.instances = self.circuit.instances();
    }

}

impl<F: Field, C: Circuit<F>> AsRef<C> for Halo2Circuit<F, C> {
    fn as_ref(&self) -> &C {
        &self.circuit
    }
}

impl<F: PrimeField, C: Circuit<F>> PlonkishCircuit<F> for Halo2Circuit<F, C> {
    fn circuit_info_without_preprocess(&self) -> Result<PlonkishCircuitInfo<F>, crate::Error> {
    let Self {
        k,
        instances,
        cs,
        challenge_idx,
        ..
    } = self;

    let advice_idx = advice_idx(cs);

    let constraints = vec![Expression::Constant(F::ZERO)];
    // let constraints = cs
    //     .gates()
    //     .iter()
    //     .flat_map(|gate| {
    //         gate.polynomials().iter().map(|expression| {
    //             convert_expression(cs, &advice_idx, challenge_idx, expression)
    //         })
    //     })
    //     .collect();

    let gate_expressions: Vec<plonk::Expression<F>> = cs
        .gates()
        .iter()
        .flat_map(|gate| {
            gate.polynomials().iter().cloned()
        })
    .collect_vec();
    // todo assuming each gate has only one selector
    let mut queried_selectors: HashMap<usize, (usize, Vec<usize>)> = cs.gates().iter().map(|gate| {
        let selector_index = gate.queried_selectors().iter().map(|selector| selector.index()).collect_vec().last().cloned().unwrap();
        let degree_vec = gate.polynomials().iter().map(|poly| poly.degree()).collect_vec();
        (selector_index, (gate.polynomials().len(), degree_vec))
    }).collect();

    // not used for error only for creating nark lookup polys so u = 1
    let lookups = cs
        .lookups()
        .iter()
        .map(|lookup| {
            lookup
                .input_expressions()
                .iter()
                .zip(lookup.table_expressions())
                .map(|(input, table)| {
                    let [input, table] = [input, table].map(|expression| {
                        convert_expression(cs, &advice_idx, challenge_idx, expression) 
                    });
                    (input, table)
                })
                .collect_vec()
        })
        .collect_vec();

    // used for error
    let lookup_expressions: Vec<Vec<(plonk::Expression<F>, plonk::Expression<F>)>> = cs
        .lookups()
        .iter()
        .map(|lookup| {
            lookup
                .input_expressions()
                .iter()
                .zip(lookup.table_expressions())
                .map(|(input, table)| {
                    let [input, table] = [input, table].map(|expression| {
                        expression.clone()
                    });
                    (input, table)
                })
                .collect_vec()
        })
        .collect_vec();
    println!("queried_selectors before {:?}", queried_selectors.len());
    if !lookups.is_empty() {
        cs.lookups().iter().map(|lookup| {
            let selector_index = lookup.queried_selectors().iter().map(|selector| selector.index()).collect_vec().last().cloned().unwrap();
            queried_selectors.insert(selector_index, (1, vec![3])); // h constraint
        }).collect_vec();
        queried_selectors.insert(queried_selectors.len(), (1, vec![2])); // g constraint
    } 
    println!("queried_selectors after {:?}", queried_selectors.len());
    let num_instances = instances.iter().map(Vec::len).collect_vec();
    let preprocess_polys =
        vec![vec![F::ZERO; 1 << k]; cs.num_selectors() + cs.num_fixed_columns()];
    let column_idx = column_idx(cs);
    let permutations = cs
        .permutation()
        .get_columns()
        .iter()
        .map(|column| {
            let key = (*column.column_type(), column.index());
            vec![(column_idx[&key], 1)]
        })
        .collect_vec();
    let fixed_permutation_idx_for_permutation_constraints = cs
        .permutation()
        .get_fixed_columns()
        .iter()
        .map(|column| {
            let key = (*column.column_type(), column.index());
            column_idx[&key]
        })
        .collect_vec();

    let fixed_permutation_idx_for_preprocess_poly: Vec<usize> =  fixed_permutation_idx_for_permutation_constraints.clone().iter()
        .map(|&x| {
            if x >= cs.num_instance_columns() {
                x - cs.num_instance_columns()
            } else {
                0
            }
        })
        .collect();

    Ok(PlonkishCircuitInfo {
        k: *k as usize,
        num_instances,
        preprocess_polys,
        num_witness_polys: num_by_phase(&cs.advice_column_phase()),
        num_fixed_columns: cs.num_fixed_columns(),
        num_challenges: num_by_phase(&cs.challenge_phase()),
        constraints,
        gate_expressions,
        lookups,
        lookup_expressions,
        permutations,
        advice_copies: vec![],
        max_degree: Some(cs.degree()),
        fixed_permutation_idx_for_preprocess_poly,
        fixed_permutation_idx_for_permutation_constraints,
        queried_selectors,
        selector_map: HashMap::new(),
        row_map_selector: HashMap::new(),
        selector_groups: vec![],
        floor_planner_data: None,
        last_rows: vec![],
        log_num_betas: 0,
        witness_count: 0,
        copy_count: 0,
    })
}

fn circuit_info(&self) -> Result<PlonkishCircuitInfo<F>, crate::Error> {
    let Self {
        k,
        instances,
        cs,
        config,
        circuit,
        constants,
        row_mapping,
        ..
    } = self;    
    let mut circuit_info = self.circuit_info_without_preprocess()?;
    let num_instances = instances.iter().map(Vec::len).collect_vec();
    let column_idx = column_idx(cs);
    let permutation_column_idx = cs
        .permutation()
        .get_columns()
        .iter()
        .map(|column| {
            let key = (*column.column_type(), column.index());
            (key, column_idx[&key])
        })
        .collect();

    let mut preprocess_collector = PreprocessCollector {
        k: *k,
        num_instances,        
        fixeds: vec![vec![F::ZERO.into(); 1 << k]; cs.num_fixed_columns()],
        permutation: Permutation::new(permutation_column_idx),
        selectors: vec![vec![false; 1 << k]; cs.num_selectors()],
        row_mapping,
        selector_map: HashMap::new(),
        row_map_selector: HashMap::new(),
    };

    let queried_selectors = &circuit_info.queried_selectors;

        let mut plan = FoldingPlan::new(&mut preprocess_collector).unwrap();
        // First pass: measure the regions within the circuit.
        let mut measure = MeasurementPass::new();
        {
            let pass = &mut measure;
            circuit
                .without_witnesses()
                .synthesize(config.clone(), FoldingPass::<_, PreprocessCollector<F>>::measure(pass)).unwrap();
        }


        // Planning:
        // - Position the regions.
        let (regions, column_allocations) = strategy::slot_in_biggest_advice_first(measure.regions);
        plan.regions = regions.clone();

        //- Determine how many rows our planned circuit will require.
        let first_unassigned_row = column_allocations
            .values()
            .map(|a| a.unbounded_interval_start())
            .max()
            .unwrap_or(0);

        let data = FloorPlannerData {
            regions,
            column_allocations,
            first_unassigned_row,
        };

    circuit_info.floor_planner_data = Some(data.clone());

    C::FloorPlanner::synthesize(
        &mut preprocess_collector,
        circuit,
        config.clone(),
        constants.clone(),
        Some(data.clone()),
    )
    .map_err(|err| crate::Error::InvalidSnark(format!("Synthesize failure: {err:?}")))?;

    circuit_info.preprocess_polys = iter::empty()
        .chain(batch_invert_assigned(preprocess_collector.fixeds))
        .chain(preprocess_collector.selectors.into_iter().map(|selectors| {
            selectors
                .into_iter()
                .map(|selector| if selector { F::ONE } else { F::ZERO })
                .collect()
        }))
        .collect();
    circuit_info.permutations = preprocess_collector.permutation.into_cycles().clone();
    
    let mut selector_map = preprocess_collector.selector_map.clone();
    if !circuit_info.lookups.is_empty() {
        selector_map.insert(queried_selectors.len() - 1, (0..1<<LOOKUP_BITS).collect_vec()); //todo hardcoded to 0 for now
    }
    circuit_info.selector_map = selector_map.clone();
    let mut num_betas = 0;
    for (key, values) in &circuit_info.selector_map {
        num_betas += values.len() * queried_selectors.get(key).unwrap_or(&(0, vec![])).0;
    }
    println!("num_betas: {}", num_betas);
    let log_num_betas = ((num_betas as f64).log2().ceil() as usize + 1) & !1;
    println!("log_num_betas: {}", log_num_betas);
    circuit_info.log_num_betas = log_num_betas;

    let instances = self.instances.iter().map(Vec::as_slice).collect_vec();
    let challenges = vec![F::ZERO; circuit_info.num_challenges.iter().sum::<usize>()];
    let phase = 0;
    let mut dummy_witness_collector = DummyWitnessCollector {
        k: self.k,
        phase: phase as u8,
        advice_idx_in_phase: &self.advice_idx_in_phase,
        challenge_idx: &self.challenge_idx,
        instances: instances.as_slice(),
        advices: vec![vec![F::ZERO.into(); 1 << self.k]; self.num_witness_polys[phase]],
        last_rows: vec![0; self.num_witness_polys[phase]],
        challenges: &challenges,
        row_mapping: &self.row_mapping,
        witness_count: 0,
        copy_count: 0,
    };
    let constants = self.constants.clone();
    C::FloorPlanner::synthesize(
        &mut dummy_witness_collector,
        &self.circuit,
        self.config.clone(),
        constants,
        Some(data),
    )
    .map_err(|err| crate::Error::InvalidSnark(format!("Synthesize failure: {err:?}")))?;
    circuit_info.last_rows = dummy_witness_collector.last_rows.clone();
    circuit_info.witness_count = dummy_witness_collector.witness_count;
    circuit_info.copy_count = dummy_witness_collector.copy_count;
    
    let last_row_offset: Vec<usize> = circuit_info.last_rows.iter().map(|&row| row + 1).collect();
    let mut acc_last_row = Vec::new();
    let mut sum = 0;
    for &row in &last_row_offset {
        sum += row;
        acc_last_row.push(sum);
    }
    
    let advice_idx_offset = cs.num_instance_columns() + cs.num_fixed_columns() + cs.num_selectors();
    let mut total_advice_cycles = vec![];
    let mut advice_cycles = vec![];
    let mut total_advice_copies = vec![];
    let mut advice_copies = vec![];
    for cycle in &circuit_info.permutations {
        for (i, j) in cycle {
            if advice_idx(cs).contains(i) {
                advice_cycles.push((*i, *j));
                advice_copies.push(acc_last_row[*i - advice_idx_offset] + *j);
            }
        }
        total_advice_cycles.push(advice_cycles.clone());
        total_advice_copies.push(advice_copies.clone());
        advice_cycles = vec![];
        advice_copies = vec![];
    }
    circuit_info.advice_copies = total_advice_copies;
    Ok(circuit_info)
}

    fn floor_planner_data(&mut self) {
        let data = self.circuit_info().unwrap().floor_planner_data;
        self.floor_planner_data = data;
    }

    fn instances(&self) -> &[Vec<F>] {
        &self.instances
    }

    fn synthesize(&self, phase: usize, challenges: &[F]) -> Result<Vec<Vec<F>>, crate::Error> {
        let instances = self.instances.iter().map(Vec::as_slice).collect_vec();
        let mut witness_collector = WitnessCollector {
            k: self.k,
            phase: phase as u8,
            advice_idx_in_phase: &self.advice_idx_in_phase,
            challenge_idx: &self.challenge_idx,
            instances: instances.as_slice(),
            advices: vec![vec![F::ZERO.into(); 1 << self.k]; self.num_witness_polys[phase]],
            last_rows: vec![0; self.num_witness_polys[phase]],
            challenges,
            row_mapping: &self.row_mapping,
            witness_count: 0,
            copy_count: 0,
        };
        let constants = self.constants.clone();
        let floor_planner_data = self.floor_planner_data.clone();
        C::FloorPlanner::synthesize(
            &mut witness_collector,
            &self.circuit,
            self.config.clone(),
            constants,
            floor_planner_data,
        )
        .map_err(|err| crate::Error::InvalidSnark(format!("Synthesize failure: {err:?}")))?;
        println!("witness_count: {}", witness_collector.witness_count);
        println!("copy_count: {}", witness_collector.copy_count);
        println!("last_rows: {:?}", witness_collector.last_rows);
        Ok(batch_invert_assigned(witness_collector.advices))
    }
}

fn merge_sets(map: &HashMap<usize, Vec<usize>>) -> Vec<Vec<usize>> {
    let mut sets: Vec<HashSet<usize>> = Vec::new();

    for values in map.values() {
        let mut new_set: HashSet<_> = values.iter().cloned().collect();
        let mut to_merge = Vec::new();

        for (i, set) in sets.iter().enumerate() {
            if !new_set.is_disjoint(set) {
                to_merge.push(i);
            }
        }

        for &i in to_merge.iter().rev() {
            new_set.extend(sets.swap_remove(i));
        }

        sets.push(new_set);
    }

    sets.into_iter()
        .map(|set| set.into_iter().collect())
        .collect()
}

#[derive(Debug)]
struct PreprocessCollector<'a, F: Field> {
    k: u32,
    num_instances: Vec<usize>,
    fixeds: Vec<Vec<Assigned<F>>>,
    permutation: Permutation,
    selectors: Vec<Vec<bool>>,
    row_mapping: &'a [usize],
    selector_map: HashMap<usize, Vec<usize>>,
    row_map_selector: HashMap<usize, Vec<usize>>,
}

impl<'a, F: Field> Assignment<F> for PreprocessCollector<'a, F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn exit_region(&mut self) {}

    fn annotate_column<A, AR>(&mut self, _: A, _: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {   
        self.selector_map.entry(selector.index()).or_default().push(row);
        //if selector.index() != 12 { //todo fix thishardcoded to 11 for now -- range_check constraint
            self.row_map_selector.entry(row).or_default().push(selector.index());
        //}
        // let Some(row) = self.row_mapping.get(row).copied() else {
        //     return Err(Error::NotEnoughRowsAvailable { current_k: self.k});
        // };

        if row > 1 << self.k {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        }

        self.selectors[selector.index()][row] = true;

        Ok(())
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        self.num_instances
            .get(column.index())
            .and_then(|num_instances| (row < *num_instances).then(Value::unknown))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Advice>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // let Some(row) = self.row_mapping.get(row).copied() else {
        //     return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        // };

        if row > 1 << self.k {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        }

        *self
            .fixeds
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

        Ok(())
    }

    fn copy(
        &mut self,
        lhs_column: Column<Any>,
        lhs_row: usize,
        rhs_column: Column<Any>,
        rhs_row: usize,
    ) -> Result<(), Error> {
        // let Some(lhs_row) = self.row_mapping.get(lhs_row).copied() else {
        //     return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        // };
        if lhs_row > 1 << self.k {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        }
        // let Some(rhs_row) = self.row_mapping.get(rhs_row).copied() else {
        //     return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        // };
        if rhs_row > 1 << self.k {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        }
        self.permutation
            .copy(lhs_column, lhs_row, rhs_column, rhs_row)
    }

    fn fill_from_row(
        &mut self,
        column: Column<Fixed>,
        from_row: usize,
        to: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        let Some(_) = self.row_mapping.get(from_row) else {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        };

        // if !self.usable_rows.contains(&from_row) {
        //     return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        // }

        let col = self
            .fixeds
            .get_mut(column.index())
            .ok_or(Error::BoundsFailure)?;

        let filler = to.assign()?;
        for row in self.row_mapping.iter().skip(from_row).copied() {
            col[row] = filler;
        }

        Ok(())
    }

    fn get_challenge(&self, _: Challenge) -> Value<F> {
        Value::unknown()
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn pop_namespace(&mut self, _: Option<String>) {}
}

#[derive(Debug)]
struct Permutation {
    column_idx: HashMap<(Any, usize), usize>,
    cycles: Vec<HashSet<(usize, usize)>>,
    cycle_idx: HashMap<(usize, usize), usize>,
}

impl Permutation {
    fn new(column_idx: HashMap<(Any, usize), usize>) -> Self {
        Self {
            column_idx,
            cycles: Default::default(),
            cycle_idx: Default::default(),
        }
    }

    fn copy(
        &mut self,
        lhs_column: Column<Any>,
        lhs_row: usize,
        rhs_column: Column<Any>,
        rhs_row: usize,
    ) -> Result<(), Error> {
        let lhs_idx = *self
            .column_idx
            .get(&(*lhs_column.column_type(), lhs_column.index()))
            .ok_or(Error::ColumnNotInPermutation(lhs_column))?;
        let rhs_idx = *self
            .column_idx
            .get(&(*rhs_column.column_type(), rhs_column.index()))
            .ok_or(Error::ColumnNotInPermutation(rhs_column))?;

        match (
            self.cycle_idx.get(&(lhs_idx, lhs_row)).copied(),
            self.cycle_idx.get(&(rhs_idx, rhs_row)).copied(),
        ) {
            (Some(lhs_cycle_idx), Some(rhs_cycle_idx)) => {
                for cell in self.cycles[rhs_cycle_idx].iter().copied() {
                    self.cycle_idx.insert(cell, lhs_cycle_idx);
                }
                let rhs_cycle = mem::take(&mut self.cycles[rhs_cycle_idx]);
                self.cycles[lhs_cycle_idx].extend(rhs_cycle);
            }
            cycle_idx => {
                let cycle_idx = if let (Some(cycle_idx), None) | (None, Some(cycle_idx)) = cycle_idx
                {
                    cycle_idx
                } else {
                    let cycle_idx = self.cycles.len();
                    self.cycles.push(Default::default());
                    cycle_idx
                };
                for cell in [(lhs_idx, lhs_row), (rhs_idx, rhs_row)] {
                    self.cycles[cycle_idx].insert(cell);
                    self.cycle_idx.insert(cell, cycle_idx);
                }
            }
        };

        Ok(())
    }

    fn into_cycles(self) -> Vec<Vec<(usize, usize)>> {
        self.cycles
            .into_iter()
            .filter_map(|cycle| {
                (!cycle.is_empty()).then(|| cycle.into_iter().sorted().collect_vec())
            })
            .collect()
    }
}

#[derive(Debug)]
struct WitnessCollector<'a, F: Field> {
    k: u32,
    phase: u8,
    advice_idx_in_phase: &'a [usize],
    challenge_idx: &'a [usize],
    instances: &'a [&'a [F]],
    advices: Vec<Vec<Assigned<F>>>,
    last_rows: Vec<usize>,
    challenges: &'a [F],
    row_mapping: &'a [usize],
    witness_count: usize,
    copy_count: usize,
}

impl<'a, F: Field> Assignment<F> for WitnessCollector<'a, F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn exit_region(&mut self) {}

    fn annotate_column<A, AR>(&mut self, _: A, _: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
    }

    fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        self.instances
            .get(column.index())
            .and_then(|column| column.get(row))
            .map(|v| Value::known(*v))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if self.phase != column.column_type().phase() {
            return Ok(());
        }

        if self.last_rows[column.index()] < row {
            self.last_rows[column.index()] = row;
        }

        // let Some(row) = self.row_mapping.get(row).copied() else {
        //     return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        // };

        if row > 1 << self.k {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        }

        *self
            .advices
            .get_mut(self.advice_idx_in_phase[column.index()])
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

        self.witness_count += 1;
        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Fixed>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    //todo implement copy
    fn copy(&mut self, _: Column<Any>, _: usize, _: Column<Any>, _: usize) -> Result<(), Error> {
        self.copy_count += 1;
        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn get_challenge(&self, challenge: Challenge) -> Value<F> {
        self.challenges
            .get(self.challenge_idx[challenge.index()])
            .copied()
            .map(Value::known)
            .unwrap_or_else(Value::unknown)
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn pop_namespace(&mut self, _: Option<String>) {}
}

#[derive(Debug)]
struct DummyWitnessCollector<'a, F: Field> {
    k: u32,
    phase: u8,
    advice_idx_in_phase: &'a [usize],
    challenge_idx: &'a [usize],
    instances: &'a [&'a [F]],
    advices: Vec<Vec<Assigned<F>>>,
    last_rows: Vec<usize>,
    challenges: &'a [F],
    row_mapping: &'a [usize],
    witness_count: usize,
    copy_count: usize,
}

impl<'a, F: Field> Assignment<F> for DummyWitnessCollector<'a, F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn exit_region(&mut self) {}

    fn annotate_column<A, AR>(&mut self, _: A, _: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
    }

    fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        self.instances
            .get(column.index())
            .and_then(|column| column.get(row))
            .map(|v| Value::known(*v))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if self.phase != column.column_type().phase() {
            return Ok(());
        }

        if self.last_rows[column.index()] < row {
            self.last_rows[column.index()] = row;
        }

        // let Some(row) = self.row_mapping.get(row).copied() else {
        //     return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        // };

        if row > 1 << self.k {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        }

        // *self
        //     .advices
        //     .get_mut(self.advice_idx_in_phase[column.index()])
        //     .and_then(|v| v.get_mut(row))
        //     .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

        self.witness_count += 1;
        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Fixed>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn copy(&mut self, _: Column<Any>, _: usize, _: Column<Any>, _: usize) -> Result<(), Error> {
        self.copy_count += 1;
        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn get_challenge(&self, challenge: Challenge) -> Value<F> {
        self.challenges
            .get(self.challenge_idx[challenge.index()])
            .copied()
            .map(Value::known)
            .unwrap_or_else(Value::unknown)
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn pop_namespace(&mut self, _: Option<String>) {}
}

fn advice_idx<F: Field>(cs: &ConstraintSystem<F>) -> Vec<usize> {
    let advice_offset = cs.num_instance_columns() + cs.num_fixed_columns() + cs.num_selectors();
    idx_order_by_phase(&cs.advice_column_phase(), advice_offset)
}

fn column_idx<F: Field>(cs: &ConstraintSystem<F>) -> HashMap<(Any, usize), usize> {

    let advice_idx = advice_idx(cs);
    iter::empty()
        .chain((0..cs.num_instance_columns()).map(|idx| (Any::Instance, idx)))
        .chain((0..cs.num_fixed_columns() + cs.num_selectors()).map(|idx| (Any::Fixed, idx)))
        .enumerate()
        .map(|(idx, column)| (column, idx))
        .chain((0..advice_idx.len()).map(|idx| ((Any::advice(), idx), advice_idx[idx])))
        .collect()
}

fn num_phases(phases: &[u8]) -> usize {
    phases.iter().max().copied().unwrap_or_default() as usize + 1
}

fn num_by_phase(phases: &[u8]) -> Vec<usize> {
    phases.iter().copied().fold(
        vec![0usize; num_phases(phases)],
        |mut num_by_phase, phase| {
            num_by_phase[phase as usize] += 1;
            num_by_phase
        },
    )
}

fn idx_in_phase(phases: &[u8]) -> Vec<usize> {
    phases
        .iter()
        .copied()
        .scan(vec![0; num_phases(phases)], |state, phase| {
            let index = state[phase as usize];
            state[phase as usize] += 1;
            Some(index)
        })
        .collect_vec()
}

fn idx_order_by_phase(phases: &[u8], offset: usize) -> Vec<usize> {
    phases
        .iter()
        .copied()
        .scan(phase_offsets(phases), |state, phase| {
            let index = state[phase as usize];
            state[phase as usize] += 1;
            Some(offset + index)
        })
        .collect()
}

fn phase_offsets(phases: &[u8]) -> Vec<usize> {
    num_by_phase(phases)
        .into_iter()
        .scan(0, |state, num| {
            let offset = *state;
            *state += num;
            Some(offset)
        })
        .collect()
}

pub fn convert_expression<F: Field>(
    cs: &ConstraintSystem<F>,
    advice_idx: &[usize],
    challenge_idx: &[usize],
    expression: & plonk::Expression<F>,
) -> Expression<F> {

    expression.evaluate(
        &|_| unreachable!("AccU should not be used in convert_expression"),
        &|constant| Expression::Constant(constant),
        &|selector| {
            let poly = cs.num_instance_columns() + cs.num_fixed_columns() + selector.index();
            Query::new(poly, Rotation::cur()).into()
        },
        &|query| {
            let poly = cs.num_instance_columns() + query.column_index();
            Query::new(poly, Rotation(query.rotation().0)).into()
        },
        &|query| {
            let poly = advice_idx[query.column_index()];
            Query::new(poly, Rotation(query.rotation().0)).into()
        },
        &|query| Query::new(query.column_index(), Rotation(query.rotation().0)).into(),
        &|challenge| Expression::Challenge(challenge_idx[challenge.index()]),
        &|value| -value,
        &|lhs, rhs| lhs + rhs,
        &|lhs, rhs| lhs * rhs,
        &|value, scalar| value * scalar,
    )
}

fn batch_invert_assigned<F: Field>(assigneds: Vec<Vec<Assigned<F>>>) -> Vec<Vec<F>> {
    let mut denoms: Vec<_> = assigneds
        .iter()
        .map(|f| {
            f.iter()
                .map(|value| value.denominator())
                .collect::<Vec<_>>()
        })
        .collect();

    denoms
        .iter_mut()
        .flat_map(|f| f.iter_mut().filter_map(|d| d.as_mut()))
        .batch_invert();

    assigneds
        .iter()
        .zip(denoms)
        .map(|(assigneds, denoms)| {
            assigneds
                .iter()
                .zip(denoms)
                .map(|(assigned, denom)| {
                    denom
                        .map(|denom| assigned.numerator() * denom)
                        .unwrap_or_else(|| assigned.numerator())
                })
                .collect()
        })
        .collect()
}
