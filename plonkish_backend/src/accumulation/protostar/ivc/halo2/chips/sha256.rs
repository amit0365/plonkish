//! The [SHA-256] hash function.
//!
//! [SHA-256]: https://tools.ietf.org/html/rfc6234

use std::cmp::min;
use std::convert::TryInto;
use std::fmt;

use halo2_proofs::{
    circuit::{Chip, Layouter, SimpleFloorPlanner, Value}, dev::{CircuitLayout, MockProver}, halo2curves::bn256::Fr, plonk::{Circuit, ConstraintSystem, Error}
};
use plotters::{prelude::BitMapBackend, style::WHITE};
use rand::{rngs::StdRng, RngCore};
use crate::{
    frontend::halo2::CircuitExt, util::arithmetic::{
        fe_to_fe, CurveAffine, Field, FromUniformBytes, MultiMillerLoop, PrimeFieldBits,
        TwoChainCurve,
    }};

mod table16;

pub use table16::{BlockWord, Table16Chip, Table16Config};

/// The size of a SHA-256 block, in 32-bit words.
pub const BLOCK_SIZE: usize = 16;
/// The size of a SHA-256 digest, in 32-bit words.
const DIGEST_SIZE: usize = 8;

/// The set of circuit instructions required to use the [`Sha256`] gadget.
pub trait Sha256Instructions<F: Field>: Chip<F> {
    /// Variable representing the SHA-256 internal state.
    type State: Clone + fmt::Debug;
    /// Variable representing a 32-bit word of the input block to the SHA-256 compression
    /// function.
    type BlockWord: Copy + fmt::Debug + Default;

    /// Places the SHA-256 IV in the circuit, returning the initial state variable.
    fn initialization_vector(&self, layouter: &mut impl Layouter<F>) -> Result<Self::State, Error>;

    /// Creates an initial state from the output state of a previous block
    fn initialization(
        &self,
        layouter: &mut impl Layouter<F>,
        init_state: &Self::State,
    ) -> Result<Self::State, Error>;

    /// Starting from the given initialized state, processes a block of input and returns the
    /// final state.
    fn compress(
        &self,
        layouter: &mut impl Layouter<F>,
        initialized_state: &Self::State,
        input: [Self::BlockWord; BLOCK_SIZE],
    ) -> Result<Self::State, Error>;

    /// Converts the given state into a message digest.
    fn digest(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
    ) -> Result<[Self::BlockWord; DIGEST_SIZE], Error>;
}

/// The output of a SHA-256 circuit invocation.
#[derive(Debug)]
pub struct Sha256Digest<BlockWord>(pub [BlockWord; DIGEST_SIZE]);

/// A gadget that constrains a SHA-256 invocation. It supports input at a granularity of
/// 32 bits.
#[derive(Debug)]
pub struct Sha256<F: Field, CS: Sha256Instructions<F>> {
    chip: CS,
    state: CS::State,
    cur_block: Vec<CS::BlockWord>,
    length: usize,
}

impl<F: Field, Sha256Chip: Sha256Instructions<F>> Sha256<F, Sha256Chip> {
    /// Create a new hasher instance.
    pub fn new(chip: Sha256Chip, mut layouter: impl Layouter<F>) -> Result<Self, Error> {
        let state = chip.initialization_vector(&mut layouter)?;
        Ok(Sha256 {
            chip,
            state,
            cur_block: Vec::with_capacity(BLOCK_SIZE),
            length: 0,
        })
    }

    /// Digest data, updating the internal state.
    pub fn update(
        &mut self,
        mut layouter: impl Layouter<F>,
        mut data: &[Sha256Chip::BlockWord],
    ) -> Result<(), Error> {
        self.length += data.len() * 32;

        // Fill the current block, if possible.
        let remaining = BLOCK_SIZE - self.cur_block.len();
        let (l, r) = data.split_at(min(remaining, data.len()));
        self.cur_block.extend_from_slice(l);
        data = r;

        // If we still don't have a full block, we are done.
        if self.cur_block.len() < BLOCK_SIZE {
            return Ok(());
        }

        // Process the now-full current block.
        self.state = self.chip.compress(
            &mut layouter,
            &self.state,
            self.cur_block[..]
                .try_into()
                .expect("cur_block.len() == BLOCK_SIZE"),
        )?;
        self.cur_block.clear();

        // Process any additional full blocks.
        let mut chunks_iter = data.chunks_exact(BLOCK_SIZE);
        for chunk in &mut chunks_iter {
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                chunk.try_into().expect("chunk.len() == BLOCK_SIZE"),
            )?;
        }

        // Cache the remaining partial block, if any.
        let rem = chunks_iter.remainder();
        self.cur_block.extend_from_slice(rem);

        Ok(())
    }

    /// Retrieve result and consume hasher instance.
    pub fn finalize(
        mut self,
        mut layouter: impl Layouter<F>,
    ) -> Result<Sha256Digest<Sha256Chip::BlockWord>, Error> {
        // Pad the remaining block
        if !self.cur_block.is_empty() {
            let padding = vec![Sha256Chip::BlockWord::default(); BLOCK_SIZE - self.cur_block.len()];
            self.cur_block.extend_from_slice(&padding);
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                self.cur_block[..]
                    .try_into()
                    .expect("cur_block.len() == BLOCK_SIZE"),
            )?;
        }
        self.chip
            .digest(&mut layouter, &self.state)
            .map(Sha256Digest)
    }

    /// Convenience function to compute hash of the data. It will handle hasher creation,
    /// data feeding and finalization.
    pub fn digest(
        chip: Sha256Chip,
        layouter: &mut impl Layouter<F>,
        data: &[Sha256Chip::BlockWord],
    ) -> Result<Sha256Digest<Sha256Chip::BlockWord>, Error> {
        let mut hasher = Self::new(chip, layouter.namespace(|| "init"))?;
        hasher.update(layouter.namespace(|| "update"), data)?;
        let result = hasher.finalize(layouter.namespace(|| "finalize"))?;
        Ok(result)

    }
}

pub const INPUT_RAW_2: [u32; 16] =
    [0b01111000100000000000000000000000; 16];
pub const INPUT_RAW_3: [u32; 16 * 3] =
    [0b01111000100000000000000000000000; 16 * 3];
pub const INPUT_RAW_5: [u32; 16 * 5] =
    [0b01111000100000000000000000000000; 16 * 5];
pub const INPUT_RAW_9: [u32; 16 * 9] =
    [0b01111000100000000000000000000000; 16 * 9];
pub const INPUT_RAW_17: [u32; 16 * 17] =
    [0b01111000100000000000000000000000; 16 * 17];
pub const INPUT_RAW_33: [u32; 16 * 33] =
    [0b01111000100000000000000000000000; 16 * 33];
pub const INPUT_RAW_65: [u32; 16 * 65] =
    [0b01111000100000000000000000000000; 16 * 65];
pub const INPUT_RAW_129: [u32; 16 * 129] =
    [0b01111000100000000000000000000000; 16 * 129];
pub const INPUT_RAW_257: [u32; 16 * 257] =
    [0b01111000100000000000000000000000; 16 * 257];
pub const INPUT_RAW_513: [u32; 16 * 513] =
    [0b01111000100000000000000000000000; 16 * 513];
pub const INPUT_RAW_1025: [u32; 16 * 1025] =
    [0b01111000100000000000000000000000; 16 * 1025];

pub const INPUT_2: [BlockWord; 16] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16];
pub const INPUT_3: [BlockWord; 16 * 3] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16 * 3];
pub const INPUT_5: [BlockWord; 16 * 5] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16 * 5];
pub const INPUT_9: [BlockWord; 16 * 9] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16 * 9];
pub const INPUT_17: [BlockWord; 16 * 17] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16 * 17];
pub const INPUT_33: [BlockWord; 16 * 33] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16 * 33];
pub const INPUT_65: [BlockWord; 16 * 65] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16 * 65];
pub const INPUT_129: [BlockWord; 16 * 129] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16 * 129];
pub const INPUT_257: [BlockWord; 16 * 257] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16 * 257];
pub const INPUT_513: [BlockWord; 16 * 513] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16 * 513];
pub const INPUT_1025: [BlockWord; 16 * 1025] =
    [BlockWord(Value::known(0b01111000100000000000000000000000)); 16 * 1025];

#[derive(Default)]
pub struct Sha256Circuit {
    input_size: usize,
}

impl Sha256Circuit {
    pub fn new(input_size: usize) -> Self {
        Self { input_size }
    }
}

impl Circuit<Fr> for Sha256Circuit {
    type Params = ();
    type Config = Table16Config<Fr>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let advice = (0..7).map(|_| meta.advice_column()).collect::<Vec<_>>();
        Table16Chip::configure(meta, advice.try_into().unwrap())
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        Table16Chip::load(config.clone(), &mut layouter)?;
        let chip = Table16Chip::construct(config);
        let input = match self.input_size {
            2 => INPUT_2.as_slice(),
            3 => INPUT_3.as_slice(),
            5 => INPUT_5.as_slice(),
            9 => INPUT_9.as_slice(),
            17 => INPUT_17.as_slice(),
            33 => INPUT_33.as_slice(),
            65 => INPUT_65.as_slice(),
            129 => INPUT_129.as_slice(),
            257 => INPUT_257.as_slice(),
            513 => INPUT_513.as_slice(),
            1025 => INPUT_1025.as_slice(),
            _ => panic!("Unexpected input_size: {}", self.input_size),
        };
        Sha256::digest(chip, &mut layouter, input).map(|_| ())
    }
}

impl CircuitExt<Fr> for Sha256Circuit {
    fn rand(k: usize, _: impl RngCore) -> Self {
        assert!(k >= 16);
        let input_size = if k > 22 {
            1025
        } else {
            [33, 65, 129, 257, 513, 1025][k - 17]
        };
        Self { input_size }
    }

    fn instances(&self) -> Vec<Vec<Fr>> {
        Vec::new()
    }
}


// Todo: Allow to pass an input and constrain correctness against a PI or similar.
#[derive(Default)]
struct MyCircuit {
    iter_num: usize,
}

impl Circuit<Fr> for MyCircuit {
    type Params = ();
    type Config = Table16Config<Fr>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let advice = (0..7).map(|_| meta.advice_column()).collect::<Vec<_>>();
        Table16Chip::configure(meta, advice.try_into().unwrap())
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        Table16Chip::load(config.clone(), &mut layouter)?;
        let table16_chip = Table16Chip::construct(config);

        let mut test_input = [BlockWord(Value::known(0xff)); 8];

        for _ in 0..self.iter_num {
            test_input = Sha256::digest(
                table16_chip.clone(),
                &mut layouter,
                &test_input,
            )?
            .0;
        }
        Ok(())
    }
}

#[test]
pub fn sha_test_iter() {
    let k = 17;
    let circuit = MyCircuit { iter_num: 1 };
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    prover.assert_satisfied();
}

#[test]
pub fn sha_test() {
    let k = 17;
    let circuit = Sha256Circuit{input_size: 33};
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    prover.assert_satisfied();
    println!("Witness Count: {:?}", prover.witness_count);
    println!("Copy Count: {:?}", prover.copy_count);
}

use plotters::prelude::*;
#[test]
pub fn sha_test_layout() {
    let root =
        BitMapBackend::new("sha-256-table16-chip-layout.png", (1024, 3480)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
        .titled("16-bit Table SHA-256 Chip", ("sans-serif", 60))
        .unwrap();

    let k = 17;
    let circuit = Sha256Circuit{input_size: 33};
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    prover.assert_satisfied();
    println!("Witness Count: {:?}", prover.witness_count);
    println!("Copy Count: {:?}", prover.copy_count);

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