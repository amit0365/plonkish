use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ConstraintSystem, Error,
    },
    poly::commitment::Params,
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use rand::rngs::OsRng;
use halo2_curves::pasta::{pallas, EqAffine};

// use criterion::{criterion_group, criterion_main, Criterion};
// use std::{
//     fs::{create_dir_all, File},
//     io::{prelude::*, BufReader},
//     path::Path,
// };

use crate::sha256::{BlockWord, Sha256, Table16Chip, Table16Config, BLOCK_SIZE};
#[derive(Default)]
struct MyCircuit {}

    impl Circuit<pallas::Base> for MyCircuit {
        type Config = Table16Config<pallas::Base>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> Self::Config {
            Table16Chip::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<pallas::Base>,
        ) -> Result<(), Error> {
            Table16Chip::load(config.clone(), &mut layouter)?;
            let table16_chip = Table16Chip::construct(config);

            // Test vector: "abc"
            let test_input = [
                BlockWord(Value::known(0b01100001011000100110001110000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000000000)),
                BlockWord(Value::known(0b00000000000000000000000000011000)),
            ];

            // Create a message of length 31 blocks
            let mut input = Vec::with_capacity(31 * BLOCK_SIZE);
            for _ in 0..31 {
                input.extend_from_slice(&test_input);
            }

            Sha256::digest(table16_chip, layouter.namespace(|| "'abc' * 2"), &input)?;

            Ok(())
        }
    }