//! An easy-to-use implementation of the Poseidon Hash in the form of a Halo2 Chip. While the Poseidon Hash function
//! is already implemented in halo2_gadgets, there is no wrapper chip that makes it easy to use in other circuits.
use halo2_gadgets::poseidon::{primitives::{ConstantLength, Hash as inlineHash, Spec}, Hash, Pow5Chip, Pow5Config};
use halo2_base::{halo2_proofs::{
    circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Value}, dev::MockProver, halo2curves::{bn256::{self, Fq as Fp}, grumpkin}, plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed}
}, utils::FromUniformBytes};
use halo2_proofs::arithmetic::Field;
use crate::{accumulation::protostar::ivc::halo2::ivc_circuits::primary::{RATE, T}, util::{arithmetic::{PrimeFieldBits, TwoChainCurve}, end_timer, start_timer}};
use halo2_base::utils::BigPrimeField;
use rand::rngs::OsRng;
use super::spec::{PoseidonSpecFp, PoseidonSpec};
use std::{fs::File, marker::PhantomData};
// use halo2_gadgets::poseidon::{primitives::{ConstantLength, Hash as inlineHash, Spec}, Hash, Pow5Chip, Pow5Config};
use poseidon2::circuit::{hash_chip::NUM_PARTIAL_SBOX, spec::PoseidonSpec as Poseidon2ChipSpec};

use poseidon2::circuit::{primitives::{ConstantLength as ConstantLength2, Hash as Hash2}, pow5::{Pow5Chip as Poseidon2Pow5Chip, Pow5Config as Poseidon2Pow5Config}};
use crate::accumulation::protostar::ivc::halo2::chips::poseidon::spec::PoseidonSpec as PoseidonChipSpec;
const L: usize = 13;

#[derive(Debug, Clone)]
pub struct PoseidonConfig<C, const WIDTH: usize, const RATE: usize, const L: usize> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub pow5_config: Pow5Config<C::Scalar, WIDTH, RATE>,
}

#[derive(Debug, Clone)]
pub struct PoseidonChip<
    C,
    S: Spec<C::Scalar, WIDTH, RATE>,
    const WIDTH: usize,
    const RATE: usize,
    const L: usize,
> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits + FromUniformBytes<64>,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    config: PoseidonConfig<C, WIDTH, RATE, L>,
    _marker: PhantomData<S>,
}

impl<C, S: Spec<C::Scalar, WIDTH, RATE>, const WIDTH: usize, const RATE: usize, const L: usize>
    PoseidonChip<C, S, WIDTH, RATE, L>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    /// Constructs a new Poseidon Chip given a PoseidonConfig
    pub fn construct(config: PoseidonConfig<C, WIDTH, RATE, L>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    /// Configures the Poseidon Chip
    pub fn configure(
        meta: &mut ConstraintSystem<C::Scalar>,
        state: [Column<Advice>; WIDTH],
        partial_sbox: Column<Advice>,
        rc_a: [Column<Fixed>; WIDTH],
        rc_b: [Column<Fixed>; WIDTH],
    ) -> PoseidonConfig<C, WIDTH, RATE, L> {
        let pow5_config = Pow5Chip::configure::<S>(meta, state, partial_sbox, rc_a, rc_b);

        PoseidonConfig { pow5_config }
    }

    /// Performs poseidon hash on the given input cells. Returns the output cell.
    pub fn hash(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        input_cells: [AssignedCell<C::Scalar, C::Scalar>; L],
    ) -> Result<AssignedCell<C::Scalar, C::Scalar>, Error> {
        let pow5_chip = Pow5Chip::construct(self.config.pow5_config.clone());

        let hasher = Hash::<_, _, S, ConstantLength<L>, WIDTH, RATE>::init(
            pow5_chip,
            layouter.namespace(|| "hasher"),
        )?;

        let timer = start_timer(|| format!("hash {}", L));
        let hash = hasher.hash(layouter.namespace(|| "hash"), input_cells);
        end_timer(timer);

        hash
    }
}

#[derive(Debug, Clone)]
pub struct Poseidon2Config<C, const WIDTH: usize, const RATE: usize, const L: usize> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub pow5_config: Poseidon2Pow5Config<C::Scalar, WIDTH, RATE>,
}

#[derive(Debug, Clone)]
pub struct Poseidon2Chip<
    C: TwoChainCurve,
    S: Spec<C::Scalar, WIDTH, RATE>,
    const WIDTH: usize,
    const RATE: usize,
    const L: usize,
> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    config: Poseidon2Config<C, WIDTH, RATE, L>,
    _marker: PhantomData<S>,
}

impl<C, S: Spec<C::Scalar, WIDTH, RATE>, const WIDTH: usize, const RATE: usize, const L: usize>
    Poseidon2Chip<C, S, WIDTH, RATE, L>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    /// Constructs a new Poseidon Chip given a PoseidonConfig
    pub fn construct(config: Poseidon2Config<C, WIDTH, RATE, L>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    /// Configures the Poseidon Chip
    pub fn configure(
        meta: &mut ConstraintSystem<C::Scalar>,
        state: [Column<Advice>; WIDTH],
        partial_sbox: [Column<Advice>; NUM_PARTIAL_SBOX],
        rc_full_rounds: [Column<Fixed>; WIDTH],
        rc_partial_rounds: [Column<Fixed>; NUM_PARTIAL_SBOX],
        pad_fixed: [Column<Fixed>; WIDTH],
    ) -> Poseidon2Config<C, WIDTH, RATE, L> {
        let pow5_config = Poseidon2Pow5Chip::configure::<S>(meta, state, partial_sbox, rc_full_rounds, rc_partial_rounds, pad_fixed);

        Poseidon2Config { pow5_config }
    }

    /// Performs poseidon hash on the given input cells. Returns the output cell.
    pub fn hash(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        input_cells: [AssignedCell<C::Scalar, C::Scalar>; L],
    ) -> Result<AssignedCell<C::Scalar, C::Scalar>, Error> {
        let pow5_chip = Poseidon2Pow5Chip::construct(self.config.pow5_config.clone());
        let hasher = Hash::<_, _, S, ConstantLength<L>, WIDTH, RATE>::init(
            pow5_chip,
            layouter.namespace(|| "hasher"),
        )?;
        hasher.hash(layouter.namespace(|| "hash"), input_cells)
    }
}

struct PoseidonHashCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    message: [C::Scalar; L],
}

impl<C> Circuit<C::Scalar> for PoseidonHashCircuit<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    type Config = (PoseidonConfig<C, T, RATE, L>, [Column<Advice>; T + 1]);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        let advices = [0; T + 1].map(|_| meta.advice_column());
        let constants = [0; 2*T].map(|_| meta.fixed_column());
        meta.enable_constant(constants[T]);


        let poseidon_config = PoseidonChip::<C, PoseidonChipSpec, T, RATE, L>::configure(
            meta,
            advices[..T].try_into().unwrap(),
            advices[T],
            constants[..T].try_into().unwrap(), 
            constants[T..].try_into().unwrap(), 
        );

        (poseidon_config, advices)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {

        let chip = PoseidonChip::<C, PoseidonChipSpec, T, RATE, L>::construct(
            config.0,
        ); 

        let mut messages_vec: Vec<AssignedCell<C::Scalar, C::Scalar>> = vec![];
        for message in self.message.iter() {
            messages_vec.push(layouter.assign_region(
                || "load message",
                |mut region| {
                    region.assign_advice(
                        || "value",
                        config.1[0],
                        0,
                        || Value::known(*message)
                    )
                },
            )?);
        };

        let message: [AssignedCell<C::Scalar, C::Scalar>; L] =
        match messages_vec.try_into() {
            Ok(arr) => arr,
            Err(_) => panic!("Failed to convert Vec to Array"),
        };
        let timer = start_timer(|| "hash");
        let hash = chip.hash(
            layouter.namespace(|| "perform poseidon entry hash"),
            message,
        )?;
        end_timer(timer);
        // let chip = PoseidonChip::<C, PoseidonSpec, 5, 4, L>::construct(
        //     config.0,
        // ); 

        // chip.hash(
        //     layouter.namespace(|| "perform poseidon entry hash"),
        //     message,
        // )?;
        
        print!("hash: {:?}", hash.value_field());

        Ok(())

    }
}
struct Poseidon2HashCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    message: [C::Scalar; L],
}

// impl<C> Circuit<C::Scalar> for Poseidon2HashCircuit<C>
// where
//     C: TwoChainCurve,
//     C::Scalar: BigPrimeField + PrimeFieldBits,
//     C::Base: BigPrimeField + PrimeFieldBits,
// {
//     type Config = (Poseidon2Config<C, T, RATE, L>, [Column<Advice>; T + 1]);
//     type FloorPlanner = SimpleFloorPlanner;
//     type Params = ();

//     fn without_witnesses(&self) -> Self {
//         unimplemented!()
//     }

//     fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
//         let advices = [0; T + 1].map(|_| meta.advice_column());
//         let constants = [0; 2*T].map(|_| meta.fixed_column());
//         meta.enable_constant(constants[T]);


//         let poseidon_config = Poseidon2Chip::<C, Poseidon2ChipSpec, T, RATE, L>::configure(
//             meta,
//             advices[..T].try_into().unwrap(),
//             advices[T],
//             constants[..T].try_into().unwrap(), 
//             constants[T..].try_into().unwrap(), 
//         );

//         (poseidon_config, advices)
//     }

//     fn synthesize(
//         &self,
//         config: Self::Config,
//         mut layouter: impl Layouter<C::Scalar>,
//     ) -> Result<(), Error> {

//         let chip = Poseidon2Chip::<C, Poseidon2ChipSpec, T, RATE, L>::construct(
//             config.0,
//         ); 

//         let mut messages_vec: Vec<AssignedCell<C::Scalar, C::Scalar>> = vec![];
//         for message in self.message.iter() {
//             messages_vec.push(layouter.assign_region(
//                 || "load message",
//                 |mut region| {
//                     region.assign_advice(
//                         || "value",
//                         config.1[0],
//                         0,
//                         || Value::known(*message)
//                     )
//                 },
//             )?);
//         };

//         let message: [AssignedCell<C::Scalar, C::Scalar>; L] =
//         match messages_vec.try_into() {
//             Ok(arr) => arr,
//             Err(_) => panic!("Failed to convert Vec to Array"),
//         };
//         let timer = start_timer(|| "hash");
//         let hash = chip.hash(
//             layouter.namespace(|| "perform poseidon entry hash"),
//             message,
//         )?;
//         end_timer(timer);
//         // let chip = PoseidonChip::<C, PoseidonSpec, 5, 4, L>::construct(
//         //     config.0,
//         // ); 

//         // chip.hash(
//         //     layouter.namespace(|| "perform poseidon entry hash"),
//         //     message,
//         // )?;
        
//         print!("hash: {:?}", hash.value_field());

//         Ok(())

//     }
// }


// L = 1, T = 3
// prover.witness_count: 151
// prover.copy_count: 11
// T = 7
// prover.witness_count: 315
// prover.copy_count: 27

// L = 10, T = 3
// prover.witness_count: 748
// prover.copy_count: 43
// T = 7
// prover.witness_count: 631
// prover.copy_count: 47

// L = 10
// T = 3
// prover.witness_count: 2238
// prover.copy_count: 123
// T = 7
// prover.witness_count: 1572
// prover.copy_count: 107

#[test]

fn poseidon_hash_longer_input_custom() {
    use plotters::prelude::*;
    let root = BitMapBackend::new("HashChip_Poseidon.png", (1024, 3096)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("HashChip", ("sans-serif", 60)).unwrap();
    let rng = OsRng;

    let message = [0; L].map(|_| Fp::random(rng));
    // let output =
    //     inlineHash::<_, PoseidonSpec, ConstantLength<L>, T, RATE>::init().hash(message);
    // println!("output: {:?}", output);

    let k = 7;
    let circuit = PoseidonHashCircuit::<grumpkin::G1Affine> {
        message,
    };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    println!("prover.witness_count: {:?}", prover.witness_count);
    println!("prover.copy_count: {:?}", prover.copy_count);
    assert_eq!(prover.verify(), Ok(()));

    halo2_base::halo2_proofs::dev::CircuitLayout::default()
    .render(k, &circuit, &root)
    .unwrap();
}

// #[test]
// fn poseidon2_hash_longer_input_custom() {
//     use plotters::prelude::*;
//     let root = BitMapBackend::new("HashChip_Poseidon2.png", (1024, 3096)).into_drawing_area();
//     root.fill(&WHITE).unwrap();
//     let root = root.titled("HashChip", ("sans-serif", 60)).unwrap();
//     let rng = OsRng;

//     let k = 8; // Reduce from 9 to 8
//     let message = [0; L].map(|_| Fp::random(rng)); // Reduce L from 13 to 5

//     let circuit = Poseidon2HashCircuit::<grumpkin::G1Affine> {
//         message,
//     };

//     let prover = MockProver::run(k, &circuit, vec![]).unwrap();
//     let result = prover.verify();
//     halo2_base::halo2_proofs::dev::CircuitLayout::default()
//     .render(k, &circuit, &root)
//     .unwrap();
// }
