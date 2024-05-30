//! An easy-to-use implementation of the Poseidon Hash in the form of a Halo2 Chip. While the Poseidon Hash function
//! is already implemented in halo2_gadgets, there is no wrapper chip that makes it easy to use in other circuits.
use halo2_gadgets::poseidon::{primitives::{ConstantLength, Spec, Hash as inlineHash}, Hash, Pow5Chip, Pow5Config};
use halo2_base::{halo2_proofs::{
    circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Value}, dev::MockProver, halo2curves::{bn256::{self, Fq as Fp}, grumpkin}, plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed}
}, utils::FromUniformBytes};
use halo2_base::halo2_proofs::arithmetic::Field;
use crate::util::arithmetic::{TwoChainCurve, PrimeFieldBits};
use halo2_base::utils::BigPrimeField;
use rand::rngs::OsRng;
use super::spec::{PoseidonSpecFp, PoseidonSpec};
use std::marker::PhantomData;

const L: usize = 23;

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
    // output: Fp,
    //_marker: PhantomData<S>,
}

impl<C> Circuit<C::Scalar> for PoseidonHashCircuit<C>
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    type Config = (PoseidonConfig<C, 3, 2, L>, [Column<Advice>; 4]);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        let advices = [0; 4].map(|_| meta.advice_column());
        let constants = [0; 6].map(|_| meta.fixed_column());
        meta.enable_constant(constants[3]);


        let poseidon_config = PoseidonChip::<C, PoseidonSpec, 3, 2, L>::configure(
            meta,
            advices[..3].try_into().unwrap(),
            advices[3],
            constants[..3].try_into().unwrap(), 
            constants[3..].try_into().unwrap(), 
        );

        (poseidon_config, advices)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {

        let chip = PoseidonChip::<C, PoseidonSpec, 3, 2, L>::construct(
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
    
        let hash = chip.hash(
            layouter.namespace(|| "perform poseidon entry hash"),
            message,
        )?;

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

#[test]
fn poseidon_hash_longer_input_custom() {

    use plotters::prelude::*;
    let root = BitMapBackend::new("HashChip.png", (1024, 3096)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("HashChip", ("sans-serif", 60)).unwrap();
    let rng = OsRng;

    let message = [0; L].map(|_| Fp::random(rng));
    let output =
        inlineHash::<_, PoseidonSpec, ConstantLength<L>, 3, 2>::init().hash(message);
    println!("output: {:?}", output);

    let k = 9;
    let circuit = PoseidonHashCircuit::<grumpkin::G1Affine> {
        message,
    };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    halo2_base::halo2_proofs::dev::CircuitLayout::default()
    .render(k, &circuit, &root)
    .unwrap();
}