pub mod range_check_opt;
pub mod range_check;

use std::marker::PhantomData;

use crate::{accumulation::protostar::ivc::halo2::{chips::range::range_check::{RangeCheckChip, RangeCheckConfig}, ivc_circuits::primary::NUM_RANGE_COLS}, util::arithmetic::TwoChainCurve,
};
use halo2_base::utils::{BigPrimeField};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    halo2curves::{ff::PrimeFieldBits},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};

use super::main_chip::Number;

#[derive(Debug, Clone)]
pub struct AddConfig {
    pub col_a: Column<Advice>, // stores the value of a
    pub col_b: Column<Advice>, // stores the value of b
    pub col_c: Column<Advice>, // stores the value of c = a + b
    pub selector: Selector,
}

#[derive(Debug, Clone)]
pub struct AddChip<C> {
    pub config: AddConfig,
    marker: PhantomData<C>,
}

impl<C> AddChip<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub fn construct(config: AddConfig) -> Self {
        Self { config, marker: PhantomData }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<C::Scalar>,
        col_a: Column<Advice>,
        col_b: Column<Advice>,
        col_c: Column<Advice>,
        add_selector: Selector,
    ) -> AddConfig {
        meta.create_gate("add", |meta| {
            let s = meta.query_selector(add_selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            vec![s * (a + b - c)]
        });

        AddConfig {
            col_a,
            col_b,
            col_c,
            selector: add_selector,
        }
    }

    pub fn assign(
        &self,
        a: C::Scalar,
        b: C::Scalar,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<
        (
            AssignedCell<C::Scalar, C::Scalar>,
            AssignedCell<C::Scalar, C::Scalar>,
            AssignedCell<C::Scalar, C::Scalar>,
        ),
        Error,
    > {
        layouter.assign_region(
            || "initialize value and sum",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let a_cell =
                    region.assign_advice(|| "a", self.config.col_a, 0, || Value::known(a))?;

                let b_cell =
                    region.assign_advice(|| "b", self.config.col_b, 0, || Value::known(b))?;

                let c_cell = region.assign_advice(
                    || "a + b",
                    self.config.col_c,
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;

                Ok((a_cell, b_cell, c_cell))
            },
        )
    }
}

#[derive(Debug, Clone)]
pub struct TestConfig {
    pub addchip_config: AddConfig,
    pub range_check_config: RangeCheckConfig,
    pub lookup_u8_table: Column<Fixed>,
}

// The test circuit takes two inputs a and b.
// It adds them together by using the add chip to produce c = a + b.
// Performs a range check on a, b and c. Each value should lie in N_BYTES.
#[derive(Default, Clone, Debug)]
struct TestCircuit<C, const N_BYTES: usize> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    pub a: C::Scalar,
    pub b: C::Scalar,
}


impl<C, const N_BYTES: usize> Circuit<C::Scalar> for TestCircuit<C, N_BYTES> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{
    type Params = ();
    type Config = TestConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        let z = [(); NUM_RANGE_COLS].map(|_| meta.advice_column());
        let lookup_u8_table = meta.fixed_column();

        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();

        for z in z {
            meta.enable_equality(z);
        }

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);

        let constants = meta.fixed_column();
        meta.enable_constant(constants);

        let add_selector = meta.selector();
        let lookup_enable_selector = meta.complex_selector();

        let range_check_config =
            RangeCheckChip::<C>::configure(meta, z[0], lookup_u8_table, lookup_enable_selector);

        let addchip_config = AddChip::<C>::configure(meta, a, b, c, add_selector);

        {
            TestConfig {
                addchip_config,
                range_check_config,
                lookup_u8_table,
            }
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {
        // Initiate the add chip
        let addchip = AddChip::<C>::construct(config.addchip_config);
        let (a_cell, b_cell, c_cell) =
            addchip.assign(self.a, self.b, layouter.namespace(|| "add chip"))?;

        // Load the lookup table
        let range_chip = RangeCheckChip::<C>::construct(config.range_check_config);
        range_chip.load_range_check_table(&mut layouter, config.lookup_u8_table)?;

        // check range on a, b and c
        // range_chip.assign(
        //     layouter.namespace(|| "range check a"),
        //     &Number(a_cell),
        //     8*N_BYTES,
        // )?;
        // range_chip.assign(
        //     layouter.namespace(|| "range check b"),
        //     &Number(b_cell),
        //     8*N_BYTES,
        // )?;
        // println!("a and b assigned");
        // range_chip.assign(
        //     layouter.namespace(|| "range check c"),
        //     &Number(c_cell),
        //     8*N_BYTES,
        // )?;

        range_chip.assign(
            &mut layouter,
            &Number(a_cell),
            8*N_BYTES,
        )?;
        range_chip.assign(
            &mut layouter.namespace(|| "range check b"),
            &Number(b_cell),
            8*N_BYTES,
        )?;
        println!("a and b assigned");
        range_chip.assign(
            &mut layouter.namespace(|| "range check c"),
            &Number(c_cell),
            8*N_BYTES,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod testing {
    use super::TestCircuit;
    use halo2_proofs::{
        dev::{FailureLocation, MockProver, VerifyFailure},
        halo2curves::bn256::{self, Fr as Fp},
        plonk::Any,
    };

    // a = (1 << 16) - 2 = 0xfffe
    // b = 1
    // c = a + b = 0xffff
    // All the values are within 2 bytes range.
    #[test]
    fn test_none_overflow_16bits() {
        let k = 9;

        // a: new value
        let a = Fp::from((1 << 16) - 2);
        let b = Fp::from(1);

        let circuit = TestCircuit::<bn256::G1Affine, 2> { a, b };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    // a = (1 << 16) - 2 = 0xfffe
    // b = 2
    // c = a + b = 0x10000
    // a and b are within 2 bytes range.
    // c overflows 2 bytes so the circuit should fail.
    #[test]
    fn test_overflow_16bits() {
        let k = 9;

        let a = Fp::from((1 << 16) - 2);
        let b = Fp::from(2);

        let circuit = TestCircuit::<bn256::G1Affine, 2> { a, b };
        let invalid_prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert_eq!(
            invalid_prover.verify(),
            Err(vec![
                VerifyFailure::Permutation {
                    column: (Any::advice(), 0).into(),
                    location: FailureLocation::InRegion {
                        region: (4, "range check value").into(),
                        offset: 2
                    }
                },
                VerifyFailure::Permutation {
                    column: (Any::Fixed, 1).into(),
                    location: FailureLocation::OutsideRegion { row: 2 }
                },
            ])
        );
    }

    // a is the max value within the range (32 bits / 4 bytes)
    // a = 0x-ff-ff-ff-ff
    // b = 1
    // a and b are within 4 bytes range.
    // c overflows 4 bytes so the circuit should fail.
    #[test]
    fn test_overflow_32bits() {
        let k = 9;

        let a = Fp::from(0xffffffff);
        let b = Fp::from(1);

        let circuit = TestCircuit::<bn256::G1Affine, 4> { a, b };
        let invalid_prover = MockProver::run(k, &circuit, vec![]).unwrap();

        assert_eq!(
            invalid_prover.verify(),
            Err(vec![
                VerifyFailure::Permutation {
                    column: (Any::advice(), 0).into(),
                    location: FailureLocation::InRegion {
                        region: (4, "range check value").into(),
                        offset: 4
                    }
                },
                VerifyFailure::Permutation {
                    column: (Any::Fixed, 1).into(),
                    location: FailureLocation::OutsideRegion { row: 2 }
                },
            ])
        );
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn print_range_check_test() {
        use plotters::prelude::*;

        let root =
            BitMapBackend::new("range-check-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Range Check Layout", ("sans-serif", 60))
            .unwrap();

        // let circuit = TestCircuit::<bn256::G1Affine, 4> {
        //     a: Fp::from(0x1f2f3f4f),
        //     b: Fp::from(1),
        // };
        let circuit = TestCircuit::<bn256::G1Affine, 2> { 
            a: Fp::from((1 << 16) - 2),
            b: Fp::from(1),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(9, &circuit, &root)
            .unwrap();
    }
}