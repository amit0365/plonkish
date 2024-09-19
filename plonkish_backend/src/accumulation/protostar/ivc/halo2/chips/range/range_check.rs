use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::{AssignedCell, Layouter, Value};
use halo2_proofs::halo2curves::bn256::Fr as Fp;
use halo2_proofs::plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector};
use halo2_proofs::poly::Rotation;
use halo2_base::utils::{FromUniformBytes, PrimeField, BigPrimeField};
use halo2_proofs::halo2curves::ff::PrimeFieldBits;
use num_bigint::BigUint;
use std::fmt::Debug;
use std::marker::PhantomData;

use crate::accumulation::protostar::ivc::halo2::ivc_circuits::primary::NUM_RANGE_COLS;
use crate::{accumulation::protostar::ivc::halo2::ivc_circuits::primary::T, util::arithmetic::{fe_from_limbs, fe_to_limbs, into_coordinates, TwoChainCurve}};

use super::super::main_chip::{Number, LOOKUP_BITS};

/// Converts a BigUint to a Field Element
pub fn big_uint_to_fp<F: BigPrimeField>(big_uint: &BigUint) -> F {
    F::from_str_vartime(&big_uint.to_str_radix(10)[..]).unwrap()
}

/// Converts a Field element to a BigUint
pub fn fp_to_big_uint<F: BigPrimeField>(f: F) -> BigUint {
    BigUint::from_bytes_le(f.to_bytes_le().as_ref())
}

pub fn decompose_fp_to_bytes<F: BigPrimeField>(value: F, n: usize) -> Vec<u8> {
    let value_biguint = fp_to_big_uint(value);

    let mut bytes = value_biguint.to_bytes_le();

    // Pad with 0s at the most significant bytes if bytes length is less than n.
    while bytes.len() < n {
        bytes.push(0);
    }

    // If the bytes length exceeds n, print a warning and truncate the byte array at the most significant bytes.
    if bytes.len() > n {
        println!("bytes len: {}", bytes.len());
        println!("n: {}", n);
        println!("Warning: `decompose_fp_to_bytes` value is decomposed in #bytes which are greater than n. Truncating the output to fit the specified length.");
        bytes.truncate(n);
    }

    bytes
}

/// Configuration for the Range Check Chip
///
/// # Type Parameters
///
/// * `N_BYTES`: Number of bytes in which the value to be checked should lie
///
/// # Fields
///
/// * `z`: Advice column for the value to be checked and its running sum.
/// * `lookup_enable_selector`: Selector to enable the lookup check.
///
/// Patterned after [halo2_gadgets](https://github.com/privacy-scaling-explorations/halo2/blob/main/halo2_gadgets/src/utilities/decompose_running_sum.rs)
#[derive(Debug, Copy, Clone)]
pub struct RangeCheckConfig {
    z: Column<Advice>,
    lookup_enable_selector: Selector,   
    pub lookup_u8_table: Column<Fixed>,
}

/// Helper chip that verifies that the value witnessed in a given cell lies within a given range defined by N_BYTES.
/// For example, Let's say we want to constraint 0x1f2f3f4f to be within the range N_BYTES=4.
///
/// * `z(0) = 0x1f2f3f4f`
/// * `z(1) = (0x1f2f3f4f - 0x4f) / 2^LOOKUP_BITS = 0x1f2f3f`
/// * `z(2) = (0x1f2f3f - 0x3f) / 2^LOOKUP_BITS = 0x1f2f`
/// * `z(3) = (0x1f2f - 0x2f) / 2^LOOKUP_BITS = 0x1f`
/// * `z(4) = (0x1f - 0x1f) / 2^LOOKUP_BITS = 0x00`
///
/// |                | `z`          |
/// | ------------   | -------------|
///  | 0             | `0x1f2f3f4f` |
///  | 1             | `0x1f2f3f`   |
///  | 2             | `0x1f2f`     |
///  | 3             | `0x1f`       |
///  | 4             | `0x00`       |
///
/// The column z contains the witnessed value to be checked at offset 0
/// At offset i, the column z contains the value `z(i+1) = (z(i) - k(i)) / 2^LOOKUP_BITS` (shift right by LOOKUP_BITS bits) where k(i) is the i-th decomposition big-endian of `value`
/// The constraints that are enforced are:
/// * `z(i) - 2^LOOKUP_BITS⋅z(i+1) ∈ lookup_u8_table` (enabled by lookup_enable_selector at offset [0, N_BYTES - 1])
/// * `z(N_BYTES) == 0`
#[derive(Debug, Clone)]
pub struct RangeCheckChip<C> 
where
    C: TwoChainCurve,
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    config: RangeCheckConfig,
    marker: PhantomData<C>,
}

impl<C: TwoChainCurve> RangeCheckChip<C> 
where
    C::Base: BigPrimeField + PrimeFieldBits,
    C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
{
    pub type Num = Number<C::Scalar>;

    pub fn construct(config: RangeCheckConfig) -> Self {
        Self { config , marker: PhantomData }
    }

    /// Configures the Range Chip
    /// Note: the lookup table should be loaded with values from `0` to `2^LOOKUP_BITS - 1` otherwise the range check will fail.
    pub fn configure(
        meta: &mut ConstraintSystem<C::Scalar>,
        z: Column<Advice>,
        lookup_u8_table: Column<Fixed>,
        lookup_enable_selector: Selector,
    ) -> RangeCheckConfig {
        meta.annotate_lookup_any_column(lookup_u8_table, || "LOOKUP_MAXBITS_RANGE");

        meta.lookup_any(
            "range u8 check for difference between each interstitial running sum output",
            |meta| {
                let z_cur = meta.query_advice(z, Rotation::cur());
                let z_next = meta.query_advice(z, Rotation::next());

                let lookup_enable_selector = meta.query_selector(lookup_enable_selector);
                let u8_range = meta.query_fixed(lookup_u8_table, Rotation::cur());

                let diff = z_cur - z_next * Expression::Constant(C::Scalar::from(1 << LOOKUP_BITS));

                vec![(lookup_enable_selector * diff, u8_range)]
            },
        );

        RangeCheckConfig {
            z,
            lookup_enable_selector,
            lookup_u8_table,
        }
    }

    /// Assign the running sum to the chip starting from the value within an assigned cell.
    pub fn assign(
        &self,
        layouter: &mut impl Layouter<C::Scalar>,
        value: &Self::Num,
        range_bits: usize,
    ) -> Result<(), Error> {
        let N_BYTES: usize = range_bits.div_ceil(LOOKUP_BITS);
        layouter.assign_region(
            || "range check value",
            |mut region| {
                // enable the lookup at offset [0, N_BYTES - 1]
                for i in 0..N_BYTES {
                    self.config.lookup_enable_selector.enable(&mut region, i)?;
                }

                // copy `value` to `z_0` at offset 0
                let z_0 = value.0.copy_advice(
                    || "range checked value",
                    &mut region,
                    self.config.z,
                    0,
                )?;

                // Decompose the value in #N_BYTES bytes
                let bytes = value.0
                    .value()
                    .copied()
                    .map(|x| decompose_fp_to_bytes(x, N_BYTES))
                    .transpose_vec(N_BYTES);

                // Initialize empty vector to store running sum values [z_0, ..., z_W].
                let mut zs: Vec<Self::Num> = vec![Number(z_0.clone())];
                let mut z = z_0;

                // Assign running sum `z_{i+1}` = (z_i - k_i) / (2^LOOKUP_BITS) for i = 0..= N_BYTES - 1.
                let two_pow_k_inv = Value::known(C::Scalar::from(1 << LOOKUP_BITS).invert().unwrap());

                for (i, byte) in bytes.iter().enumerate() {
                    // z_next = (z_cur - byte) / (2^K)
                    let z_next = {
                        let z_cur_val = z.value().copied();
                        let byte = byte.map(|byte| C::Scalar::from(byte as u64));
                        let z_next_val = (z_cur_val - byte) * two_pow_k_inv;
                        region.assign_advice(
                            || format!("z_{:?}", i + 1),
                            self.config.z,
                            i + 1,
                            || z_next_val,
                        )?
                    };

                    // Update `z`.
                    z = z_next;
                    zs.push(Number(z.clone()));
                }

                // Constrain the final running sum output to be zero.
                region.constrain_constant(zs[N_BYTES].0.cell(), C::Scalar::from(0))?;

                Ok(())
            },
        )
    }

    /// Loads the lookup table with values from `0` to `2^LOOKUP_BITS - 1`
    pub fn load_range_check_table(&self, layouter: &mut impl Layouter<C::Scalar>, column: Column<Fixed>) -> Result<(), Error> {
        let range = 1 << LOOKUP_BITS;
    
        layouter.assign_region(
            || format!("load range check table of {} bits", LOOKUP_BITS),
            |mut region| {
                for i in 0..range {
                    region.assign_fixed(
                            || "assign cell in fixed column",
                            column,
                            i,
                            || Value::known(C::Scalar::from(i as u64)),
                        )?;
                    }
                Ok(())
            },
        )
    }
}