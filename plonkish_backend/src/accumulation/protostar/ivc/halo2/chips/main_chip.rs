use std::iter::{self, once};
use std::cmp::max;
use ark_std::One;
use halo2_base::utils::ScalarField;
use halo2_base::{halo2_proofs::{circuit::{AssignedCell, Layouter, Value}, plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector}, poly::Rotation}, utils::{bigint_to_fe, biguint_to_fe, decompose_bigint, decompose_biguint, fe_to_bigint, fe_to_biguint, modulus, BigPrimeField, FromUniformBytes}};
use halo2_base::halo2_proofs::{arithmetic::{CurveAffine, Field}, halo2curves::ff::PrimeFieldBits};
use num_bigint::{BigUint, BigInt};
use crate::{accumulation::protostar::ivc::halo2::ivc_circuits::primary::T, util::arithmetic::{fe_from_limbs, fe_to_limbs, into_coordinates, TwoChainCurve}};
use itertools::Itertools;
use num_integer::Integer;
use num_traits::sign::Signed;
use super::range_check::RangeCheckChip;

pub const LOOKUP_BITS: usize = 16;
pub const NUM_MAIN_ADVICE: usize = 7; // T + 1;
pub const NUM_MAIN_FIXED: usize = 2*T;
pub const NUM_LIMB_BITS_PRIMARY_NON_NATIVE: usize = 128;
pub const NUM_LIMBS_PRIMARY_NON_NATIVE: usize = 2;
pub const NUM_LIMB_BITS_NON_NATIVE: usize = 88;
pub const NUM_LIMBS_NON_NATIVE: usize = 3;

    #[derive(Clone, Debug)]
    pub struct Number<F: Field>(pub AssignedCell<F, F>);

    impl<F: Field> Number<F> {
        pub fn value(&self) -> F {
            let mut value = F::ZERO;
            self.0.value().map(|val| value = *val);
            value
        }
    }

    #[derive(Clone, Debug, Default)]
    pub struct ModReduceParams<F: Field> {
        pub wrong_mod: BigInt,
        pub mod_native: F,
        pub mod_limbs: Vec<F>,
        pub num_limbs: usize,
        pub num_limb_bits: usize, 
        pub limb_bases: Vec<F>,
        pub limb_base_big: BigInt,
    }

    #[derive(Clone, Debug)]
    pub struct NonNativeNumber<F: Field> {
        pub limbs: Vec<Number<F>>,
        pub native: Number<F>,
        pub value: BigInt,
        pub params: ModReduceParams<F>,
    }

    impl<F: BigPrimeField> NonNativeNumber<F> {

        pub fn new(limbs: Vec<Number<F>>, native: Number<F>, value: BigInt, wrong_mod: BigUint) -> Self {
            let num_limbs = NUM_LIMBS_PRIMARY_NON_NATIVE;
            let num_limb_bits = NUM_LIMB_BITS_PRIMARY_NON_NATIVE;
            let modulus = modulus::<F>();
            let mod_native = biguint_to_fe(&(&wrong_mod % &modulus));
            let mod_limbs = decompose_biguint(&wrong_mod, num_limbs, num_limb_bits);    
            let limb_base = biguint_to_fe::<F>(&(BigUint::one() << num_limb_bits));
            let mut limb_bases = Vec::with_capacity(num_limbs);
                limb_bases.push(F::ONE);
           
            while limb_bases.len() != num_limbs {
                limb_bases.push(limb_base * limb_bases.last().unwrap());
            }

            let params = ModReduceParams {
                wrong_mod: wrong_mod.into(),
                mod_native,
                mod_limbs,
                num_limbs,
                num_limb_bits,
                limb_bases,
                limb_base_big: BigInt::one() << num_limb_bits,
            };

            NonNativeNumber { limbs, native, value, params }

        }

        pub fn limbs(&self) -> &Vec<Number<F>> {
            &self.limbs
        }

        pub fn native(&self) -> &Number<F> {
            &self.native
        }

    }

    #[derive(Clone, Debug)]
    pub struct EcPointNonNative<C: CurveAffine> {
        pub(crate) x: NonNativeNumber<C::Scalar>,
        pub(crate) y: NonNativeNumber<C::Scalar>,
    }

    impl<C: TwoChainCurve> EcPointNonNative<C> 
        where
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {
        pub fn coordinate_vec(&self) -> Vec<Number<C::Scalar>> {
            self.x.limbs().clone().into_iter().chain(self.y.limbs().clone()).collect_vec()
        }

        // pub fn native(&self) -> &Number<F> {
        //     &self.native
        // }

        // pub fn new(limbs: Vec<Number<F>>, native: Number<F>) -> Self {
        //     NonNativeNumber { limbs, native }
        // }
    }

    #[derive(Clone, Debug)]
    pub struct EcPointNative<C: CurveAffine> {
        pub(crate) x: Number<C::Scalar>,
        pub(crate) y: Number<C::Scalar>,
    }

    impl<C: TwoChainCurve> EcPointNative<C> 
        where
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {
        pub fn coordinate_vec_native(&self) -> Vec<Number<C::Scalar>> {
            vec![self.x.clone(), self.y.clone()]
        }

        pub fn new(x: Number<C::Scalar>, y: Number<C::Scalar>) -> Self {
            EcPointNative { x, y }
        }
    }

    #[derive(Clone, Debug)]
    pub struct MainChipConfig {
        advice: [Column<Advice>; NUM_MAIN_ADVICE],
        fixed: [Column<Fixed>; NUM_MAIN_FIXED],
        selector: [Selector; 2],
    }

    #[derive(Clone, Debug)]
    pub struct MainChip<C: TwoChainCurve> 
        where
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {
        pub config: MainChipConfig,
        pow_of_two: Vec<C::Scalar>,
        range_check_chip: RangeCheckChip<C>,
    }

    impl<C: TwoChainCurve> MainChip<C> 
        where
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {
        pub type Num = Number<C::Scalar>;
        pub type NonNatNum = NonNativeNumber<C::Scalar>;
        pub type Ecc = EcPointNonNative<C>;
        pub type NatEcc = EcPointNative<C>;

        /// Returns a new [GateChip] with the given [GateStrategy].
        pub fn new(config: MainChipConfig, range_check_chip: RangeCheckChip<C>) -> Self {
            let mut pow_of_two = Vec::with_capacity(C::Scalar::NUM_BITS as usize);
            let two = C::Scalar::from(2);
            pow_of_two.push(C::Scalar::ONE);
            pow_of_two.push(two);
            for _ in 2..C::Scalar::NUM_BITS {
                pow_of_two.push(two * pow_of_two.last().unwrap());
            }
            Self { config, pow_of_two, range_check_chip }
        }
    
        pub fn configure(
            meta: &mut ConstraintSystem<C::Scalar>,
            advice: [Column<Advice>; NUM_MAIN_ADVICE],
            fixed: [Column<Fixed>; NUM_MAIN_FIXED],
        ) -> MainChipConfig {

            let [mul_add, inner_product] = [(); 2].map(|_| meta.selector());

            meta.create_gate("mul add constraint", |meta| {
                let s = meta.query_selector(mul_add);
                let a = meta.query_advice(advice[0], Rotation::cur());
                let b = meta.query_advice(advice[1], Rotation::cur());
                let c = meta.query_advice(advice[2], Rotation::cur());
                let out = meta.query_advice(advice[3], Rotation::cur());
                vec![s * (a * b + c - out)]
            });

            meta.create_gate("inner product constraint", |meta| {
                let s = meta.query_selector(inner_product);
                let a = meta.query_advice(advice[0], Rotation::cur());
                let b = meta.query_advice(advice[1], Rotation::cur());
                let acc = meta.query_advice(advice[2], Rotation::cur());
                let acc_next = meta.query_advice(advice[3], Rotation::cur());    
                vec![s * (a * b + acc - acc_next)]
            });
            
            MainChipConfig {
                advice,
                fixed,
                selector: [mul_add, inner_product],
            }
        }

        pub fn assign_witness(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            witness: &C::Scalar,
            witness_index: usize,
        ) -> Result<Self::Num, Error> {
            let config = self.config.clone();
            let idx = witness_index % NUM_MAIN_ADVICE;
            let witness = layouter.assign_region(
                || "assign witness",
                |mut region| {
                    let witness = region.assign_advice(
                            || "witness",
                            config.advice[idx],
                            0,
                            || Value::known(*witness),
                        ).map(Number)?;
                    Ok(witness)
                },
            )?;
            Ok(witness)
        }

        pub fn assign_witnesses(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            witnesses: &[C::Scalar],
        ) -> Result<Vec<Self::Num>, Error> {
            let witnesses = witnesses.iter().enumerate().map(|(idx, witness)| self.assign_witness(layouter.namespace(|| "assign_witness"), witness, idx).unwrap()).collect_vec();
            Ok(witnesses)
        }

        pub fn from_limbs(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            limbs: Vec<Self::Num>,
            result_value: BigInt,
        ) -> Result<Self::NonNatNum, Error> {
            let num_limbs = NUM_LIMBS_PRIMARY_NON_NATIVE;
            let limb_bits = NUM_LIMB_BITS_PRIMARY_NON_NATIVE;
                
            let limb_base = biguint_to_fe::<C::Scalar>(&(BigUint::one() << limb_bits));
            let mut limb_bases = Vec::with_capacity(num_limbs);
                limb_bases.push(C::Scalar::ONE);
           
            while limb_bases.len() != num_limbs {
                limb_bases.push(limb_base * limb_bases.last().unwrap());
            }
            let limb_bases_assigned = self.assign_witnesses(layouter.namespace(|| "assign_non_native_limb_bases"), &limb_bases)?;
    
            let a_computed_native = self.inner_product(layouter.namespace(|| "inner_product"), &limbs, &limb_bases_assigned)?;
            Ok(NonNativeNumber::new(limbs, a_computed_native, result_value, modulus::<C::Base>()))
        }

        pub fn assign_witness_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: C::Base,
        ) -> Result<Self::NonNatNum, Error> {

            // move this into nonnative number impl
            let native_modulus = modulus::<C::Scalar>();
            let a = fe_to_biguint(&a);
            let a_native = biguint_to_fe(&(&a % &native_modulus)); 
            let a_native_assigned = self.assign_witness(layouter.namespace(|| "assign_non_native_a"), &a_native, 0)?;

            let num_limbs = NUM_LIMBS_PRIMARY_NON_NATIVE;
            let limb_bits = NUM_LIMB_BITS_PRIMARY_NON_NATIVE;
            let a_vec = decompose_biguint::<C::Scalar>(&a, num_limbs, limb_bits);
            let limbs = self.assign_witnesses(layouter.namespace(|| "assign_non_native_limbs"), &a_vec)?;
    
            let limb_base = biguint_to_fe::<C::Scalar>(&(BigUint::one() << limb_bits));
            let mut limb_bases = Vec::with_capacity(num_limbs);
            limb_bases.push(C::Scalar::ONE);
            while limb_bases.len() != num_limbs {
                limb_bases.push(limb_base * limb_bases.last().unwrap());
            }
            let limb_bases_assigned = self.assign_witnesses(layouter.namespace(|| "assign_non_native_limb_bases"), &limb_bases)?;

            let a_computed_native = self.inner_product(layouter.namespace(|| "inner_product"), &limbs, &limb_bases_assigned)?;
            // self.constrain_equal(layouter, &a_computed_native, &a_native_assigned)?;
    
            self.range_check_chip.assign(layouter.namespace(|| "range check"), &a_computed_native, C::Scalar::NUM_BITS as usize)?;
            Ok(NonNativeNumber::new(limbs, a_native_assigned, a.into(), modulus::<C::Base>()))

        }

        pub fn assign_witness_primary(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            witness: C,
        ) -> Result<Self::Ecc, Error> {
            let coords = into_coordinates(&witness);
            let x = self.assign_witness_base(layouter.namespace(|| "assign_witness_primary_x"), coords[0])?;
            let y = self.assign_witness_base(layouter.namespace(|| "assign_witness_primary_y"), coords[1])?;
            Ok(EcPointNonNative { x, y })
        }

        pub fn assign_witness_secondary(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            witness: C::Secondary,
        ) -> Result<Self::NatEcc, Error> {
            let coords = into_coordinates(&witness);
            let x = self.assign_witness(layouter.namespace(|| "assign_witness_secondary_x"), &coords[0], 0)?;
            let y = self.assign_witness(layouter.namespace(|| "assign_witness_secondary_y"), &coords[1], 1)?;
            Ok(EcPointNative { x, y })
        }
            
        pub fn assign_fixed(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            fixed: &C::Scalar,
            index: usize,
        ) -> Result<Self::Num, Error> {
            let config = &self.config;
            let idx = index % NUM_MAIN_ADVICE;
            let fixed = layouter.assign_region(
                || "assign fixed",
                |mut region| {
                    let fixed = region.assign_advice_from_constant(|| "fixed value",
                    config.advice[idx],
                    0, 
                    *fixed
                    ).map(Number)?;
                    Ok(fixed)
                },
            )?;
            Ok(fixed)
        }

        pub fn assign_fixed_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            fixed: &C::Base,
        ) -> Result<Self::NonNatNum, Error> {
            let config = &self.config;
            let num_limbs = NUM_LIMBS_NON_NATIVE;
            let limb_bits = NUM_LIMB_BITS_NON_NATIVE;

            let native_modulus = modulus::<C::Scalar>();
            let a = fe_to_biguint(fixed);
            let a_native = biguint_to_fe(&(&a % &native_modulus)); 
            let a_native_assigned = self.assign_witness(layouter.namespace(|| "assign_non_native_a"), &a_native, 0)?;
            let a_vec = decompose_biguint::<C::Scalar>(&a, num_limbs, limb_bits);
            
            let fixed = a_vec.iter().enumerate().map(|(idx, fixed)|
                layouter.assign_region(
                || "assign fixed",
                |mut region| {
                    let fixed = region.assign_advice_from_constant(|| "fixed value",
                    config.advice[idx],
                    0, 
                    *fixed
                    ).map(Number)?;
                    Ok(fixed)
                }
            )
        ).collect::<Result<Vec<_>, _>>()?;
            Ok(NonNativeNumber::new(fixed, a_native_assigned, a.into(), modulus::<C::Base>()))
        }

        pub fn assign_constant_primary(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            witness: C,
        ) -> Result<Self::Ecc, Error> {
            let coords = into_coordinates(&witness);
            let x = self.assign_witness_base(layouter.namespace(|| "assign_witness_primary_x"), coords[0])?;
            let y = self.assign_witness_base(layouter.namespace(|| "assign_witness_primary_y"), coords[1])?;
            Ok(EcPointNonNative { x, y })
        }

        pub fn assign_constant_secondary(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            witness: C::Secondary,
        ) -> Result<Self::NatEcc, Error> {
            let coords = into_coordinates(&witness);
            let x = self.assign_witness(layouter.namespace(|| "assign_witness_primary_x"), &coords[0], 0)?;
            let y = self.assign_witness(layouter.namespace(|| "assign_witness_primary_y"), &coords[1], 1)?;
            Ok(EcPointNative { x, y })
        }

        pub fn select(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            is_base_case: &Self::Num,
            a: &Self::Num,
            b: &Self::Num,
        )-> Result<Self::Num, Error>{
            // | sel | a - b | b | out |
            let diff = self.sub(layouter.namespace(|| "select_diff"), a, b)?;
            self.mul_add(layouter.namespace(|| "select_out"), b, &diff, is_base_case)
        }

        pub fn select_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            is_base_case: &Self::Num,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        )-> Result<Self::NonNatNum, Error>{
            // | sel | a - b | b | out |
            let diff = self.sub_base(layouter.namespace(|| "select_diff"), a, b)?;
            self.mul_native_add_base(layouter.namespace(|| "select_out"), is_base_case, &diff , b)
        }

        pub fn select_primary(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            is_base_case: &Self::Num,
            a: &Self::Ecc,
            b: &Self::Ecc,
        )-> Result<Self::Ecc, Error>{    
            let x = self.select_base(layouter.namespace(|| "select_primary_x"), is_base_case, &a.x, &b.x)?;
            let y = self.select_base(layouter.namespace(|| "select_primary_y"), is_base_case, &a.y, &b.y)?;
            Ok(EcPointNonNative { x, y })
        }

        pub fn select_secondary(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            is_base_case: &Self::Num,
            a: &Self::NatEcc,
            b: &Self::NatEcc,
        )-> Result<Self::NatEcc, Error>{    
            let x = self.select(layouter.namespace(|| "select_primary_x"), is_base_case, &a.x, &b.x)?;
            let y = self.select(layouter.namespace(|| "select_primary_y"), is_base_case, &a.y, &b.y)?;
            Ok(EcPointNative { x, y })
        }

        pub fn is_zero(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::Num,
        )-> Result<Self::Num, Error>{

            let mut val = C::Scalar::ZERO;
            a.0.value().map(|v| val = *v);

            let zero = self.assign_fixed(layouter.namespace(|| "assign_zero"), &C::Scalar::ZERO, 0)?;
            let a_inv = if val.is_zero().into() { C::Scalar::ONE } else { C::Scalar::ZERO };
            let a_inv_assigned = self.assign_witness(layouter.namespace(|| "assign_a_inv"), &a_inv, 1)?;

            let out = self.mul(layouter.namespace(|| "out_is_zero"), a, &a_inv_assigned)?;
            let out_constraint = self.mul(layouter.namespace(|| "out_constraint"), a, &out)?;
            self.constrain_equal(layouter, &out_constraint, &zero)?;
            Ok(out)
        }

        pub fn is_equal(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            lhs: &Self::Num,
            rhs: &Self::Num,
        )-> Result<Self::Num, Error>{
            let diff = self.sub(layouter.namespace(|| "is_equal_diff"), lhs, rhs)?;
            let is_zero = self.is_zero(layouter.namespace(|| "is_equal_is_zero"), &diff)?;
            Ok(is_zero)
        }

        pub fn constrain_equal(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "constrain equal",
                |mut region| {
                    region.constrain_equal(a.0.cell(), b.0.cell())?;
                    Ok(())
                }
            )?;
            Ok(())
        }

        pub fn constrain_equal_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        ) -> Result<(), Error> {
            a.limbs.clone().into_iter().zip(b.limbs.clone()).map(|(a, b)| {
                layouter.assign_region(
                    || "constrain equal",
                    |mut region| {
                        region.constrain_equal(a.0.cell(), b.0.cell())?;
                        Ok(())
                    }
                )
            }).collect_vec();
            Ok(())
        }

        pub fn constrain_equal_primary(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::Ecc,
            b: &Self::Ecc,
        ) -> Result<(), Error> {
            a.coordinate_vec().into_iter().zip(b.coordinate_vec()).map(|(a, b)| {
                layouter.assign_region(
                    || "constrain equal",
                    |mut region| {
                        region.constrain_equal(a.0.cell(), b.0.cell())?;
                        Ok(())
                    }
                )
            }).collect_vec();
            Ok(())
        }

        pub fn constrain_equal_secondary(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::NatEcc,
            b: &Self::NatEcc,
        ) -> Result<(), Error> {
            a.coordinate_vec_native().into_iter().zip(b.coordinate_vec_native()).map(|(a, b)| {
                layouter.assign_region(
                    || "constrain equal",
                    |mut region| {
                        region.constrain_equal(a.0.cell(), b.0.cell())?;
                        Ok(())
                    }
                )
            }).collect_vec();
            Ok(())
        }

        pub fn inner_product(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &[Self::Num],
            b: &[Self::Num],
        ) -> Result<Self::Num, Error> {

            let zero = self.assign_witness(layouter.namespace(|| "assign_zero"), &C::Scalar::ZERO, 0)?;
            let mut accumulator = C::Scalar::ZERO;
            let mut product = Vec::new();
            let acc = a.iter()
                .zip(b.iter())
                .map(|(a, b)| {
                    accumulator += a.value() * b.value();
                    Value::known(accumulator)
                })
                .collect_vec();

            layouter.assign_region(
                || "inner product",
                |mut region | {
                let _ = a.iter()
                        .zip(b.iter())
                        .enumerate()
                        .map(|(i, (a, b))| {

                            self.config.selector[1].enable(&mut region, i)?;

                            a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], i)?;
                            b.0.copy_advice(|| "rhs", &mut region, self.config.advice[1], i)?;
                            zero.0.copy_advice(|| "zero", &mut region, self.config.advice[2], i)?;

                            let value = a.0.value().copied() * b.0.value() + acc[i];
                            let result = region
                                .assign_advice(|| "lhs * rhs + acc",
                                self.config.advice[3], i, || value)?;

                            product.push(result);
                            Ok::<(), Error>(())
                        });
                    Ok(())              
                },
            )?;
            // todo change this
            if product.is_empty() {
                Ok(zero.clone())
            } else {
                Ok(Number(product.last().unwrap().clone()))
            }  

        }

        pub fn inner_product_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &[Self::NonNatNum],
            b: &[Self::NonNatNum],
        ) -> Result<Self::NonNatNum, Error> {
            let num_limbs = a[0].limbs.len();
            let zero_native = self.assign_fixed(layouter.namespace(|| "assign_zero_native"), &C::Scalar::ZERO, 0)?;
            let zero = self.assign_fixed_base(layouter.namespace(|| "inner_product_base_0"), &C::Base::ZERO)?;

            let inner_product_value = 
                a.iter().zip(b.iter()).fold(
                    BigInt::from(0),
                    |acc, (a, b)| {
                        acc + a.value.clone() * b.value.clone()
                });

            let mut accumulator = C::Scalar::ZERO;
            let mut product = Vec::new();
            let acc = a.iter()
                .zip(b.iter())
                .map(|(a, b)| {
                    a.limbs.iter().zip(b.limbs.iter()).map(|(a, b)| {
                        accumulator += a.value() * b.value();
                        Value::known(accumulator)
                    }).collect_vec()
                }).collect_vec();

            layouter.assign_region(
                || "inner product",
                |mut region | {
                    a.iter()
                        .zip(b.iter())
                        .enumerate()
                        .map(|(i, (a, b))| {
                            a.limbs.iter()
                            .zip(b.limbs.iter())
                            .enumerate()
                            .map(|(j, (a, b))| {
                                let offset = i * num_limbs + j;
                                self.config.selector[1].enable(&mut region, offset)?;

                                a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], offset)?;
                                b.0.copy_advice(|| "rhs", &mut region, self.config.advice[1], offset)?;
                                zero_native.0.copy_advice(|| "zero_native", &mut region, self.config.advice[2], offset)?;

                                let value = a.0.value().copied() * b.0.value().copied() + acc[i][j];
                                let result = region
                                    .assign_advice(|| "lhs * rhs + acc",
                                    self.config.advice[3], offset, || value);

                                product.push(Number(result?));
                                Ok(())

                            }).collect::<Result<Vec<_>, _>>()          
                }).collect::<Result<Vec<_>, _>>()
            })?;
            
            // todo change this
            if product.is_empty() {
                Ok(zero.clone())
            } else {
                self.from_limbs(layouter.namespace(|| "from_limbs"), product.iter().rev().take(num_limbs).cloned().collect_vec(), inner_product_value)
            }  

        }

        /// Constrains and returns little-endian bit vector representation of `a`.
        ///
        /// Assumes `range_bits >= number of bits in a`.
        /// * `a`: [QuantumCell] of the value to convert
        /// * `range_bits`: range of bits needed to represent `a`. Assumes `range_bits > 0`.
        pub fn num_to_bits(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            range_bits: usize,
            num: &Self::Num,
        ) -> Result<Vec<Self::Num>, Error> {
            let mut number = C::Scalar::ZERO;
            num.0.value().map(|v| number = *v);
            let bits = number.to_u64_limbs(range_bits, 1)
                .into_iter()
                .enumerate()    
                .map(|(idx, x)| self.assign_witness(layouter.namespace(|| "assign_witness"), &C::Scalar::from(x), idx).unwrap())
                .collect_vec();
            //range check bits
            let pow_two_assigned = self.pow_of_two[..bits.len()]
                .iter()
                .enumerate()
                .map(|(idx, c)| self.assign_fixed(layouter.namespace(|| "bits_to_num_assign"), c, idx).unwrap())
                .collect_vec();

            let acc = self.inner_product(
                layouter.namespace(|| "inner_product"),
                &bits,
                &pow_two_assigned,
            )?; 
            //self.constrain_equal(layouter, num, &acc)?;
            debug_assert!(range_bits > 0);
            Ok(bits)
        }

        /// Constrains and returns field representation of little-endian bit vector `bits`.
        ///
        /// Assumes values of `bits` are boolean.
        /// * `bits`: slice of [QuantumCell]'s that contains bit representation in little-endian form
        pub fn bits_to_num(&self, mut layouter: impl Layouter<C::Scalar>, bits: &[Self::Num]) -> Result<Self::Num, Error> {
            assert!((bits.len() as u32) <= C::Scalar::CAPACITY);
            let pow_two_assigned = self.pow_of_two[..bits.len()].iter().enumerate().map(|(idx, c)| self.assign_fixed(layouter.namespace(|| "bits_to_num_assign"), c, idx).unwrap()).collect_vec();
            self.inner_product(
                layouter.namespace(|| "bits_to_num_inner_product"),
                bits,
                &pow_two_assigned,
            )
        }    
        
        pub fn add(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
        ) -> Result<Self::Num, Error> {
            // | a | 1 | b | a + b |
            let one = self.assign_fixed(layouter.namespace(|| "assign_one"), &C::Scalar::ONE, 0)?;
            let result = layouter.namespace(|| "add").assign_region(
                || "add",
                |mut region | {
                            self.config.selector[0].enable(&mut region, 0)?;
                            a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], 0)?;
                            one.0.copy_advice(|| "one", &mut region, self.config.advice[1], 0)?;
                            b.0.copy_advice(|| "rhs", &mut region, self.config.advice[2], 0)?;
    
                            let value = a.0.value().copied() + b.0.value();
                            region.assign_advice(
                                || "lhs + rhs",
                                self.config.advice[3], 0, || value
                            )
                        })?;

            Ok(Number(result))
        }

        pub fn add_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        ) -> Result<Self::NonNatNum, Error> {
            // | a | 1 | b | a + b |
            let one = self.assign_fixed(layouter.namespace(|| "assign_one"), &C::Scalar::ONE, 0)?;
            let result = a.limbs.iter().zip(b.limbs.iter()).map(|(a, b)| {
                layouter.namespace(|| "add_base").assign_region(
                    || "add_base",
                |mut region | {
                            self.config.selector[0].enable(&mut region, 0)?;
                            a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], 0)?;
                            one.0.copy_advice(|| "one", &mut region, self.config.advice[1], 0)?;
                            b.0.copy_advice(|| "rhs", &mut region, self.config.advice[2], 0)?;
    
                            let value = a.0.value().copied() + b.0.value();
                            let result = region.assign_advice(
                                || "lhs + rhs",
                                self.config.advice[3], 0, || value
                            )?;

                                Ok(Number(result))
                            })
                }).collect::<Result<Vec<_>, _>>()?;
            
            let result_value = a.value.clone() + b.value.clone();
            self.from_limbs(layouter.namespace(|| "from_limbs"), result, result_value)
        }

        pub fn sub(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
        ) -> Result<Self::Num, Error> {
            // | a - b | 1 | b | a |
            let one = self.assign_fixed(layouter.namespace(|| "assign_one"), &C::Scalar::ONE, 0)?;
            let result = layouter.namespace(|| "sub").assign_region(
                || "sub",
                |mut region | {
                            self.config.selector[0].enable(&mut region, 0)?;

                            let diff_value = a.0.value().copied() - b.0.value();
                            let diff = region.assign_advice(
                                || "lhs - rhs",
                                self.config.advice[0], 0, || diff_value
                            );

                            one.0.copy_advice(|| "one", &mut region, self.config.advice[1], 0)?;
                            b.0.copy_advice(|| "rhs", &mut region, self.config.advice[2], 0)?;
                            a.0.copy_advice(|| "rhs", &mut region, self.config.advice[3], 0)?;
                            diff

                        })?;

            Ok(Number(result))
        }

        pub fn sub_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        ) -> Result<Self::NonNatNum, Error> {
            // | a - b | 1 | b | a |
            let one = self.assign_fixed(layouter.namespace(|| "assign_one"), &C::Scalar::ONE, 0)?;
            let result = a.limbs.iter().zip(b.limbs.iter()).map(|(a, b)| {
                layouter.namespace(|| "sub_base").assign_region(
                    || "sub_base",
                    |mut region | {
                                self.config.selector[0].enable(&mut region, 0)?;

                                let diff_value = a.0.value().copied() - b.0.value();
                                let diff = region.assign_advice(
                                    || "lhs - rhs",
                                    self.config.advice[0], 0, || diff_value
                                )?;

                                one.0.copy_advice(|| "one", &mut region, self.config.advice[1], 0)?;
                                b.0.copy_advice(|| "rhs", &mut region, self.config.advice[2], 0)?;
                                a.0.copy_advice(|| "rhs", &mut region, self.config.advice[3], 0)?;
                                
                                Ok(Number(diff))
                            })
                }).collect::<Result<Vec<_>, _>>()?;
            
            let result_value = a.value.clone() - b.value.clone();
            self.from_limbs(layouter.namespace(|| "from_limbs"), result, result_value)
        }

        pub fn mul(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
        ) -> Result<Self::Num, Error> {
            // | a | b | 0 | a * b |
            let zero = self.assign_witness(layouter.namespace(|| "assign_zero"), &C::Scalar::ZERO, 0)?;                           
            let result = layouter.namespace(|| "mul").assign_region(
                || "mul",
                |mut region | {

                            self.config.selector[0].enable(&mut region, 0)?; 
                            a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], 0)?;
                            b.0.copy_advice(|| "rhs", &mut region, self.config.advice[1], 0)?;
                            zero.0.copy_advice(|| "zero", &mut region, self.config.advice[2], 0)?;

                            let value = a.0.value().copied() * b.0.value();
                            region.assign_advice(
                                || "lhs * rhs + 0",
                                self.config.advice[3], 0, || value
                            )
                        })?;

            Ok(Number(result))
        }

        pub fn mul_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        ) -> Result<Self::NonNatNum, Error> {
            // | a | b | 0 | a * b |
            let zero = self.assign_witness(layouter.namespace(|| "assign_zero"), &C::Scalar::ZERO, 0)?;                           
            let result = a.limbs.iter().zip(b.limbs.iter()).map(|(a, b)| {
                layouter.assign_region(
                || "mul",
                |mut region | {

                            self.config.selector[0].enable(&mut region, 0)?;                            
                            a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], 0)?;
                            b.0.copy_advice(|| "rhs", &mut region, self.config.advice[1], 0)?;
                            zero.0.copy_advice(|| "zero", &mut region, self.config.advice[2], 0)?;

                            let value = a.0.value().copied() * b.0.value();
                            let result = region.assign_advice(
                                || "lhs * rhs",
                                self.config.advice[3], 0, || value
                            )?;
                            Ok(Number(result))
                        })
            }).collect::<Result<Vec<_>, _>>()?;
            
            let result_value = a.value.clone() * b.value.clone();
            self.from_limbs(layouter.namespace(|| "from_limbs"), result, result_value)
        }

        pub fn mul_add(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
            c: &Self::Num,
        ) -> Result<Self::Num, Error> {
            // | a | b | c | a * b + c |
            let result = layouter.namespace(|| "mul_add").assign_region(
                || "inner product",
                |mut region | {

                            self.config.selector[0].enable(&mut region, 0)?; 
                            a.0.copy_advice(|| "a", &mut region, self.config.advice[0], 0)?;
                            b.0.copy_advice(|| "b", &mut region, self.config.advice[1], 0)?;
                            c.0.copy_advice(|| "c", &mut region, self.config.advice[2], 0)?;

                            let value = a.0.value().copied() * b.0.value() + c.0.value();
                            region.assign_advice(
                                || "a * b + c",
                                self.config.advice[3], 0, || value
                            )
                        })?;

            Ok(Number(result))
        }

        pub fn mul_native_add_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            num: &Self::Num,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        ) -> Result<Self::NonNatNum, Error> {
            let result = a.limbs.iter().zip(b.limbs.iter()).map(|(a, b)| {
                layouter.namespace(|| "mul_add").assign_region(
                    || "inner product",
                |mut region | {

                            self.config.selector[0].enable(&mut region, 0)?; 
                            num.0.copy_advice(|| "num", &mut region, self.config.advice[0], 0)?;
                            a.0.copy_advice(|| "a", &mut region, self.config.advice[1], 0)?;
                            b.0.copy_advice(|| "b", &mut region, self.config.advice[2], 0)?;

                            let value = num.0.value().copied() * a.0.value() + b.0.value();
                            let out = region.assign_advice(
                                || "num * a + b",
                                self.config.advice[3], 0, || value
                            )?;
                            Ok(Number(out))
                        })
            }).collect::<Result<Vec<_>, _>>()?;

            let mut num_val = C::Scalar::ZERO;
            num.0.value().map(|v| num_val = *v);
            let result_value = a.value.clone() * fe_to_bigint(&num_val) + b.value.clone();
            self.from_limbs(layouter.namespace(|| "from_limbs"), result, result_value)
        }

        pub fn mul_add_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
            c: &Self::NonNatNum,
        ) -> Result<Self::NonNatNum, Error> {
            let zero = self.assign_witness(layouter.namespace(|| "assign_zero"), &C::Scalar::ZERO, 0)?;                           
            let result = a.limbs.iter().zip_eq(b.limbs.iter()).zip_eq(c.limbs.iter()).map(|((a, b), c)| {
                layouter.namespace(|| "mul_add").assign_region(
                    || "inner product",
                |mut region | {

                            self.config.selector[0].enable(&mut region, 0)?; 
                            a.0.copy_advice(|| "a", &mut region, self.config.advice[0], 0)?;
                            b.0.copy_advice(|| "b", &mut region, self.config.advice[1], 0)?;
                            c.0.copy_advice(|| "c", &mut region, self.config.advice[2], 0)?;

                            let value = a.0.value().copied() * b.0.value() + c.0.value();
                            let out = region.assign_advice(
                                || "a * b + c",
                                self.config.advice[3], 0, || value
                            )?;
                            Ok(Number(out))
                        })
            }).collect::<Result<Vec<_>, _>>()?;
            
            let result_value = a.value.clone() * b.value.clone() + c.value.clone();
            self.from_limbs(layouter.namespace(|| "from_limbs"), result, result_value)
        }

        pub fn powers(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            num: &Self::Num,
            n: usize,
        ) -> Result<Vec<Self::Num>, Error> {
            Ok(match n {
                0 => Vec::new(),
                1 => vec![self.assign_fixed(layouter.namespace(|| "assign_fixed"), &C::Scalar::ONE, 0)?],
                2 => vec![
                    self.assign_fixed(layouter.namespace(|| "assign_fixed"), &C::Scalar::ONE, 0)?,
                    num.clone(),
                ],
                _ => {
                    let mut powers = Vec::with_capacity(n);
                    powers.push(self.assign_fixed(layouter.namespace(|| "assign_fixed"), &C::Scalar::ONE, 0)?);
                    powers.push(num.clone());
                    for _ in 0..n - 2 {
                        powers.push(self.mul(layouter.namespace(|| "mul"), powers.last().unwrap(), num)?);
                    }
                    powers
                }
            })
        }

        pub fn powers_base(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            num: &Self::NonNatNum,
            n: usize,
        ) -> Result<Vec<Self::NonNatNum>, Error> {
            Ok(match n {
                0 => Vec::new(),
                1 => vec![self.assign_fixed_base(layouter.namespace(|| "powers_base_1"), &C::Base::ONE)?],
                2 => vec![
                    self.assign_fixed_base(layouter.namespace(|| "powers_base_2"), &C::Base::ONE)?,
                    num.clone(),
                ],
                _ => {
                    let mut powers = Vec::with_capacity(n);
                    powers.push(self.assign_fixed_base(layouter.namespace(|| "powers_base_1"), &C::Base::ONE)?);
                    powers.push(num.clone());
                    for _ in 0..n - 2 {
                        powers.push(self.mul_base(layouter.namespace(|| "mul"), powers.last().unwrap(), num)?);
                    }
                    powers
                }
            })
        }

    // check that `a` carries to `0 mod 2^{a.limb_bits * a.limbs.len()}`
    // same as `assign` above except we need to provide `c_{k - 1}` witness as well
    // checks there exist d_i = -c_i so that
    // a_0 = c_0 * 2^n
    // a_i + c_{i - 1} = c_i * 2^n for i = 1..=k - 1
    // and c_i \in [-2^{m - n + EPSILON}, 2^{m - n + EPSILON}], with EPSILON >= 1 for i = 0..=k-1
    // where m = a.max_limb_size.bits() and we choose EPSILON to round up to the next multiple of the range check table size
    //
    // translated to d_i, this becomes:
    // a_0 + d_0 * 2^n = 0
    // a_i + d_i * 2^n = d_{i - 1} for i = 1.. k - 1

    // aztec optimization:
    // note that a_i + c_{i - 1} = c_i * 2^n can be expanded to
    // a_i * 2^{n*w} + a_{i - 1} * 2^{n*(w-1)} + ... + a_{i - w} + c_{i - w - 1} = c_i * 2^{n*(w+1)}
    // which is valid as long as `(m - n + EPSILON) + n * (w+1) < native_modulus::<F>().bits() - 1`
    // so we only need to range check `c_i` every `w + 1` steps, starting with `i = w`
    pub fn truncate(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        a: Vec<Self::Num>,
        limb_bits: usize,
        limb_base_assigned: &Self::Num,
        limb_base_big: &BigInt,
        max_limb_bits: usize,
    ) -> Result<(), Error> {

        let k = a.len();
        let mut carries = Vec::with_capacity(k);

        for a_limb in a.iter() {
            let a_val_big = fe_to_bigint(&a_limb.value());
            let carry = if let Some(carry_val) = carries.last() {
                (a_val_big + carry_val) / limb_base_big
            } else {
                // warning: using >> on negative integer produces undesired effect
                a_val_big / limb_base_big
            };
            carries.push(carry);
        }

        // round `max_limb_bits - limb_bits + EPSILON + 1` up to the next multiple of range.lookup_bits
        const EPSILON: usize = 1;
        let range_bits = max_limb_bits - limb_bits + EPSILON;
        let lookup_bits = LOOKUP_BITS;
        let range_bits =
            ((range_bits + lookup_bits) / lookup_bits) * lookup_bits - 1;

        // `window = w + 1` valid as long as `range_bits + n * (w+1) < native_modulus::<F>().bits() - 1`
        // let window = (F::NUM_BITS as usize - 2 - range_bits) / limb_bits;
        // assert!(window > 0);
        // In practice, we are currently always using window = 1 so the above is commented out

        let shift_val = self.pow_of_two[range_bits];
        // let num_windows = (k - 1) / window + 1; // = ((k - 1) - (window - 1) + window - 1) / window + 1;
        let zero = self.assign_fixed(layouter.namespace(|| "assign_fixed"), &C::Scalar::ZERO, 0)?;
        let mut previous = None;
        for (a_limb, carry) in a.into_iter().zip(carries) {
            let neg_carry_val = bigint_to_fe(&-carry);
            let neg_carry_assigned = self.assign_fixed(layouter.namespace(|| "assign_fixed"), &neg_carry_val, 0)?;
            let previous_assigned = self.mul_add(layouter.namespace(|| "mul_add"), limb_base_assigned, &neg_carry_assigned, &a_limb)?;
            self.constrain_equal(layouter.namespace(|| "constrain_equal"), &previous_assigned, previous.as_ref().unwrap_or(&zero))?;

            // i in 0..num_windows {
            // let idx = std::cmp::min(window * i + window - 1, k - 1);
            // let carry_cell = &neg_carry_assignments[idx];
            let shift_val_assigned = self.assign_fixed(layouter.namespace(|| "assign_fixed"), &shift_val, 0)?;
            let shifted_carry = self.add(layouter.namespace(|| "add"), &neg_carry_assigned, &shift_val_assigned)?;
            self.range_check_chip.assign(layouter.namespace(|| "range_check"), &shifted_carry, range_bits + 1)?;

            previous = Some(neg_carry_assigned);
        }

        Ok(())
    }

    // Input `a` is `CRTInteger` with `a.truncation` of length `k` with "signed" limbs
    // Output is `out = a (mod modulus)` as CRTInteger with
    // `out.value = a.value (mod modulus)`
    // `out.trunction = (a (mod modulus)) % 2^t` a proper BigInt of length `k` with limbs in [0, 2^limb_bits)`
    // The witness for `out.truncation` is a BigInt in [0, modulus), but we do not constrain the inequality
    // `out.native = (a (mod modulus)) % (native_modulus::<F>)`
    // We constrain `a = out + modulus * quotient` and range check `out` and `quotient`
    //
    // Assumption: the leading two bits (in big endian) are 1,
    /// # Assumptions
    /// * abs(a) <= 2<sup>n * k - 1 + F::NUM_BITS - 2</sup> (A weaker assumption is also enough, but this is good enough for forseeable use cases)
    /// * `native_modulus::<F>` requires *exactly* `k = a.limbs.len()` limbs to represent

    // This is currently optimized for limbs greater than 64 bits, so we need `F` to be a `BigPrimeField`
    // In the future we'll need a slightly different implementation for limbs that fit in 32 or 64 bits (e.g., `F` is Goldilocks)
    pub fn mod_reduce(
        &self,
        mut layouter: impl Layouter<C::Scalar>,
        a: Self::NonNatNum,
    ) -> Result<Self::NonNatNum, Error> {

        let ModReduceParams {
            wrong_mod,
            mod_native,
            mod_limbs,
            num_limbs,
            num_limb_bits, 
            limb_bases,
            limb_base_big,
        } = a.params;

        let n = num_limb_bits;
        let k = a.limbs.len();
        let trunc_len = n * k;

        debug_assert!(a.value.bits() as usize <= n * k - 1 + (C::Scalar::NUM_BITS as usize) - 2);

        // in order for CRT method to work, we need `abs(out + modulus * quotient - a) < 2^{trunc_len - 1} * native_modulus::<F>`
        // this is ensured if `0 <= out < 2^{n*k}` and
        // `abs(modulus * quotient) < 2^{trunc_len - 1} * native_modulus::<F> - abs(a)
        // which is ensured if
        // `abs(modulus * quotient) < 2^{trunc_len - 1 + F::NUM_BITS - 1} <= 2^{trunc_len - 1} * native_modulus::<F> - abs(a)` given our assumption `abs(a) <= 2^{n * k - 1 + F::NUM_BITS - 2}`
        let quot_max_bits = trunc_len - 1 + (C::Scalar::NUM_BITS as usize) - 1 - (wrong_mod.bits() as usize);
        debug_assert!(quot_max_bits < trunc_len);
        // Let n' <= quot_max_bits - n(k-1) - 1
        // If quot[i] <= 2^n for i < k - 1 and quot[k-1] <= 2^{n'} then
        // quot < 2^{n(k-1)+1} + 2^{n' + n(k-1)} = (2+2^{n'}) 2^{n(k-1)} < 2^{n'+1} * 2^{n(k-1)} <= 2^{quot_max_bits - n(k-1)} * 2^{n(k-1)}
        let quot_last_limb_bits = quot_max_bits - n * (k - 1);

        let out_max_bits = wrong_mod.bits() as usize;
        // we assume `wrong_mod` requires *exactly* `k` limbs to represent (if `< k` limbs ok, you should just be using that)
        let out_last_limb_bits = out_max_bits - n * (k - 1);

        // these are witness vectors:
        // we need to find `out_vec` as a proper BigInt with k limbs
        // we need to find `quot_vec` as a proper BigInt with k limbs

        let (quot_val, out_val) = a.value.div_mod_floor(&wrong_mod);

        debug_assert!(out_val < (BigInt::one() << (n * k)));
        debug_assert!(quot_val.abs() < (BigInt::one() << quot_max_bits));

        // decompose_bigint just throws away signed limbs in index >= k
        let out_vec = decompose_bigint::<C::Scalar>(&out_val, k, n);
        let quot_vec = decompose_bigint::<C::Scalar>(&quot_val, k, n);

        // we need to constrain that `sum_i out_vec[i] * 2^{n*i} = out_native` in `F`
        // we need to constrain that `sum_i quot_vec[i] * 2^{n*i} = quot_native` in `F`

        // assert!(modulus < &(BigUint::one() << (n * k)));
        assert_eq!(mod_limbs.len(), k);
        // We need to show `out - a + modulus * quotient` is:
        // - congruent to `0 (mod 2^trunc_len)`
        // - equal to 0 in native field `F`

        // Modulo 2^trunc_len, using OverflowInteger:
        // ------------------------------------------
        // Goal: assign cells to `out - a + modulus * quotient`
        // 1. we effectively do mul_no_carry::truncate(mod_limbs, quot_vec) while assigning `mod_limbs` and `quot_vec` as we go
        //    call the output `prod` which has len k
        // 2. for prod[i] we can compute `prod + out - a`
        //    where we assign `out_vec` as we go

        let mut quot_assigned: Vec<Self::Num> = Vec::with_capacity(k);
        let mut out_assigned: Vec<Self::Num> = Vec::with_capacity(k);
        let mut check_assigned: Vec<Self::Num> = Vec::with_capacity(k);

        // strategies where we carry out school-book multiplication in some form:
        //    BigIntStrategy::Simple => {
        for (i, ((a_limb, quot_v), out_v)) in
            a.limbs.into_iter().zip(quot_vec).zip(out_vec).enumerate()
        {
            let new_quot_cell = self.assign_witness(layouter.namespace(|| "assign_witness"), &quot_v, i)?;
            let mod_vec_assigned: Result<Vec<_>, _> = mod_limbs[..=i]
                .iter()
                .rev()
                .enumerate()
                .map(|(index, c)| self.assign_fixed(layouter.namespace(|| "assign_fixed"), c, index))
                .collect();
            let prod = self.inner_product(
                layouter.namespace(|| "inner_product_left_last"),
                quot_assigned.iter().chain(iter::once(&new_quot_cell)).cloned().collect_vec().as_slice(),
                &mod_vec_assigned?,
            )?;

            // perform step 2: compute prod - a + out
            let temp1 = prod.value() - a_limb.value();
            let temp1_assigned = self.assign_witness(layouter.namespace(|| "assign_witness"), &temp1, i)?;
            let check_val = temp1 + out_v;
            let out_val_assigned = self.assign_witness(layouter.namespace(|| "assign_witness"), &out_v, i)?;
            let check_val_assigned = self.assign_witness(layouter.namespace(|| "assign_witness"), &check_val, i)?;

            // transpose of:
            // | prod | -1 | a | prod - a | 1 | out | prod - a + out
            // where prod is at relative row `offset`
            let prod_minus_a = self.sub(layouter.namespace(|| "carry_mod"), &prod, &a_limb)?;
            self.constrain_equal(layouter.namespace(|| "constrain_equal"), &prod_minus_a, &temp1_assigned)?;
            let prod_minus_a_plus_out = self.add(layouter.namespace(|| "carry_mod"), &prod_minus_a, &out_val_assigned)?;
            self.constrain_equal(layouter.namespace(|| "constrain_equal"), &prod_minus_a_plus_out, &check_val_assigned)?;
            
            quot_assigned.push(new_quot_cell);
            out_assigned.push(out_val_assigned);
            check_assigned.push(check_val_assigned);
        }

        // range check limbs of `out` are in [0, 2^n) except last limb should be in [0, 2^out_last_limb_bits)
        for (out_index, out_cell) in out_assigned.iter().enumerate() {
            let limb_bits = if out_index == k - 1 { out_last_limb_bits } else { n };
            self.range_check_chip.assign(layouter.namespace(|| "range_check"), out_cell, limb_bits)?;
        }

        // range check that quot_cell in quot_assigned is in [-2^n, 2^n) except for last cell check it's in [-2^quot_last_limb_bits, 2^quot_last_limb_bits)
        for (q_index, quot_cell) in quot_assigned.iter().enumerate() {
            let limb_bits = if q_index == k - 1 { quot_last_limb_bits } else { n };
            let limb_base =
                if q_index == k - 1 { self.pow_of_two[limb_bits] } else { limb_bases[1] };
            let limb_base_assigned = self.assign_fixed(layouter.namespace(|| "assign_fixed"), &limb_base, 0)?;
            // compute quot_cell + 2^n and range check with n + 1 bits
            let quot_shift = self.add(layouter.namespace(|| "add"), quot_cell, &limb_base_assigned)?;
            self.range_check_chip.assign(layouter.namespace(|| "range_check"), &quot_shift, limb_bits + 1)?;
        }

        let check_overflow_int_limbs = check_assigned;
        // using const NUM_LIMB_BITS_NON_NATIVE as max_limb_bits for each nonnative limb
        let max_limb_bits = max(max(num_limb_bits, NUM_LIMB_BITS_NON_NATIVE) + 1, 2 * n + num_limbs);

        let limb_bases_assigned = limb_bases.iter().enumerate().map(|(index, c)| self.assign_fixed(layouter.namespace(|| "assign_fixed"), c, index)).collect::<Result<Vec<_>, _>>()?;
        // check that `out - a + modulus * quotient == 0 mod 2^{trunc_len}` after carry
        self.truncate(
            layouter.namespace(|| "truncate"),
            check_overflow_int_limbs,
            num_limb_bits,
            &limb_bases_assigned[1],
            &limb_base_big,
            max_limb_bits,
        )?;

        // Constrain `quot_native = sum_i quot_assigned[i] * 2^{n*i}` in `F`
        let quot_native = self.inner_product(layouter.namespace(|| "inner_product_quot_native"), &quot_assigned, &limb_bases_assigned)?;

        // Constrain `out_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
        let out_native = self.inner_product(layouter.namespace(|| "inner_product_out_native"), &out_assigned, &limb_bases_assigned)?;
        // // We save 1 cell by connecting `out_native` computation with the following:

        // // Check `out + modulus * quotient - a = 0` in native field
        let mod_native_assigned = self.assign_fixed(layouter.namespace(|| "assign_fixed"), &mod_native, 0)?;
        let mul_add_result = self.mul_add(layouter.namespace(|| "mul_add"), &mod_native_assigned, &quot_native, &out_native)?;
        self.constrain_equal(layouter.namespace(|| "constrain_equal"), &mul_add_result, &a.native)?;
        Ok(NonNativeNumber::new(out_assigned, out_native, out_val, modulus::<C::Base>()))
    }
}
