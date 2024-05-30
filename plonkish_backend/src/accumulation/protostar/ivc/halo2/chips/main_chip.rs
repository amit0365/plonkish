use std::iter::once;

use ark_std::One;
use halo2_base::{halo2_proofs::{circuit::{AssignedCell, Layouter, Value}, plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector}, poly::Rotation}, utils::{biguint_to_fe, decompose_biguint, fe_to_biguint, modulus, BigPrimeField, FromUniformBytes}};
use halo2_base::halo2_proofs::{arithmetic::{CurveAffine, Field}, halo2curves::ff::PrimeFieldBits};
use num_bigint::BigUint;
use crate::{accumulation::protostar::ivc::halo2::ivc_circuits::primary::T, util::arithmetic::{fe_from_limbs, fe_to_limbs, into_coordinates, TwoChainCurve}};
use itertools::Itertools;

use super::range_check::RangeCheckChip;
pub const NUM_MAIN_ADVICE: usize = 7;//T + 1;
pub const NUM_MAIN_FIXED: usize = 2*T;
pub const NUM_LIMB_BITS_PRIMARY_NON_NATIVE: usize = 128;
pub const NUM_LIMBS_PRIMARY_NON_NATIVE: usize = 2;
pub const NUM_LIMB_BITS_NON_NATIVE: usize = 88;
pub const NUM_LIMBS_NON_NATIVE: usize = 3;

    #[derive(Clone, Debug)]
    pub struct Number<F: Field>(pub AssignedCell<F, F>);

    // impl<C: TwoChainCurve> Field for Number<C::Scalar> 
    //     where
    //     C::Base: BigPrimeField + PrimeFieldBits,
    //     C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    // {

    // }

    #[derive(Clone, Debug)]
    pub struct NonNativeNumber<F: Field> {
        pub limbs: Vec<Number<F>>,
        pub native: Number<F>,
    }

    impl<F: Field> NonNativeNumber<F> {
        pub fn limbs(&self) -> &Vec<Number<F>> {
            &self.limbs
        }

        pub fn native(&self) -> &Number<F> {
            &self.native
        }

        pub fn new(limbs: Vec<Number<F>>, native: Number<F>) -> Self {
            NonNativeNumber { limbs, native }
        }
    }

    // assume point is not infinity
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

        // pub fn native(&self) -> &Number<F> {
        //     &self.native
        // }

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
        //range_check_chip: RangeCheckChip<C>,
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

        // /// Returns a new [GateChip] with the given [GateStrategy].
        // pub fn new(config: MainChipConfig, range_check_chip: RangeCheckChip<C>) -> Self {
        //     let mut pow_of_two = Vec::with_capacity(C::Scalar::NUM_BITS as usize);
        //     let two = C::Scalar::from(2);
        //     pow_of_two.push(C::Scalar::ONE);
        //     pow_of_two.push(two);
        //     for _ in 2..C::Scalar::NUM_BITS {
        //         pow_of_two.push(two * pow_of_two.last().unwrap());
        //     }
        //     Self { config, pow_of_two, range_check_chip }
        // }

        /// Returns a new [GateChip] with the given [GateStrategy].
        pub fn new(config: MainChipConfig) -> Self {
            let mut pow_of_two = Vec::with_capacity(C::Scalar::NUM_BITS as usize);
            let two = C::Scalar::from(2);
            pow_of_two.push(C::Scalar::ONE);
            pow_of_two.push(two);
            for _ in 2..C::Scalar::NUM_BITS {
                pow_of_two.push(two * pow_of_two.last().unwrap());
            }
            Self { config, pow_of_two }
        }
    
        pub fn configure(
            meta: &mut ConstraintSystem<C::Scalar>,
            advice: [Column<Advice>; NUM_MAIN_ADVICE],
            fixed: [Column<Fixed>; NUM_MAIN_FIXED],
        ) -> MainChipConfig {

            let [mul_add, inner_product] = [(); 2].map(|_| meta.selector());
    
            // meta.create_gate("main constraint", |meta| {
            //     let s2 = meta.query_selector(inner_product);
            //     let s1 = meta.query_selector(mul_add);
            //     let a = meta.query_advice(col_a, Rotation::cur());
            //     let b = meta.query_advice(col_b, Rotation::cur());
            //     let acc = meta.query_advice(col_acc, Rotation::cur());
            //     let acc_next = meta.query_advice(col_acc, Rotation::next());    
            //     vec![s1 * (a * b + acc) - s2 * acc_next]
            // });

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
            limbs: Vec<Self::Num>
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
            Ok(NonNativeNumber { limbs, native: a_computed_native })
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
            //self.constrain_equal(layouter, &a_computed_native, &a_native_assigned)?;
    
            //self.range_check_chip.assign(layouter.namespace(|| "range check"), &a_computed_native);
            Ok(NonNativeNumber::new(limbs, a_native_assigned))

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
            Ok(NonNativeNumber::new(fixed, a_native_assigned))
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
            let mut a_value = C::Scalar::ZERO;
            let mut b_value = C::Scalar::ZERO;
            let inner_product = a.iter().zip(b.iter()).fold(
                C::Scalar::ZERO,    
                |acc, element| {
                    element.0.0.value().map(|v| a_value = *v); 
                    element.1.0.value().map(|v| b_value = *v);
                    acc + a_value * b_value
                }
            );

            let mut accumulator = C::Scalar::ZERO;
            let mut product = Vec::new();
            let acc = a.iter()
                .zip(b.iter())
                .map(|(a, b)| {
                    a.0.value().map(|v| a_value = *v); 
                    b.0.value().map(|v| b_value = *v);
                    let result = a_value * b_value + accumulator;
                    accumulator = result;
                    Value::known(result)
                })
                .collect_vec();

            layouter.assign_region(
                || "inner product",
                |mut region | {
                    a.iter()
                        .zip(b.iter())
                        .enumerate()
                        .map(|(i, (a, b))| {

                            self.config.selector[1].enable(&mut region, i);

                            a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], i);
                            b.0.copy_advice(|| "rhs", &mut region, self.config.advice[1], i);
                            zero.0.copy_advice(|| "zero", &mut region, self.config.advice[2], i);

                            let value = a.0.value().copied() * b.0.value() + acc[i];
    
                            // Finally, we do the assignment to the output, returning a
                            // variable to be used in another part of the circuit.
                            let result = region
                                .assign_advice(|| "lhs * rhs + acc",
                                self.config.advice[3], i, || value);

                            product.push(result.unwrap());
                            // product.as_ref().last().unwrap().unwrap()
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
            let mut a_value = C::Scalar::ZERO;
            let mut b_value = C::Scalar::ZERO;
            let inner_product = a.iter().zip(b.iter()).map(|(a, b)| {
                a.limbs.iter().zip(b.limbs.iter()).fold(
                    C::Scalar::ZERO,
                    |acc, (a, b)| {
                        a.0.value().map(|v| a_value = *v); 
                        b.0.value().map(|v| b_value = *v);
                        acc + a_value * b_value
                })
            });

            let mut accumulator = C::Scalar::ZERO;
            let mut product = Vec::new();
            let acc = a.iter()
                .zip(b.iter())
                .map(|(a, b)| {
                    a.limbs.iter().zip(b.limbs.iter()).map(|(a, b)| {
                        a.0.value().map(|v| a_value = *v); 
                        b.0.value().map(|v| b_value = *v);
                        let result = a_value * b_value + accumulator;
                        accumulator = result;
                        Value::known(result)
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
                                self.config.selector[1].enable(&mut region, offset);

                                a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], offset);
                                b.0.copy_advice(|| "rhs", &mut region, self.config.advice[1], offset);
                                zero_native.0.copy_advice(|| "zero_native", &mut region, self.config.advice[2], offset)?;

                                let value = a.0.value().copied() * b.0.value().copied() + acc[i][j];
        
                                // Finally, we do the assignment to the output, returning a
                                // variable to be used in another part of the circuit.
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
                self.from_limbs(layouter.namespace(|| "from_limbs"), product.iter().rev().take(num_limbs).cloned().collect_vec())
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
            
            self.from_limbs(layouter.namespace(|| "from_limbs"), result)
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
            self.from_limbs(layouter.namespace(|| "from_limbs"), result)
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
        
            self.from_limbs(layouter.namespace(|| "from_limbs"), result)
        }

        pub fn mul_add(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
            c: &Self::Num,
        ) -> Result<Self::Num, Error> {
            // | a | b | c | a * b + c |
            let zero = self.assign_fixed(layouter.namespace(|| "assign_zero"), &C::Scalar::ZERO, 0)?;                           
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
            let zero = self.assign_fixed(layouter.namespace(|| "assign_zero"), &C::Scalar::ZERO, 0)?;                           
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
        
            self.from_limbs(layouter.namespace(|| "from_limbs"), result)
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
        
            self.from_limbs(layouter.namespace(|| "from_limbs"), result)
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
    }