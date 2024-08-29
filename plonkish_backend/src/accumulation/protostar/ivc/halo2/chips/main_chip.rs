use std::iter::{self, once};
use std::cmp::max;
use std::marker::PhantomData;
use ark_std::One;
use halo2_base::halo2_proofs::circuit::floor_planner::V1;
use halo2_base::halo2_proofs::circuit::{Region, SimpleFloorPlanner};
use halo2_base::halo2_proofs::dev::{CircuitLayout, MockProver};
use halo2_base::halo2_proofs::halo2curves::bn256;
use halo2_base::halo2_proofs::plonk::{Circuit, Constraints, Instance};
use halo2_base::utils::ScalarField;
use halo2_base::{halo2_proofs::{circuit::{AssignedCell, Layouter, Value}, plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector}, poly::Rotation}, utils::{bigint_to_fe, biguint_to_fe, decompose_bigint, decompose_biguint, fe_to_bigint, fe_to_biguint, modulus, BigPrimeField, FromUniformBytes}};
use halo2_base::halo2_proofs::{arithmetic::{CurveAffine, Field}, halo2curves::ff::PrimeFieldBits};
use num_bigint::{BigUint, BigInt};
use halo2_base::utils::decompose;
use itertools::Itertools;
use num_integer::Integer;
use num_traits::sign::Signed;
use rand::rngs::OsRng;
use super::range_check::{RangeCheckChip, RangeCheckConfig};
use super::transcript::{NUM_CHALLENGE_BITS, NUM_HASH_BITS, RANGE_BITS};
use crate::{accumulation::protostar::ivc::halo2::ivc_circuits::primary::T, util::arithmetic::{fe_from_limbs, fe_to_limbs, into_coordinates, TwoChainCurve}};

pub const LOOKUP_BITS: usize = 8;
pub const NUM_MAIN_ADVICE: usize = T + 1;
pub const NUM_MAIN_FIXED: usize = 2*T;
pub const NUM_MAIN_SELECTORS: usize = 4;

pub const NUM_LIMB_BITS_PRIMARY_NON_NATIVE: usize = 128;
pub const NUM_LIMBS_PRIMARY_NON_NATIVE: usize = 2;
pub const NUM_LIMB_BITS_NON_NATIVE: usize = 88;
pub const NUM_LIMBS_NON_NATIVE: usize = 3;


    #[derive(Clone, Debug)]
    pub struct Number<F: Field>(pub AssignedCell<F, F>);

    impl<F: BigPrimeField> Number<F> {
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
            let num_limbs = NUM_LIMBS_NON_NATIVE;
            let num_limb_bits = NUM_LIMB_BITS_NON_NATIVE;
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
        instance: Column<Instance>,
        selector: [Selector; NUM_MAIN_SELECTORS],
    }

    #[derive(Clone, Debug)]
    pub struct MainChip<C: TwoChainCurve> 
        where
        C::Base: BigPrimeField + PrimeFieldBits,
        C::Scalar: BigPrimeField + FromUniformBytes<64> + PrimeFieldBits,
    {
        pub config: MainChipConfig,
        pub pow_of_two: Vec<C::Scalar>,
        pub pow_of_two_assigned: Vec<Number<C::Scalar>>,
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

            Self { config, pow_of_two, pow_of_two_assigned: Vec::new(), range_check_chip }
        }

        pub fn initialize(&mut self, layouter: &mut impl Layouter<C::Scalar>) -> Result<(), Error> {
            self.pow_of_two_assigned = self.assign_witnesses(layouter, &self.pow_of_two)?;
            Ok(())
        }
    
        pub fn configure(
            meta: &mut ConstraintSystem<C::Scalar>,
            advice: [Column<Advice>; NUM_MAIN_ADVICE],
            fixed: [Column<Fixed>; NUM_MAIN_FIXED],
        ) -> MainChipConfig {

            let [mul_add, inner_product, inner_product_opt, bit_constraint] = [(); NUM_MAIN_SELECTORS].map(|_| meta.selector());
            let instance = meta.instance_column();
            meta.enable_equality(instance);

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

            meta.create_gate("inner product opt", |meta| {
                let s = meta.query_selector(inner_product_opt);
                let zero = Expression::Constant(C::Scalar::ZERO);
                let a = (0..NUM_MAIN_ADVICE - 1).map(|i| meta.query_advice(advice[i], Rotation::cur())).collect_vec();
                let b = (0..NUM_MAIN_ADVICE - 1).map(|i| meta.query_advice(advice[i], Rotation::next())).collect_vec();
                let acc = meta.query_advice(advice[NUM_MAIN_ADVICE - 1], Rotation::cur());
                let acc_next = meta.query_advice(advice[NUM_MAIN_ADVICE - 1], Rotation::next());    
                let product = a.iter().zip(b.iter()).fold(zero, |acc, (a, b)| acc + a.clone() * b.clone());
                vec![s * (product + acc - acc_next)]
            });

            meta.create_gate("bit constraint", |meta| {
                let s = meta.query_selector(bit_constraint);
                let one = Expression::Constant(C::Scalar::ONE);
                let x = (0..NUM_MAIN_ADVICE - 1).map(|i| meta.query_advice(advice[i], Rotation::cur())).collect_vec();
                
                Constraints::with_selector(
                    s,
                    x.into_iter().map(|x| x.clone() * (one.clone() - x)).collect_vec()
                )
            });
            
            MainChipConfig {
                advice,
                fixed,
                instance,
                selector: [mul_add, inner_product, inner_product_opt, bit_constraint],
            }
        }

        pub fn expose_public(
            &self,
            mut layouter: impl Layouter<C::Scalar>,
            num: &Self::Num,
            row: usize,
        ) -> Result<(), Error> {
            layouter.constrain_instance(num.0.cell(), self.config.instance, row)
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

        pub fn assign_witness(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            witness: &C::Scalar,
            witness_index: usize,
        ) -> Result<Self::Num, Error> {
            let config = &self.config;
            let idx = witness_index % NUM_MAIN_ADVICE;
            layouter.assign_region(
                || "assign witness",
                |mut region| {
                    region.assign_advice(
                            || "witness",
                            config.advice[idx],
                            0,
                            || Value::known(*witness),
                        ).map(Number)
                },
            )
        }

        pub fn assign_witnesses(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            witnesses: &[C::Scalar],
        ) -> Result<Vec<Self::Num>, Error> {
            witnesses.iter().enumerate().map(|(idx, witness)| self.assign_witness(layouter, witness, idx)).collect::<Result<Vec<_>, _>>()
        }

        // todo check this
        // pub fn from_limbs(
        //     &self,
        //     layouter: &mut impl Layouter<C::Scalar>,
        //     limbs: Vec<Self::Num>,
        //     result_value: BigInt,
        // ) -> Result<Self::NonNatNum, Error> {
        //     let num_limbs = limbs.len();
        //     let limb_bits = if num_limbs == NUM_LIMBS_NON_NATIVE { NUM_LIMB_BITS_NON_NATIVE } 
        //         else if num_limbs == NUM_LIMBS_PRIMARY_NON_NATIVE { NUM_LIMB_BITS_PRIMARY_NON_NATIVE } else { unreachable!() };
                
        //     let limb_base = biguint_to_fe::<C::Scalar>(&(BigUint::one() << limb_bits));
        //     let mut limb_bases = Vec::with_capacity(num_limbs);
        //         limb_bases.push(C::Scalar::ONE);
           
        //     while limb_bases.len() != num_limbs {
        //         limb_bases.push(limb_base * limb_bases.last().unwrap());
        //     }
        //     let limb_bases_assigned = self.assign_witnesses(layouter, &limb_bases)?;
    
        //     let a_computed_native = self.inner_product(layouter, &limbs, &limb_bases_assigned)?;
        //     Ok(NonNativeNumber::new(limbs, a_computed_native, result_value, modulus::<C::Base>()))
        // }

        pub fn assign_witness_base(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: C::Base,
        ) -> Result<Self::NonNatNum, Error> {
            let native_modulus = modulus::<C::Scalar>();
            let a = fe_to_biguint(&a);
            let a_native = biguint_to_fe(&(&a % &native_modulus)); 
            let a_native_assigned = self.assign_witness(layouter, &a_native, 0)?;

            let num_limbs = NUM_LIMBS_NON_NATIVE;
            let limb_bits = NUM_LIMB_BITS_NON_NATIVE;
            let a_vec = decompose_biguint::<C::Scalar>(&a, num_limbs, limb_bits);
            let limbs = self.assign_witnesses(layouter, &a_vec)?;
            let limb_base = biguint_to_fe::<C::Scalar>(&(BigUint::one() << limb_bits));
            let mut limb_bases = Vec::with_capacity(num_limbs);
            limb_bases.push(C::Scalar::ONE);
            while limb_bases.len() != num_limbs {
                limb_bases.push(limb_base * limb_bases.last().unwrap());
            }
            let limb_bases_assigned = self.assign_witnesses(layouter, &limb_bases)?;

            let a_computed_native = self.inner_product(layouter, &limbs, &limb_bases_assigned)?;
            self.constrain_equal(layouter, &a_computed_native, &a_native_assigned)?;
            
            self.range_check_chip.assign(layouter, &a_computed_native, C::Scalar::NUM_BITS as usize)?;
            Ok(NonNativeNumber::new(limbs, a_native_assigned, a.into(), modulus::<C::Base>()))

        }

        pub fn assign_witness_primary(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            witness: C,
        ) -> Result<Self::Ecc, Error> {
            let coords = into_coordinates(&witness);
            let x = self.assign_witness_base(layouter, coords[0])?;
            let y = self.assign_witness_base(layouter, coords[1])?;
            Ok(EcPointNonNative { x, y })
        }

        pub fn assign_witness_secondary(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            witness: C::Secondary,
        ) -> Result<Self::NatEcc, Error> {
            let coords = into_coordinates(&witness);
            let x = self.assign_witness(layouter, &coords[0], 0)?;
            let y = self.assign_witness(layouter, &coords[1], 1)?;
            Ok(EcPointNative { x, y })
        }
            
        pub fn assign_fixed(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
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
            layouter: &mut impl Layouter<C::Scalar>,
            fixed: &C::Base,
        ) -> Result<Self::NonNatNum, Error> {
            let config = &self.config;
            let num_limbs = NUM_LIMBS_NON_NATIVE;
            let limb_bits = NUM_LIMB_BITS_NON_NATIVE;

            let native_modulus = modulus::<C::Scalar>();
            let a = fe_to_biguint(fixed);
            let a_native = biguint_to_fe(&(&a % &native_modulus)); 
            let a_native_assigned = self.assign_witness(layouter, &a_native, 0)?;
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
            layouter: &mut impl Layouter<C::Scalar>,
            witness: C,
        ) -> Result<Self::Ecc, Error> {
            let coords = into_coordinates(&witness);
            let x = self.assign_witness_base(layouter, coords[0])?;
            let y = self.assign_witness_base(layouter, coords[1])?;
            Ok(EcPointNonNative { x, y })
        }

        pub fn assign_constant_secondary(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            witness: C::Secondary,
        ) -> Result<Self::NatEcc, Error> {
            let coords = into_coordinates(&witness);
            let x = self.assign_witness(layouter, &coords[0], 0)?;
            let y = self.assign_witness(layouter, &coords[1], 1)?;
            Ok(EcPointNative { x, y })
        }

        pub fn select(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            sel: &Self::Num,
            a: &Self::Num,
            b: &Self::Num,
        )-> Result<Self::Num, Error>{
            // | sel | a - b | b | out |
            let diff = self.sub(layouter, a, b)?;
            self.mul_add(layouter, sel, &diff, b)
        }

        pub fn select_base(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            is_base_case: &Self::Num,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        )-> Result<Self::NonNatNum, Error>{
            // | sel | a - b | b | out |
            let diff = self.sub_base(layouter, a, b)?;
            self.mul_native_add_base(layouter, is_base_case, &diff , b)
        }

        pub fn select_primary(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            is_base_case: &Self::Num,
            a: &Self::Ecc,
            b: &Self::Ecc,
        )-> Result<Self::Ecc, Error>{    
            let x = self.select_base(layouter, is_base_case, &a.x, &b.x)?;
            let y = self.select_base(layouter, is_base_case, &a.y, &b.y)?;
            Ok(EcPointNonNative { x, y })
        }

        pub fn select_secondary(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            is_base_case: &Self::Num,
            a: &Self::NatEcc,
            b: &Self::NatEcc,
        )-> Result<Self::NatEcc, Error>{    
            let x = self.select(layouter, is_base_case, &a.x, &b.x)?;
            let y = self.select(layouter, is_base_case, &a.y, &b.y)?;
            Ok(EcPointNative { x, y })
        }

        //todo can replace with is_zero gate
        pub fn is_zero(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: &Self::Num,
        )-> Result<Self::Num, Error>{
            let zero = self.assign_fixed(layouter, &C::Scalar::ZERO, 0)?;
            let one = self.assign_fixed(layouter, &C::Scalar::ONE, 1)?;
            let a_inv = if a.value().is_zero().into() { C::Scalar::ONE } else { a.value().invert().unwrap_or(C::Scalar::ZERO) };
            let a_inv_assigned = self.assign_witness(layouter, &a_inv, 2)?;

            let out = self.mul(layouter, a, &a_inv_assigned)?;
            let one_minus_out = self.sub(layouter, &one, &out)?;
            let out_constraint = self.mul(layouter, a, &one_minus_out)?;
            self.constrain_equal(layouter, &out_constraint, &zero)?;
            Ok(one_minus_out)
        }

        pub fn is_equal(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            lhs: &Self::Num,
            rhs: &Self::Num,
        )-> Result<Self::Num, Error>{
            let diff = self.sub(layouter, lhs, rhs)?;
            let is_zero = self.is_zero(layouter, &diff)?;
            Ok(is_zero)
        }

        pub fn constrain_equal(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
        ) -> Result<(), Error> {
            //for testing
            assert_eq!(a.value(), b.value());
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
            layouter: &mut impl Layouter<C::Scalar>,
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
            layouter: &mut impl Layouter<C::Scalar>,
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
            layouter: &mut impl Layouter<C::Scalar>,
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
        
        /// Constrains that x is boolean (e.g. 0 or 1).
        ///
        /// Defines a vertical gate of form | 0 | x | x | x |.
        /// * `ctx`: [Context] to add the constraints to
        /// * `x`: [QuantumCell] value to constrain
        // pub fn assign_bit(
        //     &self,
        //     layouter: &mut impl Layouter<C::Scalar>,
        //     x: &C::Scalar,
        // ) -> Result<Self::Num, Error> {
        //     // | x | x | 0 | x * x |
        //     layouter.assign_region(
        //         || "assign_bit",
        //         |mut region | {        
        //             self.config.selector[0].enable(&mut region, 0)?; 
        //             let x = region.assign_advice(
        //                 || "x",
        //                 self.config.advice[0], 0, || Value::known(*x)
        //             )?;
        //             x.copy_advice(|| "x", &mut region, self.config.advice[1], 0)?;
        //             region.assign_advice(
        //                 || "0",
        //                 self.config.advice[2], 0, || Value::known(C::Scalar::ZERO)
        //             )?;    

        //             let value = x.value().copied() * x.value().copied();
        //             let out = region.assign_advice(
        //                 || "x * x + 0",
        //                 self.config.advice[3], 0, || value
        //             )?;
                        
        //             region.constrain_equal(x.cell(), out.cell())?;
        //             Ok(Number(x))
        //         })
        // }

        pub fn inner_product(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: &[Self::Num],
            b: &[Self::Num],
        ) -> Result<Self::Num, Error> {

            let mut acc_vec = vec![Value::known(C::Scalar::ZERO)];
            a.iter().zip(b.iter()).fold(
                C::Scalar::ZERO,
                |acc, (a, b)| {
                    acc_vec.push(Value::known(acc + a.value() * b.value()));
                    acc + a.value() * b.value()
            });
            acc_vec.pop();

            layouter.assign_region(
                || "inner product",
                |mut region: Region<'_, C::Scalar> | {
                    a.iter()
                        .zip(b.iter())
                        .enumerate()
                        .map(|(i, (a, b))| {

                            self.config.selector[1].enable(&mut region, i)?;

                            a.0.copy_advice(|| "lhs", &mut region, self.config.advice[0], i)?;
                            b.0.copy_advice(|| "rhs", &mut region, self.config.advice[1], i)?;
                            let acc = region
                                .assign_advice(|| "acc[i]",
                                self.config.advice[2], i, || acc_vec[i])?;

                            let value = a.0.value().copied() * b.0.value().copied() + acc.value().copied();

                            region
                                .assign_advice(|| "lhs * rhs + acc",
                                self.config.advice[3], i, || value).map(Number)
                        })
                        .collect::<Result<Vec<_>, _>>()
                },
            )?.last().cloned().ok_or(Error::Synthesis)
        }

        pub fn inner_product_combined(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            num_bits: usize,
            chunk_size: usize,
            a: &[C::Scalar],
            b: &[Self::Num],
        ) -> Result<(Self::Num, Self::Num, Vec<Self::Num>), Error> {

            let zero = self.assign_fixed(layouter, &C::Scalar::ZERO, 0)?;
            let mut bit_cells= Vec::new();
            let mut num = zero.clone();
            let mut bits_to_num = zero.clone();

            let product = layouter.assign_region(
                || "inner_product_combined",
                |mut region: Region<'_, C::Scalar> | {
                    a.iter()
                        .zip(b.iter())
                        .chunks(chunk_size)
                        .into_iter()
                        .enumerate()
                        .try_fold(
                            zero.clone(),
                            |acc, (j, chunk)| {

                                let mut acc_value = acc.value();
                                let (bits, pow2): (Vec<_>, Vec<_>) = chunk
                                    .map(|(bit, pow2)| {
                                        acc_value += pow2.value() * *bit;
                                        (bit, pow2)
                                    })
                                    .unzip();

                                let padding_bits = if pow2.len() < NUM_MAIN_ADVICE - 1 {
                                        vec![C::Scalar::ZERO; NUM_MAIN_ADVICE - 1 - pow2.len()]
                                    } else {
                                        vec![C::Scalar::ZERO; 0]
                                    };

                                let padding_pow2 = if pow2.len() < NUM_MAIN_ADVICE - 1 {
                                        vec![zero.clone(); NUM_MAIN_ADVICE - 1 - pow2.len()]
                                    } else {
                                        vec![zero.clone(); 0]
                                    };

                                self.config.selector[2].enable(&mut region, 2*j)?;
                                self.config.selector[3].enable(&mut region, 2*j)?;

                                bits.into_iter().chain(padding_bits.iter()).enumerate().for_each(|(i, bit)| {
                                    bit_cells.push(Number(region.assign_advice(|| "bits", self.config.advice[i], 2*j, || Value::known(*bit)).unwrap()));
                                });
                                pow2.into_iter().chain(padding_pow2.iter()).enumerate().for_each(|(i, pow2)| {
                                    pow2.0.copy_advice(|| "pow2", &mut region, self.config.advice[i], 2*j+1).unwrap();
                                });

                                region
                                    .assign_advice(|| "acc[i]",
                                    self.config.advice[NUM_MAIN_ADVICE - 1], 2*j, || Value::known(acc.value()))?;

                                num = region
                                    .assign_advice(|| "lhs * rhs + acc",
                                    self.config.advice[NUM_MAIN_ADVICE - 1], 2*j+1, || Value::known(acc_value)).map(Number)?;
                                
                                if j == num_bits/(NUM_MAIN_ADVICE - 1) - 1 {
                                    bits_to_num = num.clone();
                                }
                                Ok(num.clone())
                            }
                        )
                    },
                )?;
            Ok((product, bits_to_num, bit_cells))
        }

        pub fn inner_product_opt(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: &[C::Scalar],
            b: &[Self::Num],
        ) -> Result<(Self::Num, Vec<Self::Num>), Error> {

            let zero = self.assign_fixed(layouter, &C::Scalar::ZERO, 0)?;
            let mut bit_cells= Vec::new();

            let product = layouter.assign_region(
                || "inner product opt",
                |mut region: Region<'_, C::Scalar> | {
                    a.iter()
                        .zip(b.iter())
                        .chunks(NUM_MAIN_ADVICE - 1)
                        .into_iter()
                        .enumerate()
                        .try_fold(
                            zero.clone(),
                            |acc, (j, chunk)| {

                                let mut acc_value = acc.value();
                                let (bits, pow2): (Vec<_>, Vec<_>) = chunk
                                    .map(|(bit, pow2)| {
                                        acc_value += pow2.value() * *bit;
                                        (bit, pow2)
                                    })
                                    .unzip();

                                let padding_bits = if pow2.len() < NUM_MAIN_ADVICE - 1 {
                                        vec![C::Scalar::ZERO; NUM_MAIN_ADVICE - 1 - pow2.len()]
                                    } else {
                                        vec![C::Scalar::ZERO; 0]
                                    };

                                let padding_pow2 = if pow2.len() < NUM_MAIN_ADVICE - 1 {
                                        vec![zero.clone(); NUM_MAIN_ADVICE - 1 - pow2.len()]
                                    } else {
                                        vec![zero.clone(); 0]
                                    };

                                self.config.selector[2].enable(&mut region, 2*j)?;
                                self.config.selector[3].enable(&mut region, 2*j)?;

                                bits.into_iter().chain(padding_bits.iter()).enumerate().for_each(|(i, bit)| {
                                    bit_cells.push(Number(region.assign_advice(|| "bits", self.config.advice[i], 2*j, || Value::known(*bit)).unwrap()));
                                });
                                pow2.into_iter().chain(padding_pow2.iter()).enumerate().for_each(|(i, pow2)| {
                                    pow2.0.copy_advice(|| "pow2", &mut region, self.config.advice[i], 2*j+1).unwrap();
                                });

                                region
                                    .assign_advice(|| "acc[i]",
                                    self.config.advice[NUM_MAIN_ADVICE - 1], 2*j, || Value::known(acc.value()))?;

                                region
                                    .assign_advice(|| "lhs * rhs + acc",
                                    self.config.advice[NUM_MAIN_ADVICE - 1], 2*j+1, || Value::known(acc_value)).map(Number)
                            }
                        )
                    },
                )?;
            Ok((product, bit_cells))
        }

        // todo check this
        pub fn inner_product_base(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: &[Self::NonNatNum],
            b: &[Self::NonNatNum],
        ) -> Result<Self::NonNatNum, Error> {
            let num_limbs = a[0].limbs.len();
            let inner_product_value = 
                a.iter().zip(b.iter()).fold(
                    BigInt::from(0),
                    |acc, (a, b)| {
                        acc + a.value.clone() * b.value.clone()
                });

            let mut accumulator = C::Scalar::ZERO;
            let mut acc = vec![vec![Value::known(C::Scalar::ZERO); num_limbs]];
            acc.extend(a.iter()
                .zip(b.iter())
                .map(|(a, b)| {
                    a.limbs.iter().zip(b.limbs.iter()).map(|(a, b)| {
                        accumulator += a.value() * b.value();
                        Value::known(accumulator)
                    }).collect_vec()
                }).collect_vec());
            acc.pop();

            let out_limbs = layouter.assign_region(
                || "inner product base",
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
                                let acc = region
                                    .assign_advice(|| "acc[i][j]",
                                    self.config.advice[2], offset, || acc[i][j])?;

                                let value = a.0.value().copied() * b.0.value().copied() + acc.value().copied();
                                region
                                    .assign_advice(|| "lhs * rhs + acc",
                                    self.config.advice[3], offset, || value).map(Number)
                            }).collect::<Result<Vec<_>, _>>()          
                }).collect::<Result<Vec<_>, _>>()
            })?.last().cloned().ok_or(Error::Synthesis)?;

            let a_native_vec = a.iter().map(|x| x.native.clone()).collect_vec();
            let b_native_vec = b.iter().map(|x| x.native.clone()).collect_vec();
            let out_native = self.inner_product(layouter, &a_native_vec, &b_native_vec)?;
            Ok(NonNativeNumber::new(out_limbs, out_native, inner_product_value, modulus::<C::Base>()))
        }

        pub fn bits_and_num(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            range_bits: usize,
            num_bits: usize,
            chunk_size: usize,
            num: &Self::Num,
        ) -> Result<(Self::Num, Self::Num, Vec<Self::Num>), Error> {
            let bits = num.value().to_u64_limbs(range_bits, 1)
                .into_iter()
                .map(C::Scalar::from)
                .collect_vec();

            debug_assert!(range_bits > 0);
            assert!((num_bits as u32) <= C::Scalar::CAPACITY);

            let (product, bits_to_num, bit_cells) = self.inner_product_combined(
                layouter,
                num_bits,
                chunk_size,
                &bits,
                &self.pow_of_two_assigned[..bits.len()],
            )?; 
            self.constrain_equal(layouter, num, &product)?;
            Ok((product, bits_to_num, bit_cells))
        }

        pub fn bits_and_num_limbs(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            range_bits: usize,
            num_bits: usize,
            chunk_size: usize,
            num: &Self::Num,
        ) -> Result<(Self::Num, Self::Num, Vec<Self::Num>), Error> {
            let limbs = decompose::<C::Scalar>(&num.value(), NUM_LIMBS_NON_NATIVE, NUM_LIMB_BITS_NON_NATIVE);
            let limbs_assigned = limbs.iter().map(|x| self.assign_witness(layouter, x, 0).unwrap()).collect_vec();
            debug_assert!(range_bits > 0);
            assert!((num_bits as u32) <= C::Scalar::CAPACITY);
            let mut pow_of_two_vec = Vec::new();
            let pow = C::Scalar::from(2).pow_vartime(&[NUM_LIMB_BITS_NON_NATIVE as u64]);
            let mut shift = C::Scalar::ONE;
            for _i in 0..NUM_LIMBS_NON_NATIVE {
                pow_of_two_vec.push(self.assign_fixed(layouter, &shift, 0).unwrap());
                shift *= pow;
            }
            
            let limbs_to_num = self.inner_product(
                layouter,
                &limbs_assigned,
                &pow_of_two_vec,
            )?; 

            self.constrain_equal(layouter, num, &limbs_to_num)?;
            let challenge_limbs = self.inner_product(layouter, &limbs_assigned[..2], &pow_of_two_vec)?;
            let challenge_limb_bits = self.limb_to_bits(layouter, NUM_LIMB_BITS_NON_NATIVE, &challenge_limbs, &limbs_assigned[..2])?.iter().take(NUM_CHALLENGE_BITS).cloned().collect_vec();

            Ok((limbs_to_num, challenge_limbs, challenge_limb_bits))
        }

        pub fn bits_and_num_limbs_hash(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            range_bits: usize,
            num_bits: usize,
            num: &Self::Num,
        ) -> Result<Self::Num, Error> {
            let limbs = decompose::<C::Scalar>(&num.value(), NUM_LIMBS_NON_NATIVE, NUM_LIMB_BITS_NON_NATIVE);
            let limbs_assigned = limbs.iter().map(|x| self.assign_witness(layouter, x, 0).unwrap()).collect_vec();
            debug_assert!(range_bits > 0);
            assert!((num_bits as u32) <= C::Scalar::CAPACITY);
            let mut pow_of_two_vec = Vec::new();
            let pow = C::Scalar::from(2).pow_vartime(&[NUM_LIMB_BITS_NON_NATIVE as u64]);
            let mut shift = C::Scalar::ONE;
            for _i in 0..NUM_LIMBS_NON_NATIVE {
                pow_of_two_vec.push(self.assign_fixed(layouter, &shift, 0).unwrap());
                shift *= pow;
            }
            
            let limbs_to_num = self.inner_product(
                layouter,
                &limbs_assigned,
                &pow_of_two_vec,
            )?; 

            self.constrain_equal(layouter, num, &limbs_to_num)?;
            let hash_last_limb_bits = self.num_to_bits(layouter, NUM_LIMB_BITS_NON_NATIVE, &limbs_assigned.last().unwrap())?;
            let hash_last_limb_bits_truncated = hash_last_limb_bits.iter().take(num_bits - (NUM_LIMBS_NON_NATIVE-1)*NUM_LIMB_BITS_NON_NATIVE).cloned().collect_vec();
            let hash_last_limb = self.bits_to_num(layouter, &hash_last_limb_bits_truncated)?;
            let mut hash_limbs = limbs_assigned[..NUM_LIMBS_NON_NATIVE-1].to_vec();
            hash_limbs.push(hash_last_limb);

            let limbs_to_num_hash = self.inner_product(
                layouter,
                &hash_limbs,
                &pow_of_two_vec,
            )?; 

            Ok(limbs_to_num_hash)
        }

        /// Constrains and returns little-endian bit vector representation of `a`.
        ///
        /// Assumes `range_bits >= number of bits in a`.
        /// * `a`: [QuantumCell] of the value to convert
        /// * `range_bits`: range of bits needed to represent `a`. Assumes `range_bits > 0`.
        pub fn num_to_bits(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            range_bits: usize,
            num: &Self::Num,
        ) -> Result<Vec<Self::Num>, Error> {

            let bits = num.value().to_u64_limbs(range_bits, 1)
                .into_iter()
                .map(C::Scalar::from)
                .collect_vec();
            debug_assert!(range_bits > 0);

            let (acc, bit_cells) = self.inner_product_opt(
                layouter,
                &bits,
                &self.pow_of_two_assigned[..bits.len()],
            )?; 
            self.constrain_equal(layouter, num, &acc)?;
            Ok(bit_cells)
        }

        /// Constrains and returns little-endian bit vector representation of `a`.
        ///
        /// Assumes `range_bits >= number of bits in a`.
        /// * `a`: [QuantumCell] of the value to convert
        /// * `range_bits`: range of bits needed to represent `a`. Assumes `range_bits > 0`.
        pub fn limb_to_bits(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            range_bits: usize,
            num: &Self::Num,
            limbs: &[Self::Num], //limbs from low to high
        ) -> Result<Vec<Self::Num>, Error> {
            let mut bits_vec = Vec::new();
            for limb in limbs {
                let bits = limb.value().to_u64_limbs(range_bits, 1)
                    .into_iter()
                    .map(C::Scalar::from)
                    .collect_vec();
                bits_vec.push(bits);
            }
            let flattened_bits_vec: Vec<_> = bits_vec.into_iter().flatten().collect();
            debug_assert!(range_bits > 0);

            let (acc, bits_to_num, bit_cells) = self.inner_product_combined(
                layouter,
                NUM_CHALLENGE_BITS,
                9,
                &flattened_bits_vec,
                &self.pow_of_two_assigned[..flattened_bits_vec.len()],
            )?; 
            self.constrain_equal(layouter, num, &acc)?;
            Ok(bit_cells)
        }

        /// Constrains and returns field representation of little-endian bit vector `bits`.
        ///
        /// Assumes values of `bits` are boolean.
        /// * `bits`: slice of [QuantumCell]'s that contains bit representation in little-endian form
        pub fn bits_to_num(&self, layouter: &mut impl Layouter<C::Scalar>, bits: &[Self::Num]) -> Result<Self::Num, Error> {
            assert!((bits.len() as u32) <= C::Scalar::CAPACITY);
            let (product, _) = self.inner_product_opt(
                layouter,
                &bits.iter().map(|x| x.value()).collect_vec(),
                &self.pow_of_two_assigned[..bits.len()],
            )?;
            Ok(product)
        }    
        
        pub fn add(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
        ) -> Result<Self::Num, Error> {
            // | a | 1 | b | a + b |
            let one = self.assign_fixed(layouter, &C::Scalar::ONE, 0)?;
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
            layouter: &mut impl Layouter<C::Scalar>,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        ) -> Result<Self::NonNatNum, Error> {
            // | a | 1 | b | a + b |
            let one = self.assign_fixed(layouter, &C::Scalar::ONE, 0)?;
            let out_limbs = a.limbs.iter().zip(b.limbs.iter()).map(|(a, b)| {
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
            
            let out_native = self.add(layouter, &a.native, &b.native)?;
            let out_int_value = a.value.clone() + b.value.clone();
            Ok(NonNativeNumber::new(out_limbs, out_native, out_int_value, modulus::<C::Base>()))
        }

        pub fn sub(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
        ) -> Result<Self::Num, Error> {
            // | a - b | 1 | b | a |
            let one = self.assign_fixed(layouter, &C::Scalar::ONE, 0)?;
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
            layouter: &mut impl Layouter<C::Scalar>,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        ) -> Result<Self::NonNatNum, Error> {
            // | a - b | 1 | b | a |
            let one = self.assign_fixed(layouter, &C::Scalar::ONE, 0)?;
            let out_limbs = a.limbs.iter().zip(b.limbs.iter()).map(|(a, b)| {
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
            
            let out_native = self.sub(layouter, &a.native, &b.native)?;
            let out_int_value = a.value.clone() - b.value.clone();
            Ok(NonNativeNumber::new(out_limbs, out_native, out_int_value, modulus::<C::Base>()))
        }

        pub fn mul(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
        ) -> Result<Self::Num, Error> {
            // | a | b | 0 | a * b |
            let zero = self.assign_witness(layouter, &C::Scalar::ZERO, 0)?;                           
            let result = layouter.assign_region(
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
            layouter: &mut impl Layouter<C::Scalar>,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        ) -> Result<Self::NonNatNum, Error> {
            // | a | b | 0 | a * b |
            let k = a.limbs.len();
            let out_limbs = (0..k)
                .map(|i| {
                    self.inner_product(
                        layouter,
                        &a.limbs[..=i],
                        &b.limbs[..=i].iter().rev().cloned().collect_vec(),
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let out_native = self.mul(layouter, &a.native, &b.native)?;
            let out_int_value = a.value.clone() * b.value.clone();
            Ok(NonNativeNumber::new(out_limbs, out_native, out_int_value, modulus::<C::Base>()))
        }

        pub fn mul_add(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: &Self::Num,
            b: &Self::Num,
            c: &Self::Num,
        ) -> Result<Self::Num, Error> {
            // | a | b | c | a * b + c |
            let result = layouter.assign_region(
                || "mul_add",
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
            layouter: &mut impl Layouter<C::Scalar>,
            num: &Self::Num,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
        ) -> Result<Self::NonNatNum, Error> {
            let out_limbs = a.limbs.iter().zip(b.limbs.iter()).map(|(a, b)| {
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

            let out_native = self.mul_add(layouter, &num,&a.native, &b.native)?;
            let out_int_value = fe_to_bigint(&num.value()) * a.value.clone() + b.value.clone();
            Ok(NonNativeNumber::new(out_limbs, out_native, out_int_value, modulus::<C::Base>()))
        }

        pub fn mul_add_base(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            a: &Self::NonNatNum,
            b: &Self::NonNatNum,
            c: &Self::NonNatNum,
        ) -> Result<Self::NonNatNum, Error> {
            let result = self.mul_base(layouter, a, b)?;
            self.add_base(layouter, &result, c)
        }

        pub fn powers(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            num: &Self::Num,
            n: usize,
        ) -> Result<Vec<Self::Num>, Error> {
            Ok(match n {
                0 => Vec::new(),
                1 => vec![self.assign_fixed(layouter, &C::Scalar::ONE, 0)?],
                2 => vec![
                    self.assign_fixed(layouter, &C::Scalar::ONE, 0)?,
                    num.clone(),
                ],
                _ => {
                    let mut powers = Vec::with_capacity(n);
                    powers.push(self.assign_fixed(layouter, &C::Scalar::ONE, 0)?);
                    powers.push(num.clone());
                    for _ in 0..n - 2 {
                        powers.push(self.mul(layouter, powers.last().unwrap(), num)?);
                    }
                    powers
                }
            })
        }

        pub fn powers_base(
            &self,
            layouter: &mut impl Layouter<C::Scalar>,
            num: &Self::NonNatNum,
            n: usize,
        ) -> Result<Vec<Self::NonNatNum>, Error> {
            Ok(match n {
                0 => Vec::new(),
                1 => vec![self.assign_fixed_base(layouter, &C::Base::ONE)?],
                2 => vec![
                    self.assign_fixed_base(layouter, &C::Base::ONE)?,
                    num.clone(),
                ],
                _ => {
                    let mut powers = Vec::with_capacity(n);
                    powers.push(self.assign_fixed_base(layouter, &C::Base::ONE)?);
                    powers.push(num.clone());
                    for _ in 0..n - 2 {
                        let power_no_mod = self.mul_base(layouter, powers.last().unwrap(), num)?;
                        powers.push(self.mod_reduce(layouter, power_no_mod)?);
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
        layouter: &mut impl Layouter<C::Scalar>,
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
        let zero = self.assign_fixed(layouter, &C::Scalar::ZERO, 0)?;
        let mut previous = None;
        for (idx, (a_limb, carry)) in a.into_iter().zip(carries).enumerate() {
            let neg_carry_val = bigint_to_fe(&-carry);
            let neg_carry_assigned = self.assign_fixed(layouter, &neg_carry_val, idx)?;
            let previous_assigned = self.mul_add(layouter, limb_base_assigned, &neg_carry_assigned, &a_limb)?;
            self.constrain_equal(layouter, &previous_assigned, previous.as_ref().unwrap_or(&zero))?;
            // i in 0..num_windows {
            // let idx = std::cmp::min(window * i + window - 1, k - 1);
            // let carry_cell = &neg_carry_assignments[idx];
            let shift_val_assigned = self.assign_fixed(layouter, &shift_val, idx)?;
            let shifted_carry = self.add(layouter, &neg_carry_assigned, &shift_val_assigned)?;
            self.range_check_chip.assign(layouter, &shifted_carry, range_bits + 1)?;

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
        layouter: &mut impl Layouter<C::Scalar>,
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
            let new_quot_cell = self.assign_witness(layouter, &quot_v, i)?;
            let mod_vec_assigned: Result<Vec<_>, _> = mod_limbs[..=i]
                .iter()
                .rev()
                .enumerate()
                .map(|(index, c)| self.assign_fixed(layouter, c, index))
                .collect();

            let prod = self.inner_product(
                layouter,
                quot_assigned.iter().chain(iter::once(&new_quot_cell)).cloned().collect_vec().as_slice(),
                &mod_vec_assigned?,
            )?;

            // perform step 2: compute prod - a + out
            let temp1 = prod.value() - a_limb.value();
            let temp1_assigned = self.assign_witness(layouter, &temp1, i)?;
            let check_val = temp1 + out_v;
            let out_val_assigned = self.assign_witness(layouter, &out_v, i)?;
            let check_val_assigned = self.assign_witness(layouter, &check_val, i)?;

            // can be written as one gate
            // transpose of:
            // | prod | -1 | a | prod - a | 1 | out | prod - a + out
            // where prod is at relative row `offset`
            let prod_minus_a = self.sub(layouter, &prod, &a_limb)?;
            self.constrain_equal(layouter, &prod_minus_a, &temp1_assigned)?;
            let prod_minus_a_plus_out = self.add(layouter, &prod_minus_a, &out_val_assigned)?;
            self.constrain_equal(layouter, &prod_minus_a_plus_out, &check_val_assigned)?;

            quot_assigned.push(new_quot_cell);
            out_assigned.push(out_val_assigned);
            check_assigned.push(check_val_assigned);
        }

        // range check limbs of `out` are in [0, 2^n) except last limb should be in [0, 2^out_last_limb_bits)
        for (out_index, out_cell) in out_assigned.iter().enumerate() {
            let limb_bits = if out_index == k - 1 { out_last_limb_bits } else { n };
            self.range_check_chip.assign(layouter, out_cell, limb_bits)?;
        }

        // range check that quot_cell in quot_assigned is in [-2^n, 2^n) except for last cell check it's in [-2^quot_last_limb_bits, 2^quot_last_limb_bits)
        for (q_index, quot_cell) in quot_assigned.iter().enumerate() {
            let limb_bits = if q_index == k - 1 { quot_last_limb_bits } else { n };
            let limb_base =
                if q_index == k - 1 { self.pow_of_two[limb_bits] } else { limb_bases[1] };
            let limb_base_assigned = self.assign_fixed(layouter, &limb_base, q_index)?;
            // compute quot_cell + 2^n and range check with n + 1 bits
            let quot_shift = self.add(layouter, quot_cell, &limb_base_assigned)?;
            self.range_check_chip.assign(layouter, &quot_shift, limb_bits + 1)?;
        }

        // using const NUM_LIMB_BITS_NON_NATIVE as max_limb_bits for each nonnative limb, since we dont do mod reduce for primary nonnative limbs
        let max_limb_bits = max(max(num_limb_bits, NUM_LIMB_BITS_NON_NATIVE) + 1, 2 * n + num_limbs);

        let limb_bases_assigned = limb_bases.iter().enumerate().map(|(index, c)| self.assign_fixed(layouter, c, index)).collect::<Result<Vec<_>, _>>()?;
        // check that `out - a + modulus * quotient == 0 mod 2^{trunc_len}` after carry
        self.truncate(
            layouter,
            check_assigned,
            num_limb_bits,
            &limb_bases_assigned[1],
            &limb_base_big,
            max_limb_bits,
        )?;

        // Constrain `quot_native = sum_i quot_assigned[i] * 2^{n*i}` in `F`
        let quot_native = self.inner_product(layouter, &quot_assigned, &limb_bases_assigned)?;

        // Constrain `out_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
        let out_native = self.inner_product(layouter, &out_assigned, &limb_bases_assigned)?;
        // We can save 1 cell by connecting `out_native` computation with the following:

        // todo write as one gate mul_add_constrain
        // Check `out + modulus * quotient - a = 0` in native field
        let mod_native_assigned = self.assign_fixed(layouter, &mod_native, 0)?;
        let mul_add_result = self.mul_add(layouter, &mod_native_assigned, &quot_native, &out_native)?;
        self.constrain_equal(layouter, &mul_add_result, &a.native)?;
        Ok(NonNativeNumber::new(out_assigned, out_native, out_val, modulus::<C::Base>()))
    }
}

#[derive(Clone, Debug)]
pub struct MainChipCircuitConfig {
    pub main_config: MainChipConfig,
    pub range_check_config: RangeCheckConfig,
}
pub struct MainChipCircuit<C> {
    marker: PhantomData<C>,
}

impl<C> Circuit<C::Scalar> for MainChipCircuit<C> 
where
    C: TwoChainCurve,
    C::Scalar: BigPrimeField + PrimeFieldBits,
    C::Base: BigPrimeField + PrimeFieldBits,
{

    type Params = ();
    type Config = MainChipCircuitConfig; 
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            marker: PhantomData::<C>,
        }
    }

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {

        let main_advice = (0..NUM_MAIN_ADVICE).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let main_fixed = (0..NUM_MAIN_FIXED).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        for col in &main_advice {
            meta.enable_equality(*col)
        }

        for col in &main_fixed {
            meta.enable_constant(*col)
        }

        let main_config = MainChip::<C>::configure(meta, main_advice.clone().try_into().unwrap(), main_fixed.try_into().unwrap());
        let range_check_fixed = meta.fixed_column();
        meta.enable_constant(range_check_fixed);
        // we need 1 complex selector for the lookup check in the range check chip
        let enable_lookup_selector = meta.complex_selector();
        let range_check_config = RangeCheckChip::<C>::configure(
            meta,
            main_advice[NUM_MAIN_ADVICE - 1], //range_advice.try_into().unwrap(),
            range_check_fixed,
            enable_lookup_selector,
        );

        Self::Config {
            main_config,
            range_check_config,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Scalar>,
    ) -> Result<(), Error> {

        let range_chip = RangeCheckChip::<C>::construct(config.range_check_config);
        let mut main_chip = MainChip::<C>::new(config.main_config.clone(), range_chip);
        main_chip.initialize(&mut layouter)?;
        main_chip.load_range_check_table(&mut layouter, config.range_check_config.lookup_u8_table)?;

        /// test inner product
        // let mut rng = OsRng;
        // let a = (0..10).map(|_| C::Scalar::from(1)).collect::<Vec<_>>();
        // let b = (0..10).map(|_| C::Scalar::from(1)).collect::<Vec<_>>();

        // let a_assigned = main_chip.assign_witnesses(&mut layouter, a.as_slice())?;
        // let b_assigned = main_chip.assign_witnesses(&mut layouter, b.as_slice())?;

        // let result = main_chip.inner_product_opt(&mut layouter, &a_assigned, &b_assigned)?;

        // let inner_product_value = 
        //     a.iter().zip(b.iter()).fold(
        //         C::Scalar::ZERO,
        //         |acc, (a, b)| {
        //             acc + *a * *b
        //     });

        // let inner_product_assigned = main_chip.assign_witness(&mut layouter, &inner_product_value, 0)?;
        // main_chip.constrain_equal(&mut layouter, &result, &inner_product_assigned)?;

        /// test num_to_bits + bits_to_num, Witness count: 594 + 577 + 254(pow2 copy) = 1425
        // let mut rng = OsRng;
        // let a = C::Scalar::random(&mut rng);
        // let a_assigned = main_chip.assign_witness(&mut layouter, &a, 0)?;
        // let bits = main_chip.num_to_bits(&mut layouter, RANGE_BITS, &a_assigned)?;
        // let num = main_chip.bits_to_num(&mut layouter, &bits[..NUM_HASH_BITS])?;

        // /// test bits_and_num, Witness count: 594 + 254(pow2 copy) = 828
        // let mut rng = OsRng;
        // let a = C::Scalar::random(&mut rng);
        // let a_assigned = main_chip.assign_witness(&mut layouter, &a, 0)?;
        // let bits = main_chip.bits_and_num(&mut layouter, RANGE_BITS, NUM_CHALLENGE_BITS, 10, &a_assigned)?;
        // // let num = main_chip.bits_to_num(&mut layouter, &bits[..NUM_HASH_BITS])?;
        
        /// test bits_and_num_LIMBS, Witness count: 597 + 128(bits copy) = 597
        let mut rng = OsRng;
        let a = C::Scalar::random(&mut rng);
        let a_assigned = main_chip.assign_witness(&mut layouter, &a, 0)?;
        let bits = main_chip.bits_and_num_limbs(&mut layouter, RANGE_BITS, NUM_CHALLENGE_BITS, 9, &a_assigned)?;
        // let num = main_chip.bits_to_num(&mut layouter, &bits[..NUM_HASH_BITS])?;

        /// test assign_witness_base and mod_reduce, Witness count: 349
        // let mut rng = OsRng;
        // let a = C::Base::from_str_vartime("19834382608297447889961323302677467055070110053155139740545148874538063289754").unwrap();
        // let a_assigned = main_chip.assign_witness_base(&mut layouter, a)?;
        // let power_no_mod = main_chip.mul_base(&mut layouter, &a_assigned, &a_assigned)?;
        // let power_no_mod_reduced = main_chip.mod_reduce(&mut layouter, power_no_mod)?;

        /// test inner_product_base: vec.len = 10, Witness count: 1200
        // let mut rng = OsRng;
        // let a = (0..10).map(|_| C::Base::random(&mut rng)).collect::<Vec<_>>();
        // let b = (0..10).map(|_| C::Base::random(&mut rng)).collect::<Vec<_>>();
        // let a_assigned = a.iter().map(|x| main_chip.assign_witness_base(&mut layouter, *x).unwrap()).collect_vec();
        // let b_assigned = b.iter().map(|x| main_chip.assign_witness_base(&mut layouter, *x).unwrap()).collect_vec();
        // let result_no_mod = main_chip.inner_product_base(&mut layouter, &a_assigned, &b_assigned)?;
        // let result_no_mod_reduced = main_chip.mod_reduce(&mut layouter, result_no_mod)?;

        Ok(())
    }
}

#[test]
fn circuit_test() {
    let k = 10;
    let circuit = MainChipCircuit::<bn256::G1Affine>{ marker: PhantomData::<bn256::G1Affine> };
    let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();
    println!("Witness count: {}", prover.witness_count);
    prover.assert_satisfied();
    // assert_eq!(prover.verify(), Ok(()));
}

#[test]
fn circuit_test_layout() {
    use plotters::prelude::*;
    let root = BitMapBackend::new("MainChip_debug.png", (1024, 768)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("Main Chip Layout", ("sans-serif", 60))
        .unwrap();

    let k = 11;
    let circuit = MainChipCircuit::<bn256::G1Affine>{ marker: PhantomData::<bn256::G1Affine> };
    MockProver::run(k, &circuit, vec![vec![]]).unwrap().assert_satisfied();
    // let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    // assert_eq!(prover.verify(), Ok(()));

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