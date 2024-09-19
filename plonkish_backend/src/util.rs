pub mod arithmetic;
pub mod code;
pub mod expression;
pub mod hash;
pub mod parallel;
mod timer;
pub mod transcript;
pub mod expression_new;

use halo2_proofs::halo2curves::group::{Curve, Group};
pub use itertools::{chain, izip, Itertools};
pub use num_bigint::BigUint;
pub use serde::{de::DeserializeOwned, Deserialize, Deserializer, Serialize, Serializer};
pub use timer::{end_timer, start_timer, start_unit_timer};

pub fn sum_and_reduce_bases<T: Clone + std::ops::Add<Output = T> + Default + PartialEq>(vec: &[T], index_groups: &[Vec<usize>]) -> Vec<T> {
    let mut result: Vec<Option<T>> = vec.iter().map(|_| None).collect();
    let mut summed_indices = vec![false; vec.len()];

    for group in index_groups {
        if let Some(&min_index) = group.iter().min() {
            let sum: T = group.iter().fold(T::default(), |acc, &idx| {
                if idx < vec.len() { acc + vec[idx].clone() } else { acc }
            });

            result[min_index] = Some(sum);

            for &idx in group {
                if idx < vec.len() {
                    summed_indices[idx] = true;
                }
            }
        }
    }

    // Fill in the unsummed elements.
    for (idx, val) in vec.iter().enumerate() {
        if !summed_indices[idx] {
            result[idx] = Some(val.clone());
        }
    }

    // Remove None values and unwrap the Some values.
    result.into_iter().filter_map(|x| x).collect()
}

pub fn reduce_scalars<F: Clone + Default + std::cmp::PartialEq>(scalars: &[F], index_groups: &[Vec<usize>]) -> Vec<F> {
    let mut result: Vec<Option<F>> = scalars.iter().map(|_| None).collect();
    let mut used_indices = vec![false; scalars.len()];

    // Process index groups
    for group in index_groups {
        if let Some(&first_idx) = group.first() {
            if first_idx < scalars.len() {
                result[first_idx] = Some(scalars[first_idx].clone());
                for &idx in group {
                    if idx < scalars.len() {
                        used_indices[idx] = true;
                    }
                }
            }
        }
    }

    // Fill in unused scalars
    for (idx, scalar) in scalars.iter().enumerate() {
        if !used_indices[idx] {
            result[idx] = Some(scalar.clone());
        }
    }

    // Remove default values and reorder
    result.into_iter().filter_map(|x| x).collect()
}

#[test]
fn test_reduce_scalars() {
    use crate::util::arithmetic::Field;
    use halo2_proofs::halo2curves::bn256::Fr as F;

    let scalars: Vec<F> = (0..10).map(|i| F::from(i as u64)).collect();
    let index_groups = vec![
        vec![2, 7, 8],
        vec![4, 6],
        vec![3, 5],
    ];

    let result = reduce_scalars(&scalars, &index_groups);
    
    let expected: Vec<F> = vec![0, 1, 2, 3, 4, 9].into_iter().map(F::from).collect();
    assert_eq!(result, expected);
}

#[test]
fn sum_bases() {
    let vec = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    let index_groups = vec![
        vec![2, 7, 8],
        vec![4, 6],
        vec![3, 5],
    ];

    let result = sum_and_reduce_bases(&vec, &index_groups);
    println!("{:?}", result);
}  

macro_rules! izip_eq {
    (@closure $p:pat => $tup:expr) => {
        |$p| $tup
    };
    (@closure $p:pat => ($($tup:tt)*) , $_iter:expr $(, $tail:expr)*) => {
        $crate::util::izip_eq!(@closure ($p, b) => ($($tup)*, b) $(, $tail)*)
    };
    ($first:expr $(,)*) => {
        itertools::__std_iter::IntoIterator::into_iter($first)
    };
    ($first:expr, $second:expr $(,)*) => {
        $crate::util::izip_eq!($first).zip_eq($second)
    };
    ($first:expr $(, $rest:expr)* $(,)*) => {
        $crate::util::izip_eq!($first)
            $(.zip_eq($rest))*
            .map($crate::util::izip_eq!(@closure a => (a) $(, $rest)*))
    };
}

pub trait BitIndex {
    fn nth_bit(&self, nth: usize) -> bool;
}

impl BitIndex for usize {
    fn nth_bit(&self, nth: usize) -> bool {
        (self >> nth) & 1 == 1
    }
}

macro_rules! impl_index {
    (@ $name:ty, $field:tt, [$($range:ty => $output:ty),*$(,)?]) => {
        $(
            impl<F> std::ops::Index<$range> for $name {
                type Output = $output;

                fn index(&self, index: $range) -> &$output {
                    self.$field.index(index)
                }
            }

            impl<F> std::ops::IndexMut<$range> for $name {
                fn index_mut(&mut self, index: $range) -> &mut $output {
                    self.$field.index_mut(index)
                }
            }
        )*
    };
    (@ $name:ty, $field:tt) => {
        impl_index!(
            @ $name, $field,
            [
                usize => F,
                std::ops::Range<usize> => [F],
                std::ops::RangeFrom<usize> => [F],
                std::ops::RangeFull => [F],
                std::ops::RangeInclusive<usize> => [F],
                std::ops::RangeTo<usize> => [F],
                std::ops::RangeToInclusive<usize> => [F],
            ]
        );
    };
    ($name:ident, $field:tt) => {
        impl_index!(@ $name<F>, $field);
    };
}

pub(crate) use {impl_index, izip_eq};

//#[cfg(any(test, feature = "benchmark"))]
pub mod test {
    use crate::util::arithmetic::Field;
    use rand::{
        rngs::{OsRng, StdRng},
        CryptoRng, RngCore, SeedableRng,
    };
    use std::{array, iter, ops::Range};

    pub fn std_rng() -> impl RngCore + CryptoRng {
        StdRng::from_seed(Default::default())
    }

    pub fn seeded_std_rng() -> impl RngCore + CryptoRng {
        StdRng::seed_from_u64(OsRng.next_u64())
    }

    pub fn rand_idx(range: Range<usize>, mut rng: impl RngCore) -> usize {
        range.start + (rng.next_u64() as usize % (range.end - range.start))
    }

    pub fn rand_array<F: Field, const N: usize>(mut rng: impl RngCore) -> [F; N] {
        array::from_fn(|_| F::random(&mut rng))
    }

    pub fn rand_vec<F: Field>(n: usize, mut rng: impl RngCore) -> Vec<F> {
        iter::repeat_with(|| F::random(&mut rng)).take(n).collect()
    }
}


