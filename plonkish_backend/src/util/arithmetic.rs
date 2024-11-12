use crate::util::{BigUint, Itertools};
use itertools::izip;
use num_integer::Integer;
use std::{borrow::Borrow, fmt::Debug, iter, hash::Hash};

mod bh;
mod msm;

pub use bh::BooleanHypercube;
pub use bitvec::field::BitField;

pub use halo2_proofs::halo2curves::{
    group::{
        ff::{BatchInvert, Field, FromUniformBytes, PrimeField, PrimeFieldBits},
        prime::PrimeCurveAffine,
        Curve, Group},
    CurveAffine,Coordinates,CurveExt, pairing::{self, MillerLoopResult}, bn256::{self, Bn256}, grumpkin, pasta::{pallas, vesta}
    };
pub use msm::{fixed_base_msm, variable_base_msm, window_size, window_table};
use halo2_base::utils::{CurveAffineExt, ScalarField, BigPrimeField};

pub trait MultiMillerLoop: pairing::MultiMillerLoop + Debug + Sync {
    fn pairings_product_is_identity(terms: &[(&Self::G1Affine, &Self::G2Prepared)]) -> bool {
        Self::multi_miller_loop(terms)
            .final_exponentiation()
            .is_identity()
            .into()
    }
}

impl<M> MultiMillerLoop for M where M: pairing::MultiMillerLoop + Debug + Sync {}

pub trait OverridenCurveAffine: CurveAffine
where
    <Self as CurveAffine>::ScalarExt: BigPrimeField,
    <Self as CurveAffine>::Base: BigPrimeField,
{}

pub trait TwoChainCurve: OverridenCurveAffine 
where
    <Self as CurveAffine>::ScalarExt: BigPrimeField,
    <Self as CurveAffine>::Base: BigPrimeField,
{
    type Secondary: TwoChainCurve<ScalarExt = Self::Base, Base = Self::ScalarExt, Secondary = Self>;
}

impl OverridenCurveAffine for bn256::G1Affine{}
impl OverridenCurveAffine for grumpkin::G1Affine{}

impl TwoChainCurve for bn256::G1Affine 
{
    type Secondary = grumpkin::G1Affine;
}

impl TwoChainCurve for grumpkin::G1Affine 
{
    type Secondary = bn256::G1Affine;
}

pub fn horner<F: Field>(coeffs: &[F], x: &F) -> F {
    coeffs
        .iter()
        .rev()
        .fold(F::ZERO, |acc, coeff| acc * x + coeff)
}

pub fn steps<F: Field>(start: F) -> impl Iterator<Item = F> {
    steps_by(start, F::ONE)
}

pub fn steps_by<F: Field>(start: F, step: F) -> impl Iterator<Item = F> {
    iter::successors(Some(start), move |state| Some(step + state))
}

pub fn powers<F: Field>(scalar: F) -> impl Iterator<Item = F> {
    iter::successors(Some(F::ONE), move |power| Some(scalar * power))
}

pub fn squares<F: Field>(scalar: F) -> impl Iterator<Item = F> {
    iter::successors(Some(scalar), move |scalar| Some(scalar.square()))
}

pub fn product<F: Field>(values: impl IntoIterator<Item = impl Borrow<F>>) -> F {
    values
        .into_iter()
        .fold(F::ONE, |acc, value| acc * value.borrow())
}

pub fn sum<F: Field>(values: impl IntoIterator<Item = impl Borrow<F>>) -> F {
    values
        .into_iter()
        .fold(F::ZERO, |acc, value| acc + value.borrow())
}

pub fn repeat_vector<F: Clone>(vec: &[F], times: usize) -> Vec<F> {
    vec.iter().cloned().cycle().take(vec.len() * times).collect()
}

pub fn repeat_elements<F: Clone>(vec: &[F], times: usize) -> Vec<F> {
    vec.iter().flat_map(|x| std::iter::repeat(x.clone()).take(times)).collect()
}

pub fn inner_product<'a, 'b, F: Field>(
    lhs: impl IntoIterator<Item = &'a F>,
    rhs: impl IntoIterator<Item = &'b F>,
) -> F {
    lhs.into_iter()
        .zip_eq(rhs)
        .map(|(lhs, rhs)| *lhs * rhs)
        .reduce(|acc, product| acc + product)
        .unwrap_or_default()
}

pub fn barycentric_weights<F: Field>(points: &[F]) -> Vec<F> {
    let mut weights = points
        .iter()
        .enumerate()
        .map(|(j, point_j)| {
            points
                .iter()
                .enumerate()
                .filter_map(|(i, point_i)| (i != j).then(|| *point_j - point_i))
                .reduce(|acc, value| acc * &value)
                .unwrap_or(F::ONE)
        })
        .collect_vec();
    weights.iter_mut().batch_invert();
    weights
}

pub fn barycentric_interpolate<F: Field>(weights: &[F], points: &[F], evals: &[F], x: &F) -> F {
    let (coeffs, sum_inv) = {
        let mut coeffs = points.iter().map(|point| *x - point).collect_vec();
        coeffs.iter_mut().batch_invert();
        coeffs.iter_mut().zip(weights).for_each(|(coeff, weight)| {
            *coeff *= weight;
        });
        let sum_inv = coeffs.iter().fold(F::ZERO, |sum, coeff| sum + coeff);
        (coeffs, sum_inv.invert().unwrap())
    };
    inner_product(&coeffs, evals) * &sum_inv
}

pub fn modulus<F: PrimeField>() -> BigUint {
    BigUint::from_bytes_le((-F::ONE).to_repr().as_ref()) + 1u64
}

pub fn fe_from_bool<F: Field>(value: bool) -> F {
    if value {
        F::ONE
    } else {
        F::ZERO
    }
}

pub fn fe_mod_from_le_bytes<F: PrimeField>(bytes: impl AsRef<[u8]>) -> F {
    fe_from_le_bytes((BigUint::from_bytes_le(bytes.as_ref()) % modulus::<F>()).to_bytes_le())
}

pub fn fe_truncated_from_le_bytes<F: PrimeField>(bytes: impl AsRef<[u8]>, num_bits: usize) -> F {
    let mut big = BigUint::from_bytes_le(bytes.as_ref());
    (num_bits as u64..big.bits()).for_each(|idx| big.set_bit(idx, false));
    fe_from_le_bytes(big.to_bytes_le())
}

pub fn fe_from_le_bytes<F: PrimeField>(bytes: impl AsRef<[u8]>) -> F {
    let bytes = bytes.as_ref();
    let mut repr = F::Repr::default();
    assert!(bytes.len() <= repr.as_ref().len());
    repr.as_mut()[..bytes.len()].copy_from_slice(bytes);
    F::from_repr(repr).unwrap()
}

pub fn fe_to_fe<F1: PrimeField, F2: PrimeField>(fe: F1) -> F2 {
    debug_assert!(BigUint::from_bytes_le(fe.to_repr().as_ref()) <modulus::<F2>());
    let mut repr = F2::Repr::default();
    repr.as_mut().copy_from_slice(fe.to_repr().as_ref());
    F2::from_repr(repr).unwrap()
}

pub fn fe_truncated<F: PrimeField>(fe: F, num_bits: usize) -> F {
    let (num_bytes, num_bits_last_byte) = div_rem(num_bits, 8);
    let mut repr = fe.to_repr();
    repr.as_mut()[num_bytes + 1..].fill(0);
    repr.as_mut()[num_bytes] &= (1 << num_bits_last_byte) - 1;
    F::from_repr(repr).unwrap()
}

pub fn usize_from_bits_le(bits: &[bool]) -> usize {
    bits.iter()
        .rev()
        .fold(0, |int, bit| (int << 1) + (*bit as usize))
}

pub fn div_rem(dividend: usize, divisor: usize) -> (usize, usize) {
    Integer::div_rem(&dividend, &divisor)
}

pub fn div_ceil(dividend: usize, divisor: usize) -> usize {
    Integer::div_ceil(&dividend, &divisor)
}

pub fn fe_to_bits_le<F: PrimeField>(fe: F) -> Vec<F> {
    let mut fe_le_bits = Vec::new();
    for fe_byte in fe.to_repr().as_ref().to_vec() {
        for i in 0..8 {  // u64 has 64 bits
            let bit = (fe_byte >> i) & 1;  // Extract the ith bit
            fe_le_bits.push(bit);
        }
    }
    fe_le_bits.iter().map(|bit| F::from(*bit as u64)).collect_vec()
}

pub fn fe_from_bits_le<F: PrimeField>(bits: Vec<F>) -> F {
    let mut pow_of_two = Vec::with_capacity(F::NUM_BITS as usize);
    let two = F::from(2);
        pow_of_two.push(F::ONE);
        pow_of_two.push(two);
        for _ in 2..F::NUM_BITS {
            pow_of_two.push(two * pow_of_two.last().unwrap());
        }
    izip!(bits, pow_of_two)
    .map(|(bit, pow)| bit * pow)
    .sum()
}

pub fn field_integers<F: Field>() -> impl Iterator<Item = F> {
    std::iter::successors(Some(F::ZERO), |acc| Some(*acc + F::ONE))
}

// use ff::{Field, PrimeField};
// use halo2::arithmetic::best_fft;
// use halo2::halo2curves::bn256;
// use num_traits::pow;

//use super::{powers_of_omega, half_squares, inv_lagrange_prod};

pub fn into_coordinate_proj<C: CurveAffine>(ec_point: &C) -> ProjectivePoint<C::Base> {
    let coords = ec_point.coordinates().unwrap();
    let zero_proj = ProjectivePoint::identity();
    if coords.x().is_zero().into() && coords.y().is_zero().into() { 
        zero_proj
    } else { 
        ProjectivePoint::new(*coords.x(), *coords.y(), C::Base::ONE)
    }
}


pub trait FieldUtils where Self: PrimeField {
    fn scale(&self, scale: u64) -> Self;
}

impl<F> FieldUtils for F
where
    F: PrimeField + PrimeFieldBits,
{
    /// Addition chains mostly taken from https://github.com/mratsim/constantine/blob/master/constantine/math/arithmetic/finite_fields.nim#L443 
    fn scale(&self, scale: u64) -> Self {
        let mut x = *self;
        let mut acc = Self::ZERO;
        if scale > 15 {
            let mut scale = scale;
            while scale > 0 {
                if scale%2 == 1 {
                    acc += x;
                }
                x = x.double();
                scale >>= 1;
            }
            acc
        } else {
            match scale {
                0 => F::ZERO,
                1 => x,
                2 => x.double(),
                3 => {let y = x.double(); y+x},
                4 => x.double().double(),
                5 => {let y = x.double().double(); y+x},
                6 => {x = x.double(); let y = x.double(); y+x},
                7 => {let y = x.double().double().double(); y-x},
                8 => {x.double().double().double()},
                9 => {let y = x.double().double().double(); y+x},
                10 => {x = x.double(); let y = x.double().double(); y+x},
                11 => {let y = x.double().double(); y.double()+y-x},
                12 => {let y = x.double().double(); y.double()+y},
                13 => {let y = x.double().double(); y.double()+y+x},
                14 => {x=x.double(); let y = x.double().double().double(); y-x},
                15 => {let y = x.double().double().double().double(); y-x},
                _ => unreachable!(),
            }
        }
    }
}

/// Incomplete Addition in affine coordinates.
/// 
// dx = x2 - x1
// dy = y2 - y1
// x_3 * dx_sq = dy_sq - x_1 * dx_sq - x_2 * dx_sq
// y_3 * dx = dy * (x_1 - x_3) - y_1 * dx

pub fn add_aff_unequal<F: PrimeField+FieldUtils>(pt1: (F, F), pt2: (F, F)) -> (F, F) {
    let u1 = pt2.1;
    let u2 = pt1.1;
    let v1 = pt2.0;
    let v2 = pt1.0;

    // if v1 == v2 {
    //     if u1 != u2 {
    //         return (F::ZERO, F::ZERO);
    //     } else {
    //         return double_proj(pt1);
    //     }
    // }
    
    let dx = v1 - v2;
    let dy = u1 - u2;
    let dx_sq = dx * dx;
    let dy_sq = dy * dy;

    // x_3 * dx_sq = dy_sq - x_1 * dx_sq - x_2 * dx_sq
    // y_3 * dx = dy * (x_1 - x_3) - y_1 * dx
    let v3 = (dy_sq - v1*dx_sq - v2*dx_sq) * dx_sq.invert().unwrap();
    let u3 = dy * (v1 - v3) * dx.invert().unwrap() - u1;

    (v3, u3)
}

/// Incomplete Doubling in projective coordinates.
pub fn double_proj<F: PrimeField+FieldUtils>(pt: ProjectivePoint<F>) -> ProjectivePoint<F> {
    let x = pt.x;
    let y = pt.y;
    let z = pt.z;

    if y.is_zero().into() {
        return ProjectivePoint::identity();
    }

    let y_sq = y.square();
    let z_sq = z.square();

    let w = x.square().scale(3);
    let b = x*y_sq*z;
    let h = w.square() - b.scale(8);
    
    ProjectivePoint::new(h*y*z.scale(2),
    (w*(b.scale(4) - h) - z_sq*y_sq.square().scale(8)),
    (z*z_sq*y*y_sq.scale(8)))
}

/// Incomplete Addition in projective coordinates.
pub fn add_proj<F: PrimeField+FieldUtils>(pt1: ProjectivePoint<F>, pt2: ProjectivePoint<F>) -> ProjectivePoint<F> {
    let u1 = pt2.y * pt1.z;
    let u2 = pt1.y * pt2.z;
    let v1 = pt2.x * pt1.z;
    let v2 = pt1.x * pt2.z;

    if v1 == v2 {
        if u1 != u2 {
            return ProjectivePoint::identity();
        } else {
            return double_proj(pt1);
        }
    }
    
    let u = u1 - u2;
    let v = v1 - v2;
    let w = pt1.z * pt2.z;

    let vsq = v.square();
    let vcb = vsq*v;

    let a = u.square() * w - vcb - vsq*v2.scale(2);

    ProjectivePoint::new(v*a,
    (u*(vsq*v2 - a) - vcb*u2),
    vcb*w)
}

/// Incomplete Subtraction in projective coordinates.
pub fn sub_proj<F: PrimeField+FieldUtils>(pt1: ProjectivePoint<F>, pt2: ProjectivePoint<F>) -> ProjectivePoint<F> {
    let u1 = - pt2.y * pt1.z;
    let u2 = pt1.y * pt2.z;
    let v1 = pt2.x * pt1.z;
    let v2 = pt1.x * pt2.z;

    if v1 == v2 {
        if u1 != u2 {
            return ProjectivePoint::identity();
        } else {
            return double_proj(pt1);
        }
    }
    
    let u = u1 - u2;
    let v = v1 - v2;
    let w = pt1.z * pt2.z;

    let vsq = v.square();
    let vcb = vsq*v;

    let a = u.square() * w - vcb - vsq*v2.scale(2);

    ProjectivePoint::new(v*a,
    (u*(vsq*v2 - a) - vcb*u2),
    vcb*w)
}

/// Doubling of affine to projective coordinates.
pub fn double_aff_proj<F: PrimeField+FieldUtils>(pt: (F,F)) -> ProjectivePoint<F> {
    let x = pt.0;
    let y = pt.1;

    if y.is_zero().into() {
        return ProjectivePoint::identity();
    }

    let y_sq = y.square();

    let w = x.square().scale(3);
    let b = x*y_sq;
    let h = w.square() - b.scale(8);
    
    ProjectivePoint::new(h*y.scale(2),
    (w*(b.scale(4) - h) - y_sq.square().scale(8)),
    (y*y_sq.scale(8)))
}

/// Addition of affines to projective coordinates.
pub fn add_aff_proj<F: PrimeField+FieldUtils>(pt1: (F,F), pt2: (F,F)) -> ProjectivePoint<F> {
    let u1 = pt2.1;
    let u2 = pt1.1;
    let v1 = pt2.0;
    let v2 = pt1.0;

    if v1 == v2 {
        if u1 != u2 {
            return ProjectivePoint::identity();
        } else {
            return double_aff_proj(pt1);
        }
    }
    
    let u = u1 - u2;
    let v = v1 - v2;

    let vsq = v.square();
    let vcb = vsq*v;

    let a = u.square() - vcb - vsq*v2.scale(2);

    ProjectivePoint::new(v*a,
    (u*(vsq*v2 - a) - vcb*u2),
    vcb)
}

/// Subtraction in projective coordinates.
pub fn sub_aff_proj<F: PrimeField+FieldUtils>(pt1: (F,F), pt2: (F,F)) -> ProjectivePoint<F> {
    let u1 = -pt2.1;
    let u2 = pt1.1;
    let v1 = pt2.0;
    let v2 = pt1.0;

    if v1 == v2 {
        if u1 != u2 {
            return ProjectivePoint::identity();
        } else {
            return double_aff_proj(pt1);
        }
    }
    
    let u = u1 - u2;
    let v = v1 - v2;

    let vsq = v.square();
    let vcb = vsq*v;

    let a = u.square() - vcb - vsq*v2.scale(2);

    ProjectivePoint::new(v*a,
    (u*(vsq*v2 - a) - vcb*u2),
    vcb)
}

#[derive(Debug, Clone, Copy)]
pub struct ProjectivePoint<F: PrimeField> {
    pub x: F,
    pub y: F,
    pub z: F,
}

impl<F> ProjectivePoint<F> 
where F: PrimeField {
    pub fn new(x: F, y: F, z: F) -> Self {
        ProjectivePoint::<F> {
            x,
            y,
            z,
        }
    }

    pub fn identity() -> Self {
        ProjectivePoint::<F> {
            x: F::ZERO,
            y: F::ONE,
            z: F::ZERO,
        }
    }

    pub fn to_affine(&self) -> (F, F) {
        let z_inv = self.z.invert().unwrap_or(F::ZERO);
        let x = self.x * z_inv;
        let y = self.y * z_inv;
        (x, y)
    }
    
}

/// Complete Doubling in projective coordinates.
    // pt double, b = 3 for bn254
    //  x' = 2xy(y^2 - 9bz^2)
    //  y' = (y^2 - 9bz^2)(y^2 + 3bz^2) + 24*b*y^2*z^2 
    //  z' = 8y^3*z
pub fn double_proj_comp<F: PrimeField+FieldUtils>(pt: ProjectivePoint<F>) -> ProjectivePoint<F> {
    let x = pt.x;
    let y = pt.y;
    let z = pt.z;

    if y.is_zero().into() {
        return ProjectivePoint::identity();
    }

    let y_sq = y.square();
    let z_sq = z.square();
    let nine_z_sq = z_sq.scale(9);

    let x2 = x*y.scale(2)*(y_sq - nine_z_sq.scale(3)); 
    let y2 = (y_sq - nine_z_sq.scale(3))*(y_sq + nine_z_sq) + y_sq.scale(8)*nine_z_sq;
    let z2 = y_sq*y*z.scale(8);

    // Step 1: Precompute squares
    // let y_sq = y.square();       // y^2
    // let z_sq = z.square();       // z^2

    // // Step 2: Compute scaled squares
    // let twenty_seven_z_sq = z_sq.scale(27);   // 27 * z^2
    // let nine_z_sq = z_sq.scale(9);            // 9 * z^2

    // // Step 3: Compute common expressions
    // let s1 = y_sq - twenty_seven_z_sq;        // s1 = y^2 - 27 * z^2
    // let s2 = y_sq + nine_z_sq;                // s2 = y^2 + 9 * z^2
    // let s3 = y_sq * z_sq;                     // s3 = y^2 * z^2
    // let y_cubed = y * y_sq;                   // y^3
    // let z_scaled = z.scale(8);                // 8 * z

    // // Step 4: Compute x2
    // let x2 = x * y.scale(2) * s1;             // x2 = x * 2y * (y^2 - 27z^2)

    // // Step 5: Compute y2
    // let y_sq_sq = y_sq * y_sq;                // y^4
    // let s4 = s3.scale(54);                    // 54 * y^2 * z^2
    // let s5 = z_sq.square().scale(243);        // 243 * z^4
    // let y2 = y_sq_sq + s4 - s5;               // y2 = y^4 + 54y^2z^2 - 243z^4

    // // Step 6: Compute z2
    // let z2 = y_cubed * z_scaled;              // z2 = 8 * y^3 * z


    ProjectivePoint::new(x2, y2, z2)
}

/// Complete Addition in projective coordinates.
    // X_3 &= (X_1(Y_2) + X_2Y_1)(Y_1(Y_2)) - 3bZ_1Z_2) \\
    //  - (Y_1Z_2 + Y_2Z_1)(3b(X_1Z_2 + X_2Z_1)), \\
    // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) \\
    //  + (Y_1(Y_2) + 3bZ_1Z_2)(Y_1(Y_2) - 3bZ_1Z_2), \\
    // Z_3 &= (Y_1Z_2 + Y_2Z_1)(Y_1(Y_2) + 3bZ_1Z_2) \\
    //  + (X_1(Y_2) + X_2Y_1)(3X_1X_2).

pub fn add_proj_comp<F: PrimeField+FieldUtils>(pt1: ProjectivePoint<F>, pt2: ProjectivePoint<F>) -> ProjectivePoint<F> {

    let x1 = pt1.x;
    let y1 = pt1.y;
    let z1 = pt1.z;

    let x2 = pt2.x;
    let y2 = pt2.y;
    let z2 = pt2.z;

    // b = 3
    let x3 = (x1 * y2 + x2 * y1) * ((y1 * y2) - F::from(9) * z1 * z2) - (y1 * z2 + y2 * z1) * (F::from(9) * (x1 * z2 + x2 * z1));
    let y3 = (F::from(3) * x1 * x2) * (F::from(9) * (x1 * z2 + x2 * z1)) + (y1 * y2 + F::from(9) * z1 * z2) * (y1 * y2 - F::from(9) * z1 * z2);
    let z3 = (y1 * z2 + y2 * z1) * (y1 * y2 + F::from(9) * z1 * z2) + (x1 * y2 + x2 * y1) * (F::from(3) * x1 * x2);
    
    ProjectivePoint::<F> {
        x: x3,
        y: y3,
        z: z3,
    }

}


/// Complete Subtraction in projective coordinates.
    // X_3 &= (X_1(-Y_2) + X_2Y_1)(Y_1(-Y_2) - 3bZ_1Z_2) \\
    //  - (Y_1Z_2 - Y_2Z_1)(3b(X_1Z_2 + X_2Z_1)), \\
    // Y_3 &= (3X_1X_2)(3b(X_1Z_2 + X_2Z_1)) \\
    //  + (Y_1(-Y_2) + 3bZ_1Z_2)(Y_1(-Y_2) - 3bZ_1Z_2), \\
    // Z_3 &= (Y_1Z_2 - Y_2Z_1)(Y_1(-Y_2) + 3bZ_1Z_2) \\
    //  + (X_1(-Y_2) + X_2Y_1)(3X_1X_2).

pub fn sub_proj_comp<F: PrimeField+FieldUtils>(pt1: ProjectivePoint<F>, pt2: ProjectivePoint<F>) -> ProjectivePoint<F> {

    let x1 = pt1.x;
    let y1 = pt1.y;
    let z1 = pt1.z;

    let x2 = pt2.x;
    let y2 = pt2.y;
    let z2 = pt2.z;

    // b = 3
    let x3 = (x1 * -y2 + x2 * y1) * (y1 * -y2 - F::from(9) * z1 * z2) - (y1 * z2 - y2 * z1) * (F::from(9) * (x1 * z2 + x2 * z1));   
    let y3 = (F::from(3) * x1 * x2) * (F::from(9) * (x1 * z2 + x2 * z1)) + (y1 * -y2 + F::from(9) * z1 * z2) * (y1 * -y2 - F::from(9) * z1 * z2);   
    let z3 = (y1 * z2 - y2 * z1) * (y1 * -y2 + F::from(9) * z1 * z2) + (x1 * -y2 + x2 * y1) * (F::from(3) * x1 * x2);

    // Precompute common subexpressions
    // let s1 = x2 * y1 - x1 * y2;
    // let s2 = (-y1 * y2) - (z1 * z2).scale(9);
    // let s3 = y1 * z2 - y2 * z1;
    // let s4 = x1 * z2 + x2 * z1;
    // let s5 = (-y1 * y2) + (z1 * z2).scale(9);
    // let s6 = x1 * x2.scale(3); // Alternatively, x1.scale(3) * x2

    // // Compute x3, y3, and z3 using the precomputed subexpressions
    // let x3 = s1 * s2 - s3 * s4.scale(9);
    // let y3 = s6 * s4.scale(9) + s5 * s2;
    // let z3 = s3 * s5 + s1 * s6;

    
    ProjectivePoint::<F> {
        x: x3,
        y: y3,
        z: z3,
    }

}

pub fn is_identity_proj<F: PrimeField+FieldUtils>(pt: ProjectivePoint<F>) -> bool {

    let x = pt.x;
    let y = pt.y;
    let z = pt.z;

    if x.is_zero().into() && y == F::ONE && z.is_zero().into() {
        return true;
    } else {
        return false;
    }

}

pub fn is_scaled_identity_proj<F: PrimeField+FieldUtils>(pt: ProjectivePoint<F>) -> bool {

    let x = pt.x;
    let y = pt.y;
    let z = pt.z;

    if x.is_zero().into() && y != F::ONE && z.is_zero().into() {
        return true;
    } else {
        return false;
    }

}

pub fn fe_to_limbs<F1: ScalarField, F2: ScalarField>(fe: F1, num_limb_bits: usize, num_limbs: usize) -> Vec<F2> {
    fe.to_bytes_le()
        .chunks(num_limb_bits/8)
        .into_iter()
        .map(|bytes| match bytes.len() {
            1..=8 => F2::from_bytes_le(bytes),
            9..=16 => {
                let lo = &bytes[..8];
                let hi = &bytes[8..];
                F2::from_bytes_le(hi) * F2::from(2).pow_vartime([64]) + F2::from_bytes_le(lo)
            }
            _ => unimplemented!(),
        })
        .take(num_limbs)
        .collect()
}

pub fn fe_from_limbs<F1: ScalarField, F2: ScalarField>(
    limbs: &[F1],
    num_limb_bits: usize,
) -> F2 {
    limbs.iter().rev().fold(F2::ZERO, |acc, limb| {
        acc * F2::from_u128(1 << num_limb_bits) + fe_to_fe::<F1, F2>(*limb)
    })
}

pub fn into_coordinates<C: CurveAffine>(ec_point: &C) -> [C::Base; 2] {
    let coords = ec_point.coordinates().unwrap();
    [*coords.x(), *coords.y()]
}

pub fn into_proj_coordinates<C: CurveExt>(ec_point: &C) -> [C::Base; 3] {
    let coords = ec_point.jacobian_coordinates();
    [coords.0, coords.1, coords.2]
}
 