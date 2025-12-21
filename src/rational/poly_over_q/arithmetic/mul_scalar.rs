// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`PolyOverQ`].

use super::super::PolyOverQ;
use crate::integer::Z;
use crate::macros::arithmetics::{
    arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::rational::Q;
use flint_sys::fmpq_poly::{
    fmpq_poly_scalar_mul_fmpq, fmpq_poly_scalar_mul_fmpz, fmpq_poly_scalar_mul_si,
    fmpq_poly_scalar_mul_ui,
};
use std::ops::{Mul, MulAssign};

impl Mul<&Z> for &PolyOverQ {
    type Output = PolyOverQ;
    /// Implements the [`Mul`] trait for a [`PolyOverQ`] with a [`Z`] integer.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    /// [`Mul`] is also implemented for [`Z`] using [`PolyOverQ`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the polynomial is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{PolyOverQ, Q};
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolyOverQ::from_str("4  1/2 2 3/4 4").unwrap();
    /// let integer = Z::from(2);
    ///
    /// let poly_2 = &poly_1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_scalar_mul_fmpz(&mut out.poly, &self.poly, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Z, PolyOverQ, PolyOverQ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverQ, Z, PolyOverQ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, PolyOverQ, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverQ, Z, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, PolyOverQ, PolyOverQ);

implement_for_others!(Z, PolyOverQ, PolyOverQ, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Mul<&Q> for &PolyOverQ {
    type Output = PolyOverQ;
    /// Implements the [`Mul`] trait for a [`PolyOverQ`] with a [`Q`] rational.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    /// [`Mul`] is also implemented for [`Q`] using [`PolyOverQ`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the polynomial is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{PolyOverQ, Q};
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolyOverQ::from_str("4  1/2 2 3/4 4").unwrap();
    /// let rational = Q::from((2,3));
    ///
    /// let poly_2 = &poly_1 * &rational;
    /// ```
    fn mul(self, scalar: &Q) -> Self::Output {
        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_scalar_mul_fmpq(&mut out.poly, &self.poly, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Q, PolyOverQ, PolyOverQ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverQ, Q, PolyOverQ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Q, PolyOverQ, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverQ, Q, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Q, PolyOverQ, PolyOverQ);

implement_for_others!(Q, PolyOverQ, PolyOverQ, Mul Scalar for f32 f64);

impl MulAssign<&Q> for PolyOverQ {
    /// Computes the scalar multiplication of `self` and `other` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply to `self`
    ///
    /// Returns the scalar of the polynomial as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::rational::{PolyOverQ, Q};
    /// use std::str::FromStr;
    ///
    /// let mut a = PolyOverQ::from_str("3  1 2 -3/2").unwrap();
    /// let b = Q::from((2,5));
    /// let c = Z::from(2);
    ///
    /// a *= &b;
    /// a *= b;
    /// a *= &c;
    /// a *= c;
    /// a *= 2;
    /// a *= -2;
    /// ```
    fn mul_assign(&mut self, scalar: &Q) {
        unsafe { fmpq_poly_scalar_mul_fmpq(&mut self.poly, &self.poly, &scalar.value) };
    }
}

impl MulAssign<&Z> for PolyOverQ {
    /// Documentation at [`PolyOverQ::mul_assign`].
    fn mul_assign(&mut self, other: &Z) {
        unsafe { fmpq_poly_scalar_mul_fmpz(&mut self.poly, &self.poly, &other.value) };
    }
}

impl MulAssign<i64> for PolyOverQ {
    /// Documentation at [`PolyOverQ::mul_assign`].
    fn mul_assign(&mut self, other: i64) {
        unsafe { fmpq_poly_scalar_mul_si(&mut self.poly, &self.poly, other) };
    }
}

impl MulAssign<u64> for PolyOverQ {
    /// Documentation at [`PolyOverQ::mul_assign`].
    fn mul_assign(&mut self, other: u64) {
        unsafe { fmpq_poly_scalar_mul_ui(&mut self.poly, &self.poly, other) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, PolyOverQ, Q);
arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, PolyOverQ, Z);
arithmetic_assign_between_types!(MulAssign, mul_assign, PolyOverQ, i64, i32 i16 i8);
arithmetic_assign_between_types!(MulAssign, mul_assign, PolyOverQ, u64, u32 u16 u8);
arithmetic_assign_between_types!(MulAssign, mul_assign, PolyOverQ, Q, f64 f32);

#[cfg(test)]
mod test_mul_z {
    use super::PolyOverQ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if scalar multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolyOverQ::from_str(&format!("3  1/2 2/5 {}", i64::MAX)).unwrap();
        let poly_2 = poly_1.clone();
        let poly_3 = PolyOverQ::from_str(&format!("3  1 4/5 {}", (i64::MAX as u64) * 2)).unwrap();
        let integer = Z::from(2);

        let poly_1 = &poly_1 * &integer;
        let poly_2 = &integer * &poly_2;

        assert_eq!(poly_3, poly_1);
        assert_eq!(poly_3, poly_2);
    }

    /// Checks if scalar multiplication works fine for different types
    #[test]
    fn availability() {
        let poly = PolyOverQ::from_str("3  1/2 2 3/8").unwrap();
        let z = Z::from(2);

        _ = poly.clone() * z.clone();
        _ = poly.clone() * 2i8;
        _ = poly.clone() * 2u8;
        _ = poly.clone() * 2i16;
        _ = poly.clone() * 2u16;
        _ = poly.clone() * 2i32;
        _ = poly.clone() * 2u32;
        _ = poly.clone() * 2i64;
        _ = poly.clone() * 2u64;

        _ = z.clone() * poly.clone();
        _ = 2i8 * poly.clone();
        _ = 2u64 * poly.clone();

        _ = &poly * &z;
        _ = &z * &poly;
        _ = &poly * z.clone();
        _ = z.clone() * &poly;
        _ = &z * poly.clone();
        _ = poly.clone() * &z;
        _ = &poly * 2i8;
        _ = 2i8 * &poly;
    }
}

#[cfg(test)]
mod test_mul_q {
    use crate::rational::{PolyOverQ, Q};
    use std::str::FromStr;

    /// Checks if scalar multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolyOverQ::from_str(&format!("3  1 2 {}", (i64::MAX as u64) * 2)).unwrap();
        let poly_2 = poly_1.clone();
        let poly_3 = PolyOverQ::from_str(&format!("3  1/2 1 {}", i64::MAX)).unwrap();
        let rational = Q::from((1, 2));

        let poly_1 = &poly_1 * &rational;
        let poly_2 = &rational * &poly_2;

        assert_eq!(poly_3, poly_1);
        assert_eq!(poly_3, poly_2);
    }

    /// Checks if scalar multiplication works fine for different types
    #[test]
    fn availability() {
        let poly = PolyOverQ::from_str("3  1/2 2 3/7").unwrap();
        let q = Q::from((1, 2));

        _ = poly.clone() * q.clone();
        _ = q.clone() * poly.clone();
        _ = &poly * &q;
        _ = &q * &poly;
        _ = &poly * q.clone();
        _ = q.clone() * &poly;
        _ = &q * poly.clone();
        _ = poly.clone() * &q;
        _ = &poly * 1.0_f32;
        _ = &poly * 1.0_f64;
    }
}

#[cfg(test)]
mod test_mul_assign {
    use crate::integer::Z;
    use crate::rational::{PolyOverQ, Q};
    use std::str::FromStr;

    /// Ensure that `mul_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = PolyOverQ::from_str("3  1 2 -3/2").unwrap();
        let b = Z::from(2);
        let c = Q::from((2, 5));
        let d = Z::ZERO;

        a *= &b;
        assert_eq!(PolyOverQ::from_str("3  2 4 -3").unwrap(), a);

        a *= &c;
        assert_eq!(PolyOverQ::from_str("3  4/5 8/5 -6/5").unwrap(), a);
        a *= &d;
        assert_eq!(PolyOverQ::from(0), a);
    }

    /// Ensure that `mul_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = PolyOverQ::from_str("2  2 -1").unwrap();
        let b = Q::from((1, i32::MAX));
        let cmp =
            PolyOverQ::from_str(&format!("2  2/{} 1/{}", i32::MAX, -(i32::MAX as i64))).unwrap();

        a *= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `mul_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = PolyOverQ::from_str("3  1 2 -1/3").unwrap();
        let b = Z::from(2);
        let c = Q::from((2, 3));

        a *= &b;
        a *= b;
        a *= &c;
        a *= c;
        a *= 1_u8;
        a *= 1_u16;
        a *= 1_u32;
        a *= 1_u64;
        a *= 1_i8;
        a *= 1_i16;
        a *= 1_i32;
        a *= 1_i64;
        a *= 1.0_f32;
        a *= 1.0_f64;
    }
}
