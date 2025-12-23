// Copyright © 2025 Marcel Luca Schmidt, Marvin Beckmann
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
};
use crate::macros::for_others::implement_for_others;
use crate::rational::Q;
use flint_sys::fmpq_poly::{
    fmpq_poly_scalar_div_fmpq, fmpq_poly_scalar_div_fmpz, fmpq_poly_scalar_div_si,
    fmpq_poly_scalar_div_ui,
};
use std::ops::{Div, DivAssign};

impl Div<&Z> for &PolyOverQ {
    type Output = PolyOverQ;
    /// Implements the [`Div`] trait for a [`PolyOverQ`] by a [`Z`] integer.
    /// [`Div`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the polynomial is divided
    ///
    /// Returns the division of `self` by `scalar` as a [`PolyOverQ`].
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
    /// &poly_1 / &integer;
    /// &poly_1 / integer;
    /// &poly_1 / 2;
    /// &poly_1 / -2;
    /// ```
    ///
    /// # Panics ...
    /// - if `scalar` is `0`.
    fn div(self, scalar: &Z) -> Self::Output {
        assert!(!scalar.is_zero(), "Tried to divide {self} by zero.");

        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_scalar_div_fmpz(&mut out.poly, &self.poly, &scalar.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, PolyOverQ, Z, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Div, div, PolyOverQ, Z, PolyOverQ);

implement_for_others!(Z, PolyOverQ, PolyOverQ, Div Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Div<&Q> for &PolyOverQ {
    type Output = PolyOverQ;
    /// Implements the [`Div`] trait for a [`PolyOverQ`] by a [`Q`] rational.
    /// [`Div`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the polynomial is divided
    ///
    /// Returns the division of `self` by `scalar` as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{PolyOverQ, Q};
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolyOverQ::from_str("4  1/2 2 3/4 4").unwrap();
    /// let rational = Q::from((2,3));
    ///
    /// &poly_1 / &rational;
    /// &poly_1 / rational;
    /// &poly_1 / 2.0_f32;
    /// &poly_1 / -2.0_f64;
    /// ```
    ///
    /// # Panics ...
    /// - if `scalar` is `0`.
    fn div(self, scalar: &Q) -> Self::Output {
        assert!(!scalar.is_zero(), "Tried to divide {self} by zero.");

        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_scalar_div_fmpq(&mut out.poly, &self.poly, &scalar.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, PolyOverQ, Q, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Div, div, PolyOverQ, Q, PolyOverQ);

implement_for_others!(Q, PolyOverQ, PolyOverQ, Div Scalar for f32 f64);

impl DivAssign<&Q> for PolyOverQ {
    /// Divides the polynomial coefficient-wise.
    ///
    /// Parameters:
    /// - `scalar`: specifies the value to multiply to `self`
    ///
    /// Divides `self` coefficient-wise by `scalar` returning a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{Q, PolyOverQ};
    /// use std::str::FromStr;
    ///
    /// let mut polyq = PolyOverQ::from_str(&format!("3  1/3 -5 99/2")).unwrap();
    /// let q = Q::from((3, 4));
    ///
    /// polyq /= &q;
    /// polyq /= q;
    /// polyq /= 2_f32;
    /// polyq /= -2_f64;
    /// ```
    ///
    /// # Panics ...
    /// - if the `scalar` is `0`.
    fn div_assign(&mut self, scalar: &Q) {
        assert!(!scalar.is_zero(), "Tried to divide {self} by zero.");

        unsafe { fmpq_poly_scalar_div_fmpq(&mut self.poly, &self.poly, &scalar.value) }
    }
}

impl DivAssign<&Z> for PolyOverQ {
    /// Documentation at [`PolyOverQ::div_assign`].
    fn div_assign(&mut self, scalar: &Z) {
        assert!(!scalar.is_zero(), "Tried to divide {self} by zero.");

        unsafe { fmpq_poly_scalar_div_fmpz(&mut self.poly, &self.poly, &scalar.value) };
    }
}

impl DivAssign<u64> for PolyOverQ {
    /// Documentation at [`PolyOverQ::div_assign`].
    fn div_assign(&mut self, scalar: u64) {
        assert!(scalar != 0, "Tried to divide {self} by zero.");

        unsafe { fmpq_poly_scalar_div_ui(&mut self.poly, &self.poly, scalar) };
    }
}

impl DivAssign<i64> for PolyOverQ {
    /// Documentation at [`PolyOverQ::div_assign`].
    fn div_assign(&mut self, scalar: i64) {
        assert!(scalar != 0, "Tried to divide {self} by zero.");

        unsafe { fmpq_poly_scalar_div_si(&mut self.poly, &self.poly, scalar) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(DivAssign, div_assign, PolyOverQ, Q);
arithmetic_assign_trait_borrowed_to_owned!(DivAssign, div_assign, PolyOverQ, Z);
arithmetic_assign_between_types!(DivAssign, div_assign, PolyOverQ, u64, u32 u16 u8);
arithmetic_assign_between_types!(DivAssign, div_assign, PolyOverQ, i64, i32 i16 i8);
arithmetic_assign_between_types!(DivAssign, div_assign, PolyOverQ, Q, f64 f32);

#[cfg(test)]
mod test_mul_z {
    use super::PolyOverQ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if scalar division works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolyOverQ::from_str(&format!("3  1 4/5 {}", (i64::MAX as u64) * 2)).unwrap();
        let poly_2 = PolyOverQ::from_str(&format!("3  1/2 2/5 {}", i64::MAX)).unwrap();
        let integer = Z::from(2);

        let poly_1 = &poly_1 / &integer;

        assert_eq!(poly_2, poly_1);
    }

    /// Checks if scalar multiplication works fine for different types
    #[test]
    fn availability() {
        let poly = PolyOverQ::from_str("3  1/2 2 3/8").unwrap();
        let z = Z::from(2);

        _ = poly.clone() / z.clone();
        _ = poly.clone() / 2i8;
        _ = poly.clone() / 2u8;
        _ = poly.clone() / 2i16;
        _ = poly.clone() / 2u16;
        _ = poly.clone() / 2i32;
        _ = poly.clone() / 2u32;
        _ = poly.clone() / 2i64;
        _ = poly.clone() / 2u64;

        _ = &poly / &z;
        _ = &poly / z.clone();
        _ = poly.clone() / &z;
        _ = &poly / 2i8;
    }
}

#[cfg(test)]
mod test_mul_q {
    use crate::{
        integer::Z,
        rational::{PolyOverQ, Q},
    };
    use std::str::FromStr;

    /// Checks if scalar division works fine for both borrowed
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

    /// Checks if scalar division works fine for different types
    #[test]
    fn availability() {
        let poly = PolyOverQ::from_str("3  1/2 2 3/7").unwrap();
        let q = Q::from((1, 2));

        _ = poly.clone() / q.clone();
        _ = &poly / &q;
        _ = &poly / q.clone();
        _ = &poly / 2.0_f32;
        _ = &poly / 2.0_f64;
    }

    /// Ensure that `div` panics if a division by `0` occurs
    #[test]
    #[should_panic]
    fn div_0() {
        let poly = PolyOverQ::from_str("3  1/2 2 3/7").unwrap();
        let integer = Z::from(0);

        let _ = &poly / &integer;
    }
}

#[cfg(test)]
mod test_div_assign {
    use crate::integer::Z;
    use crate::rational::{PolyOverQ, Q};
    use std::str::FromStr;

    /// Ensure that `div_assign` produces same output as normal division.
    #[test]
    fn consistency() {
        let mut a = PolyOverQ::from_str("3  1/2 2 3/7").unwrap();
        let b = Q::from((1, i32::MAX));
        let cmp = &a / &b;

        a /= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `div_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = PolyOverQ::from_str("3  1/2 2 3/7").unwrap();
        let b = Z::from(2);
        let c = Q::from((2, 3));

        a /= &b;
        a /= b;
        a /= &c;
        a /= c;
        a /= 1_u8;
        a /= 1_u16;
        a /= 1_u32;
        a /= 1_u64;
        a /= 1_i8;
        a /= 1_i16;
        a /= 1_i32;
        a /= 1_i64;
        a /= 1_f32;
        a /= 1_f64;
    }

    /// Ensure that `div_assign` panics if a division by 0 would occur.
    #[test]
    #[should_panic]
    fn div_0() {
        let mut a = PolyOverQ::from_str("3  1/2 2 3/7").unwrap();
        let b = Q::from((0, i32::MAX));

        a /= b;
    }
}
