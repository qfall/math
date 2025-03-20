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
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::rational::Q;
use flint_sys::fmpq_poly::{fmpq_poly_scalar_div_fmpq, fmpq_poly_scalar_div_fmpz};
use std::ops::Div;

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
    /// let poly_2 = &poly_1 / &integer;
    /// ```
    fn div(self, scalar: &Z) -> Self::Output {
        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_scalar_div_fmpz(&mut out.poly, &self.poly, &scalar.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, PolyOverQ, Z, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Div, div, PolyOverQ, Z, PolyOverQ);

implement_for_others!(Z, PolyOverQ, Div Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

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
    /// let poly_2 = &poly_1 / &rational;
    /// ```
    fn div(self, scalar: &Q) -> Self::Output {
        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_scalar_div_fmpq(&mut out.poly, &self.poly, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Div, div, Q, PolyOverQ, PolyOverQ);

arithmetic_trait_borrowed_to_owned!(Div, div, PolyOverQ, Q, PolyOverQ);
arithmetic_trait_borrowed_to_owned!(Div, div, Q, PolyOverQ, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Div, div, PolyOverQ, Q, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Div, div, Q, PolyOverQ, PolyOverQ);

#[cfg(test)]
mod test_mul_z {
    use super::PolyOverQ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
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
    use crate::rational::{PolyOverQ, Q};
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
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

        _ = poly.clone() / q.clone();
        _ = q.clone() / poly.clone();
        _ = &poly / &q;
        _ = &q / &poly;
        _ = &poly / q.clone();
        _ = q / &poly;
    }
}
