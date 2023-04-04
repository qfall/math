// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`PolyOverQ`] values.

use super::super::PolyOverQ;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpq_poly::fmpq_poly_mul;
use std::ops::Mul;

impl Mul for &PolyOverQ {
    type Output = PolyOverQ;
    /// Implements the [`Mul`] trait for two [`PolyOverQ`] values.
    /// [`Mul`] is implemented for any combination of [`PolyOverQ`] and borrowed [`PolyOverQ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both polynomials as a [`PolyOverQ`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2/5 -3").unwrap();
    /// let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/5 -3/17 0 8/9").unwrap();
    ///
    /// let c: PolyOverQ = &a * &b;
    /// let d: PolyOverQ = a * b;
    /// let e: PolyOverQ = &c * d;
    /// let f: PolyOverQ = c * &e;
    /// ```
    fn mul(self, other: Self) -> Self::Output {
        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_mul(&mut out.poly, &self.poly, &other.poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverQ, PolyOverQ, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverQ, PolyOverQ, PolyOverQ);

#[cfg(test)]
mod test_mul {

    use super::PolyOverQ;
    use std::str::FromStr;

    /// testing multiplication for two [`PolyOverQ`]
    #[test]
    fn mul() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2/7 -3/7").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/11 2/11 5/11 1/11 2/11").unwrap();
        let c: PolyOverQ = a * b;
        assert_eq!(
            c,
            PolyOverQ::from_str("7  1/77 4/77 6/77 5/77 -11/77 1/77 -6/77").unwrap()
        );
    }

    /// testing multiplication for two borrowed [`PolyOverQ`]
    #[test]
    fn mul_borrow() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2/7 -3/7").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/11 2/11 5/11 1/11 2/11").unwrap();
        let c: PolyOverQ = &a * &b;
        assert_eq!(
            c,
            PolyOverQ::from_str("7  1/77 4/77 6/77 5/77 -11/77 1/77 -6/77").unwrap()
        );
    }

    /// testing multiplication for borrowed [`PolyOverQ`] and [`PolyOverQ`]
    #[test]
    fn mul_first_borrowed() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2/7 -3/7").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/11 2/11 5/11 1/11 2/11").unwrap();
        let c: PolyOverQ = &a * b;
        assert_eq!(
            c,
            PolyOverQ::from_str("7  1/77 4/77 6/77 5/77 -11/77 1/77 -6/77").unwrap()
        );
    }

    /// testing multiplication for [`PolyOverQ`] and borrowed [`PolyOverQ`]
    #[test]
    fn mul_second_borrowed() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2/7 -3/7").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/11 2/11 5/11 1/11 2/11").unwrap();
        let c: PolyOverQ = a * &b;
        assert_eq!(
            c,
            PolyOverQ::from_str("7  1/77 4/77 6/77 5/77 -11/77 1/77 -6/77").unwrap()
        );
    }

    /// testing multiplication with a constant [`PolyOverQ`]
    #[test]
    fn mul_constant() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/11 1/2 -7/3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("1  4/7").unwrap();
        let c: PolyOverQ = a * b;
        assert_eq!(c, PolyOverQ::from_str("3  4/77 2/7 -28/21").unwrap());
    }

    /// testing multiplication with zero
    #[test]
    fn mul_zero() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/18 2/7 -3/10").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("0").unwrap();
        let c: PolyOverQ = a * b;
        assert_eq!(c, PolyOverQ::from_str("0").unwrap());
    }

    /// testing multiplication for large [`PolyOverQ`]
    #[test]
    fn mul_large_numbers() {
        let a: PolyOverQ = PolyOverQ::from_str(&format!("2  {} {}", 2, i64::MIN)).unwrap();
        let b: PolyOverQ = PolyOverQ::from_str(&format!(
            "2  {}/{} {}/{}",
            u32::MAX,
            u128::MAX,
            i64::MAX,
            u128::MAX
        ))
        .unwrap();
        let c: PolyOverQ = a * b;

        assert_eq!(
            c,
            PolyOverQ::from_str(&format!(
                "3  {}/{} {}/{} {}/{}",
                2_u128 * u128::from(u32::MAX),
                u128::MAX,
                2_i128 * i128::from(i64::MAX) + i128::from(u32::MAX) * i128::from(i64::MIN),
                u128::MAX,
                i128::from(i64::MAX) * i128::from(i64::MIN),
                u128::MAX
            ))
            .unwrap()
        );
    }
}
