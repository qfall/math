// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`PolyOverZ`] values.

use super::super::PolyOverZ;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpz_poly::fmpz_poly_mul;
use std::ops::Mul;

impl Mul for &PolyOverZ {
    type Output = PolyOverZ;
    /// Implements the [`Mul`] trait for two [`PolyOverZ`] values.
    /// [`Mul`] is implemented for any combination of [`PolyOverZ`] and borrowed [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both polynomials as a [`PolyOverZ`].
    ///
    /// # Example
    /// ```
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
    /// let b: PolyOverZ = PolyOverZ::from_str("5  1 2 -3 0 8").unwrap();
    ///
    /// let c: PolyOverZ = &a * &b;
    /// let d: PolyOverZ = a * b;
    /// let e: PolyOverZ = &c * d;
    /// let f: PolyOverZ = c * &e;
    /// ```
    fn mul(self, other: Self) -> Self::Output {
        let mut out = PolyOverZ::default();
        unsafe {
            fmpz_poly_mul(&mut out.poly, &self.poly, &other.poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZ, PolyOverZ, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZ, PolyOverZ, PolyOverZ);

#[cfg(test)]
mod test_mul {

    use super::PolyOverZ;
    use std::str::FromStr;

    /// testing multiplication for two [`PolyOverZ`]
    #[test]
    fn mul() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a * b;
        assert!(c == PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// testing multiplication for two borrowed [`PolyOverZ`]
    #[test]
    fn mul_borrow() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a * &b;
        assert!(c == PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// testing multiplication for borrowed [`PolyOverZ`] and [`PolyOverZ`]
    #[test]
    fn mul_first_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a * b;
        assert!(c == PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// testing multiplication for [`PolyOverZ`] and borrowed [`PolyOverZ`]
    #[test]
    fn mul_second_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a * &b;
        assert!(c == PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// testing multiplication with a constant [`PolyOverZ`]
    #[test]
    fn mul_constant() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("1  4").unwrap();
        let c: PolyOverZ = a * b;
        assert!(c == PolyOverZ::from_str("3  4 8 -12").unwrap());
    }

    /// testing multiplication with zero
    #[test]
    fn mul_zero() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("0").unwrap();
        let c: PolyOverZ = a * b;
        assert!(c == PolyOverZ::from_str("0").unwrap());
    }

    /// testing multiplication for large [`PolyOverZ`]
    #[test]
    fn mul_large_numbers() {
        let a: PolyOverZ = PolyOverZ::from_str(&format!("2  {} {}", u16::MAX, i32::MIN)).unwrap();
        let b: PolyOverZ = PolyOverZ::from_str(&format!("2  {} {}", u32::MAX, i32::MAX)).unwrap();
        let c: PolyOverZ = a * b;
        assert!(
            c == PolyOverZ::from_str(&format!(
                "3  {} {} {}",
                i64::from(u16::MAX) * i64::from(u32::MAX),
                i64::from(u16::MAX) * i64::from(i32::MAX)
                    + i64::from(u32::MAX) * i64::from(i32::MIN),
                i64::from(i32::MAX) * i64::from(i32::MIN)
            ))
            .unwrap()
        );
    }
}
