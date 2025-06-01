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
    arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
    arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpz_poly::fmpz_poly_mul;
use std::ops::{Mul, MulAssign};

impl MulAssign<&PolyOverZ> for PolyOverZ {
    /// Computes the multiplication of `self` and `other` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to multiply to `self`
    ///
    /// Returns the product of both polynomials as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mut a = PolyOverZ::from_str("3  1 2 -3").unwrap();
    /// let b = PolyOverZ::from_str("5  1 2 -3 0 8").unwrap();
    ///
    /// a *= &b;
    /// a *= b;
    /// ```
    fn mul_assign(&mut self, other: &Self) {
        unsafe { fmpz_poly_mul(&mut self.poly, &self.poly, &other.poly) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, PolyOverZ, PolyOverZ);

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
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
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
mod test_mul_assign {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that `mul_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = PolyOverZ::from_str("3  -1 2 -3").unwrap();
        let b = PolyOverZ::from_str("2  5 2").unwrap();
        let cmp = PolyOverZ::from_str("4  -5 8 -11 -6").unwrap();

        a *= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `mul_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = PolyOverZ::from_str(&format!("1  {}", i32::MIN)).unwrap();
        let b = PolyOverZ::from_str(&format!("2  {} {}", i32::MAX, i32::MIN)).unwrap();
        let cmp = PolyOverZ::from_str(&format!(
            "2  {} {}",
            i32::MIN as i64 * i32::MAX as i64,
            i32::MIN as i64 * i32::MIN as i64
        ))
        .unwrap();

        a *= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `mul_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b = PolyOverZ::from_str("3  -1 -2 3").unwrap();

        a *= &b;
        a *= b;
    }
}

#[cfg(test)]
mod test_mul {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Testing multiplication for two [`PolyOverZ`]
    #[test]
    fn mul() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a * b;
        assert_eq!(c, PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// Testing multiplication for two borrowed [`PolyOverZ`]
    #[test]
    fn mul_borrow() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a * &b;
        assert_eq!(c, PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// Testing multiplication for borrowed [`PolyOverZ`] and [`PolyOverZ`]
    #[test]
    fn mul_first_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a * b;
        assert_eq!(c, PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// Testing multiplication for [`PolyOverZ`] and borrowed [`PolyOverZ`]
    #[test]
    fn mul_second_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a * &b;
        assert_eq!(c, PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// Testing multiplication with a constant [`PolyOverZ`]
    #[test]
    fn mul_constant() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from(4);
        let c: PolyOverZ = a * b;
        assert_eq!(c, PolyOverZ::from_str("3  4 8 -12").unwrap());
    }

    /// Testing multiplication with `0`
    #[test]
    fn mul_zero() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::default();
        let c: PolyOverZ = a * b;
        assert_eq!(c, PolyOverZ::default());
    }

    /// Testing multiplication for large [`PolyOverZ`]
    #[test]
    fn mul_large_numbers() {
        let a: PolyOverZ = PolyOverZ::from_str(&format!("2  {} {}", u16::MAX, i32::MIN)).unwrap();
        let b: PolyOverZ = PolyOverZ::from_str(&format!("2  {} {}", u32::MAX, i32::MAX)).unwrap();
        let c: PolyOverZ = a * b;
        assert_eq!(
            c,
            PolyOverZ::from_str(&format!(
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
