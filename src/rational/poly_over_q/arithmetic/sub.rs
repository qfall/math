// Copyright © 2023 Phil Milewski, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`PolyOverQ`] values.

use super::super::PolyOverQ;
use crate::{
    integer::PolyOverZ,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpq_poly::fmpq_poly_sub;
use std::ops::Sub;

impl Sub for &PolyOverQ {
    type Output = PolyOverQ;
    /// Implements the [`Sub`] trait for two [`PolyOverQ`] values.
    /// [`Sub`] is implemented for any combination of [`PolyOverQ`] and borrowed [`PolyOverQ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the result of the subtraction of both polynomials as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverQ = PolyOverQ::from_str("3  1/8 2/5 -3").unwrap();
    /// let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/7 -3/17 0 8/9").unwrap();
    ///
    /// let c: PolyOverQ = &a - &b;
    /// let d: PolyOverQ = a - b;
    /// let e: PolyOverQ = &c - d;
    /// let f: PolyOverQ = c - &e;
    /// ```
    fn sub(self, other: Self) -> Self::Output {
        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_sub(&mut out.poly, &self.poly, &other.poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverQ, PolyOverQ, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverQ, PolyOverQ, PolyOverQ);

impl Sub<&PolyOverZ> for &PolyOverQ {
    type Output = PolyOverQ;
    /// Implements the [`Sub`] trait for [`PolyOverQ`] and [`PolyOverZ`].
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the subtraction of both polynomials as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a = PolyOverQ::from_str("4  1/2 0 3/7 1").unwrap();
    /// let b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    ///
    /// let c: PolyOverQ = &a - &b;
    /// ```
    fn sub(self, other: &PolyOverZ) -> Self::Output {
        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_sub(&mut out.poly, &self.poly, &PolyOverQ::from(other).poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverQ, PolyOverZ, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverQ, PolyOverZ, PolyOverQ);

#[cfg(test)]
mod test_sub {
    use super::PolyOverQ;
    use crate::rational::Q;
    use std::str::FromStr;

    /// Testing subtraction for two [`PolyOverQ`]
    #[test]
    fn sub() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/9 2 -3/7").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/8 -2/9 5/7 1 2/9").unwrap();
        let c: PolyOverQ = a - b;
        assert_eq!(
            c,
            PolyOverQ::from_str("5  -1/72 20/9 -8/7 -1 -2/9").unwrap()
        );
    }

    /// Testing subtraction for two borrowed [`PolyOverQ`]
    #[test]
    fn sub_borrow() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/9 2 -3/7").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/8 -2/9 5/7 1 2/9").unwrap();
        let c: PolyOverQ = &a - &b;
        assert_eq!(
            c,
            PolyOverQ::from_str("5  -1/72 20/9 -8/7 -1 -2/9").unwrap()
        );
    }

    /// Testing subtraction for borrowed [`PolyOverQ`] and [`PolyOverQ`]
    #[test]
    fn sub_first_borrowed() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/9 2 -3/7").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/8 -2/9 5/7 1 2/9").unwrap();
        let c: PolyOverQ = &a - b;
        assert_eq!(
            c,
            PolyOverQ::from_str("5  -1/72 20/9 -8/7 -1 -2/9").unwrap()
        );
    }

    /// Testing subtraction for [`PolyOverQ`] and borrowed [`PolyOverQ`]
    #[test]
    fn sub_second_borrowed() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/9 2 -3/7").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/8 -2/9 5/7 1 2/9").unwrap();
        let c: PolyOverQ = a - &b;
        assert_eq!(
            c,
            PolyOverQ::from_str("5  -1/72 20/9 -8/7 -1 -2/9").unwrap()
        );
    }

    /// Testing subtraction with eliminating coefficients
    #[test]
    fn sub_eliminating_coefficients() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/8 2/7 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("3  1/8 2/7 -3").unwrap();
        let c: PolyOverQ = a - b;
        assert_eq!(c, PolyOverQ::default());
    }

    /// Testing subtraction for large [`PolyOverQ`]
    #[test]
    fn sub_large_numbers() {
        let a: PolyOverQ = PolyOverQ::from_str(&format!(
            "3  {} {}/{} {}",
            u64::MAX,
            i64::MIN,
            u128::MAX - 126,
            i64::MAX
        ))
        .unwrap();
        let b: PolyOverQ = PolyOverQ::from_str(&format!("2  {} {}", u64::MAX, i64::MAX)).unwrap();
        let c: PolyOverQ = a - b;

        assert!(
            c == PolyOverQ::from_str(&format!(
                "3  0 {} {}",
                (Q::from_str(&format!("{}/{}", i64::MIN, u128::MAX - 126)).unwrap()
                    - Q::from(i64::MAX)),
                i64::MAX
            ))
            .unwrap()
        );
    }
}

#[cfg(test)]
mod test_mul_poly_over_z {
    use super::PolyOverQ;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Checks if polynomial subtraction works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolyOverQ::from_str(&format!("1  1/{}", i64::MAX)).unwrap();
        let poly_2 = PolyOverZ::from_str("2  1 2").unwrap();
        let poly_cmp =
            PolyOverQ::from_str(&format!("2  {}/{} -2", -i64::MAX as i128 + 1, i64::MAX)).unwrap();

        let poly_1 = &poly_1 - &poly_2;

        assert_eq!(poly_cmp, poly_1);
    }

    /// Checks if subtraction works fine for different types
    #[test]
    fn availability() {
        let poly = PolyOverQ::from_str("3  1/2 2 3/7").unwrap();
        let z = PolyOverZ::from(2);

        _ = poly.clone() - z.clone();
        _ = &poly - &z;
        _ = &poly - z.clone();
        _ = poly.clone() - &z;
    }
}
