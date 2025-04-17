// Copyright © 2023 Phil Milewski, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`PolyOverZ`] values.

use super::super::PolyOverZ;
use crate::{
    integer_mod_q::PolynomialRingZq,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::{fmpz_poly::fmpz_poly_sub, fq::fq_sub};
use std::ops::Sub;

impl Sub for &PolyOverZ {
    type Output = PolyOverZ;
    /// Implements the [`Sub`] trait for two [`PolyOverZ`] values.
    /// [`Sub`] is implemented for any combination of [`PolyOverZ`] and borrowed [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the result of the subtraction of both polynomials as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
    /// let b: PolyOverZ = PolyOverZ::from_str("5  1 2 -3 0 8").unwrap();
    ///
    /// let c: PolyOverZ = &a - &b;
    /// let d: PolyOverZ = a - b;
    /// let e: PolyOverZ = &c - d;
    /// let f: PolyOverZ = c - &e;
    /// ```
    fn sub(self, other: Self) -> Self::Output {
        let mut out = PolyOverZ::default();
        unsafe {
            fmpz_poly_sub(&mut out.poly, &self.poly, &other.poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverZ, PolyOverZ, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverZ, PolyOverZ, PolyOverZ);

impl Sub<&PolynomialRingZq> for &PolyOverZ {
    type Output = PolynomialRingZq;
    /// Implements the [`Sub`] trait for [`PolyOverZ`] and [`PolynomialRingZq`].
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the subtraction of both polynomials as a [`PolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let a = PolynomialRingZq::from((&poly, &modulus));
    /// let b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    ///
    /// let c: PolynomialRingZq = &b - &a;
    /// ```
    fn sub(self, other: &PolynomialRingZq) -> Self::Output {
        let mut out = PolynomialRingZq::from((&PolyOverZ::default(), &other.modulus));
        unsafe {
            fq_sub(
                &mut out.poly.poly,
                &self.poly,
                &other.poly.poly,
                other.modulus.get_fq_ctx(),
            );
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverZ, PolynomialRingZq, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverZ, PolynomialRingZq, PolynomialRingZq);

#[cfg(test)]
mod test_sub {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Testing subtraction for two [`PolyOverZ`]
    #[test]
    fn sub() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a - b;
        assert_eq!(c, PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// Testing subtraction for two borrowed [`PolyOverZ`]
    #[test]
    fn sub_borrow() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a - &b;
        assert_eq!(c, PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// Testing subtraction for borrowed [`PolyOverZ`] and [`PolyOverZ`]
    #[test]
    fn sub_first_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a - b;
        assert_eq!(c, PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// Testing subtraction for [`PolyOverZ`] and borrowed [`PolyOverZ`]
    #[test]
    fn sub_second_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a - &b;
        assert_eq!(c, PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// Testing subtraction with eliminating coefficients
    #[test]
    fn sub_eliminating_coefficients() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let c: PolyOverZ = a - b;
        assert_eq!(c, PolyOverZ::default());
    }

    /// Testing subtraction for large [`PolyOverZ`]
    #[test]
    fn sub_large_numbers() {
        let a: PolyOverZ =
            PolyOverZ::from_str(&format!("3  {} {} {}", u32::MAX, i32::MIN, i32::MAX)).unwrap();
        let b: PolyOverZ = PolyOverZ::from_str(&format!("2  {} {}", u32::MAX, i32::MAX)).unwrap();
        let c: PolyOverZ = a - b;
        assert_eq!(
            c,
            PolyOverZ::from_str(&format!(
                "3  0 {} {}",
                i64::from(i32::MIN) * 2 + 1,
                i32::MAX
            ))
            .unwrap()
        );
    }
}

#[cfg(test)]
mod test_sub_poly_ring_zq {
    use super::PolynomialRingZq;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Checks if polynomial subtraction works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 =
            PolynomialRingZq::from_str(&format!("2  2 {} / 4  1 2 3 4 mod {}", i64::MAX, u64::MAX))
                .unwrap();
        let poly_2 = PolynomialRingZq::from_str(&format!(
            "2  -1 -{} / 4  1 2 3 4 mod {}",
            i64::MAX as u64 - 2,
            u64::MAX
        ))
        .unwrap();
        let poly = PolyOverZ::from_str("2  1 2").unwrap();

        let poly_1 = &poly - &poly_1;

        assert_eq!(poly_2, poly_1);
    }

    /// Checks if subtraction works fine for different types
    #[test]
    fn availability() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let z = PolyOverZ::from(2);

        _ = z.clone() - poly.clone();
        _ = &z - &poly;
        _ = z.clone() - &poly;
        _ = &z - poly.clone();
    }
}
