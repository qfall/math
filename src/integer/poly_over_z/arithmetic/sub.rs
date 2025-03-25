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
    integer_mod_q::PolyOverZq,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
    rational::PolyOverQ,
};
use flint_sys::{
    fmpq_poly::fmpq_poly_sub, fmpz_mod_poly::fmpz_mod_poly_sub, fmpz_poly::fmpz_poly_sub,
};
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

impl Sub<&PolyOverZq> for &PolyOverZ {
    type Output = PolyOverZq;
    /// Implements the [`Sub`] trait for [`PolyOverZ`] and [`PolyOverZq`].
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the subtraction of both polynomials as a [`PolyOverZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use qfall_math::integer_mod_q::ModulusPolyOverZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    /// let b = PolyOverZq::from_str("4  -1 0 1 1 mod 17").unwrap();
    ///
    /// let c: PolyOverZq = &a - &b;
    /// ```
    fn sub(self, other: &PolyOverZq) -> Self::Output {
        let mut out = PolyOverZq::from(&other.modulus);
        unsafe {
            fmpz_mod_poly_sub(
                &mut out.poly,
                &PolyOverZq::from((self, &other.modulus)).poly,
                &other.poly,
                other.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverZ, PolyOverZq, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverZ, PolyOverZq, PolyOverZq);

impl Sub<&PolyOverQ> for &PolyOverZ {
    type Output = PolyOverQ;
    /// Implements the [`Sub`] trait for [`PolyOverZ`] and [`PolyOverQ`].
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the subtraction of both polynomials as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverQ;
    /// use qfall_math::integer_mod_q::ModulusPolyOverQ;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    /// let b = PolyOverQ::from_str("4  1/2 0 3/7 1").unwrap();
    ///
    /// let c: PolyOverQ = &a - &b;
    /// ```
    fn sub(self, other: &PolyOverQ) -> Self::Output {
        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_sub(&mut out.poly, &PolyOverQ::from(self).poly, &other.poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverZ, PolyOverQ, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverZ, PolyOverQ, PolyOverQ);

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
mod test_mul_poly_over_zq {
    use super::PolyOverZq;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Checks if polynomial subtraction works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolyOverZ::from_str("2  1 2").unwrap();
        let poly_2 = PolyOverZq::from_str(&format!("1  {} mod {}", i64::MAX, u64::MAX)).unwrap();

        let poly_cmp =
            PolyOverZq::from_str(&format!("2  {} 2 mod {}", -i64::MAX as u64 + 1, u64::MAX))
                .unwrap();

        let poly_1 = &poly_1 - &poly_2;

        assert_eq!(poly_cmp, poly_1);
    }

    /// Checks if subtraction works fine for different types
    #[test]
    fn availability() {
        let poly = PolyOverZq::from_str("3  1 2 3 mod 17").unwrap();
        let z = PolyOverZ::from(2);

        _ = z.clone() - poly.clone();
        _ = &z - &poly;
        _ = z.clone() - &poly;
        _ = &z - poly.clone();
    }
}

#[cfg(test)]
mod test_mul_poly_over_q {
    use super::PolyOverQ;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Checks if polynomial subtraction works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolyOverZ::from_str("2  1 2").unwrap();
        let poly_2 = PolyOverQ::from_str(&format!("1  1/{}", i64::MAX)).unwrap();
        let poly_cmp =
            PolyOverQ::from_str(&format!("2  {}/{} 2", i64::MAX as i128 - 1, i64::MAX)).unwrap();

        let poly_1 = &poly_1 - &poly_2;

        assert_eq!(poly_cmp, poly_1);
    }

    /// Checks if subtraction works fine for different types
    #[test]
    fn availability() {
        let poly = PolyOverQ::from_str("3  1/2 2 3/7").unwrap();
        let z = PolyOverZ::from(2);

        _ = z.clone() - poly.clone();
        _ = &z - &poly;
        _ = z.clone() - &poly;
        _ = &z - poly.clone();
    }
}
