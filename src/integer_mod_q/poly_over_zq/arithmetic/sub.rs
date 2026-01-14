// Copyright © 2023 Phil Milewski, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`PolyOverZq`] values.

use super::super::PolyOverZq;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    integer_mod_q::PolynomialRingZq,
    macros::arithmetics::{
        arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
    traits::CompareBase,
};
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_sub;
use std::{
    ops::{Sub, SubAssign},
    str::FromStr,
};

impl SubAssign<&PolyOverZq> for PolyOverZq {
    /// Computes the subtraction of `self` and `other` reusing
    /// the memory of `self`.
    /// [`SubAssign`] can be used on [`PolyOverZq`] in combination with
    /// [`PolyOverZq`] and [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the difference of both polynomials modulo `q` as a [`PolyOverZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer_mod_q::PolyOverZq, integer::PolyOverZ};
    /// use std::str::FromStr;
    ///
    /// let mut a = PolyOverZq::from_str("3  1 2 3 mod 7").unwrap();
    /// let b = PolyOverZq::from_str("5  1 2 -3 0 4 mod 7").unwrap();
    /// let c = PolyOverZ::from_str("4  -1 2 5 3").unwrap();
    ///
    /// a -= &b;
    /// a -= b;
    /// a -= &c;
    /// a -= c;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli of both [`PolyOverZq`] mismatch.
    fn sub_assign(&mut self, other: &Self) {
        if !self.compare_base(other) {
            panic!("{}", self.call_compare_base_error(other).unwrap());
        }

        unsafe {
            fmpz_mod_poly_sub(
                &mut self.poly,
                &self.poly,
                &other.poly,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
    }
}
impl SubAssign<&PolyOverZ> for PolyOverZq {
    /// Documentation at [`PolyOverZq::sub_assign`].
    fn sub_assign(&mut self, other: &PolyOverZ) {
        let other = PolyOverZq::from((other, self.get_mod()));

        self.sub_assign(&other);
    }
}

arithmetic_assign_trait_borrowed_to_owned!(SubAssign, sub_assign, PolyOverZq, PolyOverZq);
arithmetic_assign_trait_borrowed_to_owned!(SubAssign, sub_assign, PolyOverZq, PolyOverZ);

impl Sub for &PolyOverZq {
    type Output = PolyOverZq;
    /// Implements the [`Sub`] trait for two [`PolyOverZq`] values.
    /// [`Sub`] is implemented for any combination of [`PolyOverZq`] and borrowed [`PolyOverZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the result of the subtraction of both polynomials as a [`PolyOverZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
    /// let b: PolyOverZq = PolyOverZq::from_str("3  5 1 1 mod 7").unwrap();
    ///
    /// let c: PolyOverZq = &a - &b;
    /// let d: PolyOverZq = a - b;
    /// let e: PolyOverZq = &c - d;
    /// let f: PolyOverZq = c - &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli of both [`PolyOverZq`] mismatch.
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverZq, PolyOverZq, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverZq, PolyOverZq, PolyOverZq);

impl Sub<&PolyOverZ> for &PolyOverZq {
    type Output = PolyOverZq;
    /// Implements the [`Sub`] trait for [`PolyOverZq`] and [`PolyOverZ`].
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
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a = PolyOverZq::from_str("4  -1 0 1 1 mod 17").unwrap();
    /// let b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    ///
    /// let c: PolyOverZq = &a - &b;
    /// ```
    fn sub(self, other: &PolyOverZ) -> Self::Output {
        let mut out = PolyOverZq::from(&self.modulus);
        unsafe {
            fmpz_mod_poly_sub(
                &mut out.poly,
                &self.poly,
                &PolyOverZq::from((other, &self.modulus)).poly,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverZq, PolyOverZ, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverZq, PolyOverZ, PolyOverZq);

impl Sub<&PolynomialRingZq> for &PolyOverZq {
    type Output = PolynomialRingZq;
    /// Implements the [`Sub`] trait for [`PolyOverZq`] and [`PolynomialRingZq`].
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the subtraction of both polynomials as a [`PolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolyOverZq, PolynomialRingZq};
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let a = PolynomialRingZq::from((&poly, &modulus));
    /// let b = PolyOverZq::from_str("4  2 0 3 1 mod 17").unwrap();
    ///
    /// let c: PolynomialRingZq = &b - &a;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli mismatch.
    fn sub(self, other: &PolynomialRingZq) -> Self::Output {
        let mut out = PolynomialRingZq::from((self, &other.modulus));
        out -= other;
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverZq, PolynomialRingZq, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverZq, PolynomialRingZq, PolynomialRingZq);

impl PolyOverZq {
    /// Implements subtraction for two [`PolyOverZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the result of the subtraction of both polynomials as a [`PolyOverZq`] or an error if the moduli
    /// mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
    /// let b: PolyOverZq = PolyOverZq::from_str("3  5 1 1 mod 7").unwrap();
    ///
    /// let c: PolyOverZq = a.sub_safe(&b).unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    ///   both [`PolyOverZq`] mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<PolyOverZq, MathError> {
        if !self.compare_base(other) {
            return Err(self.call_compare_base_error(other).unwrap());
        }
        let mut out = PolyOverZq::from_str(&format!("0 mod {}", self.modulus)).unwrap();
        unsafe {
            fmpz_mod_poly_sub(
                &mut out.poly,
                &self.poly,
                &other.poly,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_sub_assign {
    use super::PolyOverZq;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that `sub_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = PolyOverZq::from_str("3  6 2 -3 mod 7").unwrap();
        let b = PolyOverZq::from_str("5  -1 -2 -5 -1 -2 mod 7").unwrap();
        let cmp = PolyOverZq::from_str("5  0 4 2 1 2 mod 7").unwrap();

        a -= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `sub_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = PolyOverZq::from_str(&format!(
            "3  {} {} {} mod {}",
            u32::MAX,
            i32::MIN,
            i32::MAX,
            u64::MAX
        ))
        .unwrap();
        let b = PolyOverZq::from_str(&format!("2  -{} -{} mod {}", u32::MAX, i32::MAX, u64::MAX))
            .unwrap();
        let cmp = PolyOverZq::from_str(&format!(
            "3  {} -1 {} mod {}",
            u64::from(u32::MAX) * 2,
            i32::MAX,
            u64::MAX
        ))
        .unwrap();

        a -= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `sub_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = PolyOverZq::from_str("3  1 2 -3 mod 5").unwrap();
        let b = PolyOverZq::from_str("3  -1 -2 3 mod 5").unwrap();
        let c = PolyOverZ::from_str("2  -2 2").unwrap();

        a -= &b;
        a -= b;
        a -= &c;
        a -= c;
    }

    /// Ensures that mismatching moduli result in a panic.
    #[test]
    #[should_panic]
    fn mismatching_moduli() {
        let mut a: PolyOverZq = PolyOverZq::from_str("3  -5 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 4 1 mod 8").unwrap();

        a -= b;
    }
}

#[cfg(test)]
mod test_sub {
    use super::PolyOverZq;
    use std::str::FromStr;

    /// Testing subtraction for two [`PolyOverZq`]
    #[test]
    fn sub() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 6 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 5 1 mod 7").unwrap();
        let c: PolyOverZq = a - b;
        assert_eq!(c, PolyOverZq::from_str("3  0 6 5 mod 7").unwrap());
    }

    /// Testing subtraction for two borrowed [`PolyOverZq`]
    #[test]
    fn sub_borrow() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 6 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 5 1 mod 7").unwrap();
        let c: PolyOverZq = &a - &b;
        assert_eq!(c, PolyOverZq::from_str("3  0 6 5 mod 7").unwrap());
    }

    /// Testing subtraction for borrowed [`PolyOverZq`] and [`PolyOverZq`]
    #[test]
    fn sub_first_borrowed() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 6 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 5 1 mod 7").unwrap();
        let c: PolyOverZq = a - b;
        assert_eq!(c, PolyOverZq::from_str("3  0 6 5 mod 7").unwrap());
    }

    /// Testing subtraction for [`PolyOverZq`] and borrowed [`PolyOverZq`]
    #[test]
    fn sub_second_borrowed() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 6 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 5 1 mod 7").unwrap();
        let c: PolyOverZq = a - b;
        assert_eq!(c, PolyOverZq::from_str("3  0 6 5 mod 7").unwrap());
    }

    /// Testing subtraction of [`PolyOverZq`] is reducing the polynomial
    #[test]
    fn sub_reduce() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 4 -6 mod 7").unwrap();
        let c: PolyOverZq = a - b;
        assert_eq!(c, PolyOverZq::from_str("0 mod 7").unwrap());
    }

    /// Testing subtraction for large [`PolyOverZq`]
    #[test]
    fn sub_large_numbers() {
        let a: PolyOverZq = PolyOverZq::from_str(&format!(
            "3  -{} 4 {} mod {}",
            u64::MAX,
            i64::MIN,
            u64::MAX - 58
        ))
        .unwrap();
        let b: PolyOverZq = PolyOverZq::from_str(&format!(
            "3  {} 5 {} mod {}",
            i64::MIN,
            i64::MIN,
            u64::MAX - 58
        ))
        .unwrap();
        let c: PolyOverZq = a - b;
        assert_eq!(
            c,
            PolyOverZq::from_str(&format!(
                "2  {} -1 mod {}",
                i128::from(i64::MAX) - 57,
                u64::MAX - 58
            ))
            .unwrap()
        );
    }

    /// Testing subtraction for [`PolyOverZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn sub_mismatching_modulus() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 6 mod 9").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 5 1 mod 7").unwrap();
        let _c: PolyOverZq = a - b;
    }

    /// Testing whether sub_safe throws an error for mismatching moduli
    #[test]
    fn sub_safe_is_err() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 6 mod 9").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 5 1 mod 7").unwrap();
        assert!(&a.sub_safe(&b).is_err());
    }
}

#[cfg(test)]
mod test_mul_poly_over_z {
    use super::PolyOverZq;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Checks if polynomial subtraction works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolyOverZq::from_str(&format!("1  {} mod {}", i64::MAX, u64::MAX)).unwrap();
        let poly_2 = PolyOverZ::from_str("2  1 2").unwrap();
        let poly_cmp =
            PolyOverZq::from_str(&format!("2  {} -2 mod {}", i64::MAX as u64 - 1, u64::MAX))
                .unwrap();

        let poly_1 = &poly_1 - &poly_2;

        assert_eq!(poly_cmp, poly_1);
    }

    /// Checks if subtraction works fine for different types
    #[test]
    fn availability() {
        let poly = PolyOverZq::from_str("3  1 2 3 mod 17").unwrap();
        let z = PolyOverZ::from(2);

        _ = poly.clone() - z.clone();
        _ = &poly - &z;
        _ = &poly - z.clone();
        _ = poly.clone() - &z;
    }
}

#[cfg(test)]
mod test_sub_poly_ring_zq {
    use super::PolynomialRingZq;
    use crate::integer_mod_q::PolyOverZq;
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
        let poly = PolyOverZq::from_str(&format!("2  1 2 mod {}", u64::MAX)).unwrap();

        let poly_1 = &poly - &poly_1;

        assert_eq!(poly_2, poly_1);
    }

    /// Checks if subtraction works fine for different types
    #[test]
    fn availability() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let zq = PolyOverZq::from((2, 17));

        _ = zq.clone() - poly.clone();
        _ = &zq - &poly;
        _ = zq.clone() - &poly;
        _ = &zq - poly.clone();
    }

    /// Checks if subtraction panics if the moduli mismatch
    #[test]
    #[should_panic]
    fn different_moduli_panic() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let zq = PolyOverZq::from((2, 16));

        _ = &zq - &poly;
    }
}
