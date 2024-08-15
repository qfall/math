// Copyright © 2023 Phil Milewski
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
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_sub;
use std::{ops::Sub, str::FromStr};

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
    ///     both [`PolyOverZq`] mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<PolyOverZq, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                "Tried to subtract polynomial with modulus '{}' and polynomial with modulus '{}'.
            If the modulus should be ignored please convert into a PolyOverZ beforehand.",
                self.modulus, other.modulus
            )));
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

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverZq, PolyOverZq, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverZq, PolyOverZq, PolyOverZq);

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
