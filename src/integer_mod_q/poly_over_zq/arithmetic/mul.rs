// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`PolyOverZq`] values.

use super::super::PolyOverZq;
use crate::{
    error::MathError,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_mul;
use std::{ops::Mul, str::FromStr};

impl Mul for &PolyOverZq {
    type Output = PolyOverZq;
    /// Implements the [`Mul`] trait for two [`PolyOverZq`] values.
    /// [`Mul`] is implemented for any combination of [`PolyOverZq`] and borrowed [`PolyOverZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to multiply with `self`
    ///
    /// Returns the product of both polynomials as a [`PolyOverZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
    /// let b: PolyOverZq = PolyOverZq::from_str("3  5 1 1 mod 7").unwrap();
    ///
    /// let c: PolyOverZq = &a * &b;
    /// let d: PolyOverZq = a * b;
    /// let e: PolyOverZq = &c * d;
    /// let f: PolyOverZq = c * &e;
    /// ```
    ///
    /// # Panics ...
    /// - ... if the moduli of both [`PolyOverZq`] mismatch.
    fn mul(self, other: Self) -> Self::Output {
        self.mul_safe(other).unwrap()
    }
}

impl PolyOverZq {
    /// Implements multiplication for two [`PolyOverZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to multiply to `self`
    ///
    /// Returns the product of both polynomials as a [`PolyOverZq`] or an error if the moduli
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
    /// let c: PolyOverZq = a.mul_safe(&b).unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    /// both [`PolyOverZq`] mismatch.
    pub fn mul_safe(&self, other: &Self) -> Result<PolyOverZq, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to add polynomial with modulus '{}' and polynomial with modulus '{}'.
            If the modulus should be ignored please convert into a PolyOverZ beforehand.",
                self.modulus, other.modulus
            )));
        }
        let mut out = PolyOverZq::from_str(&format!("0 mod {}", self.modulus)).unwrap();
        unsafe {
            fmpz_mod_poly_mul(
                &mut out.poly,
                &self.poly,
                &other.poly,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZq, PolyOverZq, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZq, PolyOverZq, PolyOverZq);

#[cfg(test)]
mod test_mul {
    use super::PolyOverZq;
    use std::str::FromStr;

    /// Testing multiplication for two [`PolyOverZq`]
    #[test]
    fn mul() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("2  2 4 mod 7").unwrap();
        let c: PolyOverZq = a * b;
        assert_eq!(c, PolyOverZq::from_str("4  4 2 4 4 mod 7").unwrap());
    }

    /// Testing multiplication for two borrowed [`PolyOverZq`]
    #[test]
    fn mul_borrow() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("2  2 4 mod 7").unwrap();
        let c: PolyOverZq = &a * &b;
        assert_eq!(c, PolyOverZq::from_str("4  4 2 4 4 mod 7").unwrap());
    }

    /// Testing multiplication for borrowed [`PolyOverZq`] and [`PolyOverZq`]
    #[test]
    fn mul_first_borrowed() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("2  2 4 mod 7").unwrap();
        let c: PolyOverZq = &a * b;
        assert_eq!(c, PolyOverZq::from_str("4  4 2 4 4 mod 7").unwrap());
    }

    /// Testing multiplication for [`PolyOverZq`] and borrowed [`PolyOverZq`]
    #[test]
    fn mul_second_borrowed() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("2  2 4 mod 7").unwrap();
        let c: PolyOverZq = a * &b;
        assert_eq!(c, PolyOverZq::from_str("4  4 2 4 4 mod 7").unwrap());
    }

    /// Testing multiplication for [`PolyOverZq`] and a constant [`PolyOverZq`]
    #[test]
    fn mul_constant() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("1  2 mod 7").unwrap();
        let c: PolyOverZq = &a * b;
        assert_eq!(c, PolyOverZq::from_str("3  4 1 2 mod 7").unwrap());
        assert_eq!(
            a * PolyOverZq::from_str("0 mod 7").unwrap(),
            PolyOverZq::from_str("0 mod 7").unwrap()
        );
    }

    /// Testing multiplication for big [`PolyOverZq`]
    #[test]
    fn mul_large_numbers() {
        let a: PolyOverZq = PolyOverZq::from_str(&format!(
            "2  {} {} mod {}",
            u64::MAX,
            i64::MAX,
            u64::MAX - 58
        ))
        .unwrap();
        let b: PolyOverZq = PolyOverZq::from_str(&format!(
            "2  {} {} mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX - 58
        ))
        .unwrap();
        let c: PolyOverZq = a * &b;
        assert_eq!(
            c,
            PolyOverZq::from_str(&format!(
                "3  {} {} {} mod {}",
                i128::from(i64::MAX) * 58,
                i128::from(i64::MIN) * 58 + i128::from(i64::MAX) * i128::from(i64::MAX),
                i128::from(i64::MAX) * i128::from(i64::MIN),
                u64::MAX - 58
            ))
            .unwrap()
        );
    }

    /// Testing multiplication for [`PolyOverZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn mul_mismatching_modulus() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 8").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("2  -5 4 mod 7").unwrap();
        let _c: PolyOverZq = a * b;
    }

    /// Testing whether mul_safe throws an error for mismatching moduli
    #[test]
    fn mul_safe_is_err() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 9").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("2  -5 4 mod 7").unwrap();
        assert!(&a.mul_safe(&b).is_err());
    }
}
