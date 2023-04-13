// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`PolyOverZq`] values.

use super::super::PolyOverZq;
use crate::{
    error::MathError,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_add;
use std::{ops::Add, str::FromStr};

impl Add for &PolyOverZq {
    type Output = PolyOverZq;
    /// Implements the [`Add`] trait for two [`PolyOverZq`] values.
    /// [`Add`] is implemented for any combination of [`PolyOverZq`] and borrowed [`PolyOverZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to add to `self`
    ///
    /// Returns the sum of both polynomials as a [`PolyOverZq`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
    /// let b: PolyOverZq = PolyOverZq::from_str("3  5 1 1 mod 7").unwrap();
    ///
    /// let c: PolyOverZq = &a + &b;
    /// let d: PolyOverZq = a + b;
    /// let e: PolyOverZq = &c + d;
    /// let f: PolyOverZq = c + &e;
    /// ```
    ///
    /// # Errors and Failures
    /// - Panics if the moduli of both [`PolyOverZq`] mismatch.
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

impl PolyOverZq {
    /// Implements addition for two [`PolyOverZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to add to `self`
    ///
    /// Returns the sum of both polynomials as a [`PolyOverZq`] or an error if the modulus
    /// do mismatch.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
    /// let b: PolyOverZq = PolyOverZq::from_str("3  5 1 1 mod 7").unwrap();
    ///
    /// let c: PolyOverZq = a.add_safe(&b).unwrap();
    /// ```
    /// # Errors and Failures
    /// Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    /// both [`PolyOverZq`] mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<PolyOverZq, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to add polynomial with modulus '{}' and polynomial with modulus '{}'.
            If the modulus should be ignored please convert into a PolyOverZ beforehand.",
                self.modulus, other.modulus
            )));
        }
        let mut out = PolyOverZq::from_str(&format!("0 mod {}", self.modulus)).unwrap();
        unsafe {
            fmpz_mod_poly_add(
                &mut out.poly,
                &self.poly,
                &other.poly,
                &*self.modulus.modulus,
            );
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, PolyOverZq, PolyOverZq, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Add, add, PolyOverZq, PolyOverZq, PolyOverZq);

#[cfg(test)]
mod test_add {

    use super::PolyOverZq;
    use std::str::FromStr;

    /// testing addition for two [`PolyOverZq`]
    #[test]
    fn add() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 4 1 mod 7").unwrap();
        let c: PolyOverZq = a + b;
        assert_eq!(c, PolyOverZq::from_str("3  4 1 2 mod 7").unwrap());
    }

    /// testing addition for two borrowed [`PolyOverZq`]
    #[test]
    fn add_borrow() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 4 1 mod 7").unwrap();
        let c: PolyOverZq = &a + &b;
        assert_eq!(c, PolyOverZq::from_str("3  4 1 2 mod 7").unwrap());
    }

    /// testing addition for borrowed [`PolyOverZq`] and [`PolyOverZq`]
    #[test]
    fn add_first_borrowed() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 4 1 mod 7").unwrap();
        let c: PolyOverZq = &a + b;
        assert_eq!(c, PolyOverZq::from_str("3  4 1 2 mod 7").unwrap());
    }

    /// testing addition for [`PolyOverZq`] and borrowed [`PolyOverZq`]
    #[test]
    fn add_second_borrowed() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 4 1 mod 7").unwrap();
        let c: PolyOverZq = a + &b;
        assert_eq!(c, PolyOverZq::from_str("3  4 1 2 mod 7").unwrap());
    }

    /// testing addition of [`PolyOverZq`] is reducing the polynomial
    #[test]
    fn add_reduce() {
        let a: PolyOverZq = PolyOverZq::from_str("3  2 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 4 6 mod 7").unwrap();
        let c: PolyOverZq = a + b;
        assert_eq!(c, PolyOverZq::from_str("2  4 1 mod 7").unwrap());
    }

    /// testing addition for big [`PolyOverZq`]
    #[test]
    fn add_large_numbers() {
        let a: PolyOverZq = PolyOverZq::from_str(&format!(
            "3  -{} 4 {} mod {}",
            u64::MAX,
            i64::MIN,
            u64::MAX - 58
        ))
        .unwrap();
        let b: PolyOverZq = PolyOverZq::from_str(&format!(
            "3  {} 4 {} mod {}",
            i64::MIN,
            i64::MIN,
            u64::MAX - 58
        ))
        .unwrap();
        let c: PolyOverZq = a + b;
        assert!(
            c == PolyOverZq::from_str(&format!(
                "3  -{} 8 {} mod {}",
                i128::from(i64::MAX) + 59,
                -59,
                u64::MAX - 58
            ))
            .unwrap()
        );
    }

    /// testing addition for [`PolyOverZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn add_mismatching_modulus() {
        let a: PolyOverZq = PolyOverZq::from_str("3  -5 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 4 1 mod 8").unwrap();
        let _c: PolyOverZq = a + b;
    }

    /// testing whether add_safe throws an error for mismatching moduli
    #[test]
    fn add_safe_is_err() {
        let a: PolyOverZq = PolyOverZq::from_str("3  -5 4 1 mod 7").unwrap();
        let b: PolyOverZq = PolyOverZq::from_str("3  -5 4 1 mod 11").unwrap();
        assert!(&a.add_safe(&b).is_err());
    }
}
