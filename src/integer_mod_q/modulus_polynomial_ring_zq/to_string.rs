// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a polynomial of type
//! [`ModulusPolynomialRingZq] into a [`String`].
//!
//! This includes the [`Display`] trait.

use super::ModulusPolynomialRingZq;
use crate::{
    integer::{PolyOverZ, Z},
    macros::for_others::implement_for_owned,
};
use flint_sys::{fmpz::fmpz_set, fmpz_mod_poly::fmpz_mod_poly_get_fmpz_poly};
use std::fmt::Display;

impl From<&ModulusPolynomialRingZq> for String {
    /// Converts a [`ModulusPolynomialRingZq`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴...⌴mod⌴[modulus]"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    /// let matrix = ModulusPolynomialRingZq::from_str("2  2 1 mod 3").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &ModulusPolynomialRingZq) -> Self {
        value.to_string()
    }
}

implement_for_owned!(ModulusPolynomialRingZq, String, From);

impl Display for ModulusPolynomialRingZq {
    /// Allows to convert a [`ModulusPolynomialRingZq`] into a [`String`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// println!("{poly}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let poly_string = poly.to_string();
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // get the value of the modulus
        let mut modulus = Z::default();
        unsafe { fmpz_set(&mut modulus.value, &self.get_fq_ctx_struct().ctxp[0].n[0]) };

        // get the value of the polynomial
        let mut poly = PolyOverZ::default();
        unsafe {
            fmpz_mod_poly_get_fmpz_poly(
                &mut poly.poly,
                &self.get_fq_ctx_struct().modulus[0],
                &self.get_fq_ctx_struct().ctxp[0],
            )
        };

        write!(f, "{poly} mod {modulus}")
    }
}

/// most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_to_string {
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// Test whether a roundtrip works
    #[test]
    fn working_keeps_same_string() {
        let cmp_str = "3  1 2 2 mod 5";
        let cmp = ModulusPolynomialRingZq::from_str(cmp_str).unwrap();

        assert_eq!(cmp_str, cmp.to_string());
    }

    /// Test whether a string returned from to_string can be used to construct a [`ModulusPolynomialRingZq`]
    #[test]
    fn working_use_result_of_to_string() {
        let cmp_str = "3  1 2 2 mod 5";
        let cmp = ModulusPolynomialRingZq::from_str(cmp_str).unwrap();
        let str_1 = cmp.to_string();

        assert!(ModulusPolynomialRingZq::from_str(&str_1).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "2  2 1 mod 3";
        let matrix = ModulusPolynomialRingZq::from_str(cmp).unwrap();

        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}
