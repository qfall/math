// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a modulus of type
//! [`PolyOverZq`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::PolyOverZq;
use crate::{integer::PolyOverZ, macros::for_others::implement_for_owned};
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_get_fmpz_poly;
use std::fmt;

impl From<&PolyOverZq> for String {
    /// Converts a [`PolyOverZq`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴...⌴mod⌴[modulus]"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    /// let matrix = PolyOverZq::from_str("2  2 1 mod 3").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &PolyOverZq) -> Self {
        value.to_string()
    }
}

implement_for_owned!(PolyOverZq, String, From);

impl fmt::Display for PolyOverZq {
    /// Allows to convert a [`PolyOverZq`] into a [`String`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let poly = PolyOverZq::from_str("4  0 1 2 3 mod 5").unwrap();
    /// println!("{poly}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("4  0 1 2 3 mod 5").unwrap();
    /// let poly_string = poly.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // there is no dedicated method to create a string from a fmpz_mod_poly
        // hence we convert it to a fmpz_poly first to use the dedicated method

        let mut poly_over_z = PolyOverZ::default();
        unsafe {
            fmpz_mod_poly_get_fmpz_poly(
                &mut poly_over_z.poly,
                &self.poly,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
        write!(f, "{poly_over_z} mod {}", self.modulus)
    }
}

#[cfg(test)]
mod test_to_string {
    use super::PolyOverZq;
    use std::str::FromStr;

    /// Tests whether a polynomial that is created using a string, returns the
    /// same string, when it is converted back to a string
    #[test]
    fn working_keeps_same_string() {
        let cmp_str = "3  1 2 2 mod 5";
        let cmp = PolyOverZq::from_str(cmp_str).unwrap();

        assert_eq!(cmp_str, cmp.to_string());
    }

    /// Tests whether a polynomial that is created using a string, returns a
    /// string that can be used to create a polynomial
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp_str = "3  1 2 2 mod 5";
        let cmp = PolyOverZq::from_str(cmp_str).unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(PolyOverZq::from_str(&cmp_str_2).is_ok());
    }

    /// Test applied modulus if initialized with negative values
    #[test]
    fn initialized_neg() {
        let cmp_str = "3  -1 -2 -3 mod 5";
        let cmp = PolyOverZq::from_str(cmp_str).unwrap();

        assert_eq!("3  4 3 2 mod 5", cmp.to_string());
    }

    /// Tests that large entries and large moduli work with to_string()
    #[test]
    fn large_entries_modulus() {
        let cmp_str = format!("3  1 2 {} mod 1{}", u64::MAX, u64::MAX);
        let cmp = PolyOverZq::from_str(&cmp_str).unwrap();

        assert_eq!(cmp_str, cmp.to_string());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "2  2 1 mod 3";
        let matrix = PolyOverZq::from_str(cmp).unwrap();

        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}
