// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a modulus of type
//! [`PolynomialRingZq`] into a [`String`].
//!
//! The [`Display`](std::fmt::Display) trait is omitted, since it is derived,
//! but tests for it are included.

use super::PolynomialRingZq;
use crate::macros::for_others::implement_for_owned;

impl From<&PolynomialRingZq> for String {
    /// Converts a [`PolynomialRingZq`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the polynomial that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[#number of coefficients of element]⌴⌴[0th coefficient]⌴
    ///     [1st coefficient]⌴...⌴/⌴[#number of coefficients of polynomial modulus]⌴⌴
    ///     [0th coefficient]⌴[1st coefficient]⌴...⌴mod⌴[q]"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use std::str::FromStr;
    /// let poly = PolynomialRingZq::from_str("2  2 1 / 3  2 2 2 mod 3").unwrap();
    ///
    /// let string: String = poly.into();
    /// ```
    fn from(value: &PolynomialRingZq) -> Self {
        value.to_string()
    }
}

implement_for_owned!(PolynomialRingZq, String, From);

#[cfg(test)]
mod test_to_string {
    use super::PolynomialRingZq;
    use std::str::FromStr;

    /// Tests whether a polynomial that is created using a string, returns the
    /// same string, when it is converted back to a string
    #[test]
    fn working_keeps_same_string() {
        let cmp_str = "2  1 1 / 3  1 2 2 mod 5";
        let cmp = PolynomialRingZq::from_str(cmp_str).unwrap();

        assert_eq!(cmp_str, cmp.to_string());
    }

    /// Tests whether a polynomial that is created using a string, returns a
    /// string that can be used to create a polynomial
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp_str = "2  1 1 / 3  1 2 2 mod 5";
        let cmp = PolynomialRingZq::from_str(cmp_str).unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(PolynomialRingZq::from_str(&cmp_str_2).is_ok());
    }

    /// Test applied modulus if initialized with negative values
    #[test]
    fn initialized_neg() {
        let cmp_str = "2  -1 1 / 3  -1 -2 -3 mod 5";
        let cmp = PolynomialRingZq::from_str(cmp_str).unwrap();

        assert_eq!("2  4 1 / 3  4 3 2 mod 5", cmp.to_string());
    }

    /// Tests that large entries and large moduli work with to_string()
    #[test]
    fn large_entries_modulus() {
        let cmp_str = format!("2  1 {} / 3  1 2 {} mod 1{}", u64::MAX, u64::MAX, u64::MAX);
        let cmp = PolynomialRingZq::from_str(&cmp_str).unwrap();

        assert_eq!(cmp_str, cmp.to_string());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "2  2 1 / 3  1 1 1 mod 3";
        let poly = PolynomialRingZq::from_str(cmp).unwrap();

        let string: String = poly.clone().into();
        let borrowed_string: String = (&poly).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}
