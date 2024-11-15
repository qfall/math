// Copyright © 2024 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a matrix of type
//! [`MatPolynomialRingZq`] into a [`String`].

use super::MatPolynomialRingZq;
use crate::macros::for_others::implement_for_owned;

impl From<&MatPolynomialRingZq> for String {
    /// Converts a [`MatPolynomialRingZq`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[[poly_1, poly_2, poly_3],[poly_4, poly_5, poly_6]] / poly_7 mod q"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use std::str::FromStr;
    /// let matrix = MatPolynomialRingZq::from_str("[[2  2 2, 1  2],[0, 1  3]] / 2  4 4 mod 3").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &MatPolynomialRingZq) -> Self {
        value.to_string()
    }
}

implement_for_owned!(MatPolynomialRingZq, String, From);

#[cfg(test)]
mod test_to_string {
    use crate::integer_mod_q::MatPolynomialRingZq;
    use std::str::FromStr;

    /// Most tests are omitted, since the [`Display`](std::fmt::Display) trait
    /// is derived and therefor already tested.

    /// Tests whether a roundtrip works correctly.
    #[test]
    fn roundtrip() {
        let cmp =
            MatPolynomialRingZq::from_str("[[1  2, 1  1, 0],[1  5, 1  6, 1  7]] / 2  1 1 mod 11")
                .unwrap();

        assert_eq!(
            "[[1  2, 1  1, 0],[1  5, 1  6, 1  7]] / 2  1 1 mod 11",
            cmp.to_string()
        )
    }

    /// Tests whether the matrix is correctly reduced.
    #[test]
    fn reduced() {
        let cmp =
            MatPolynomialRingZq::from_str("[[2  2 2, 1  1, 0],[1  5, 1  6, 1  7]] / 2  4 4 mod 3")
                .unwrap();

        assert_eq!(
            "[[0, 1  1, 0],[1  2, 0, 1  1]] / 2  1 1 mod 3",
            cmp.to_string()
        )
    }
}
