// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a matrix of type
//! [`MatZq`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::MatZq;
use crate::{integer::Z, macros::for_others::implement_for_owned, utils::parse::matrix_to_string};
use core::fmt;

impl From<&MatZq> for String {
    /// Converts a [`MatZq`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[[row_0],[row_1],...[row_n]] mod q"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    /// let matrix = MatZq::from_str("[[6, 1],[5, 2]] mod 4").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &MatZq) -> Self {
        value.to_string()
    }
}

implement_for_owned!(MatZq, String, From);

impl fmt::Display for MatZq {
    /// Allows to convert a matrix of type [`MatZq`] into a [`String`].
    ///
    /// Returns the Matrix in form of a [`String`]. For matrix `[[1, 2, 3],[4, 5, 6]] mod 4`
    /// the String looks like this `[[1, 2, 3],[0, 1, 2]] mod 4`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 4").unwrap();
    /// println!("{matrix}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 4").unwrap();
    /// let matrix_string = matrix.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let matrix = matrix_to_string::<Z, MatZq>(self);
        write!(f, "{matrix} mod {}", self.get_mod())
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Tests whether a matrix with a large entry works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = MatZq::from_str(&format!(
            "[[{}, 1, 3],[5, 6, 7]] mod {}",
            u64::MAX - 1,
            u64::MAX
        ))
        .unwrap();

        assert_eq!(
            format!("[[{}, 1, 3],[5, 6, 7]] mod {}", u64::MAX - 1, u64::MAX),
            cmp.to_string()
        )
    }

    /// Tests whether a matrix with a large negative entry works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = MatZq::from_str(&format!(
            "[[-{}, 1, 3],[5, 6, 7]] mod {}",
            u64::MAX - 1,
            u64::MAX
        ))
        .unwrap();

        assert_eq!(
            format!("[[1, 1, 3],[5, 6, 7]] mod {}", u64::MAX),
            cmp.to_string()
        )
    }

    /// Tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = MatZq::from_str("[[2, 1, 3],[5, 6, 7]] mod 4").unwrap();

        assert_eq!("[[2, 1, 3],[1, 2, 3]] mod 4", cmp.to_string());
    }

    /// Tests whether a matrix with negative entries works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = MatZq::from_str("[[-2, 1, 3],[5, -6, 7]] mod 4").unwrap();

        assert_eq!("[[2, 1, 3],[1, 2, 3]] mod 4", cmp.to_string());
    }

    /// Tests whether a matrix with a large modulus works in a roundtrip
    #[test]
    fn working_large_modulus() {
        let cmp = MatZq::from_str(&format!("[[1, 1, 3],[5, 6, 7]] mod {}", u64::MAX)).unwrap();

        assert_eq!(
            format!("[[1, 1, 3],[5, 6, 7]] mod {}", u64::MAX),
            cmp.to_string()
        )
    }

    /// Tests whether a large matrix works in a roundtrip
    #[test]
    fn working_large_dimensions() {
        let cmp_1 =
            MatZq::from_str(&format!("[{}[5, 6, 7]] mod 4", "[1, 2, 3],".repeat(99))).unwrap();
        let cmp_2 = MatZq::from_str(&format!("[[{}1]] mod 4", "1, ".repeat(99))).unwrap();

        assert_eq!(
            format!("[{}[1, 2, 3]] mod 4", "[1, 2, 3],".repeat(99)),
            cmp_1.to_string()
        );
        assert_eq!(
            format!("[[{}1]] mod 4", "1, ".repeat(99)),
            cmp_2.to_string()
        );
    }

    /// Tests whether a matrix that is created using a string, returns a
    /// string that can be used to create a [`MatZq`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = MatZq::from_str("[[-2, 1, 3],[5, -6, 7]] mod 4").unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(MatZq::from_str(&cmp_str_2).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "[[6, 1, 3],[5, 2, 7]] mod 8";
        let matrix = MatZq::from_str(cmp).unwrap();
        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();
        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}
