// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a matrix of type
//! [`MatZ`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::MatZ;
use crate::{macros::for_others::implement_for_owned, utils::parse::matrix_to_string};
use core::fmt;

impl From<&MatZ> for String {
    /// Converts a [`MatZ`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[[row_0],[row_1],...[row_n]]"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    /// let matrix = MatZ::from_str("[[6, 1],[5, 2]]").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &MatZ) -> Self {
        value.to_string()
    }
}

implement_for_owned!(MatZ, String, From);

impl fmt::Display for MatZ {
    /// Allows to convert a matrix of type [`MatZ`] into a [`String`].
    ///
    /// Returns the Matrix in form of a [`String`]. For matrix `[[1, 2, 3],[4, 5, 6]]`
    /// the String looks like this `[[1, 2, 3],[4, 5, 6]]`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZ::from_str("[[1, 2, 3],[4, 5, 6]]").unwrap();
    /// println!("{matrix}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZ::from_str("[[1, 2, 3],[4, 5, 6]]").unwrap();
    /// let matrix_string = matrix.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", matrix_to_string(self))
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Tests whether a matrix with a large entry works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = MatZ::from_str(&format!("[[{}, 1, 3],[5, 6, 7]]", u64::MAX)).unwrap();

        assert_eq!(format!("[[{}, 1, 3],[5, 6, 7]]", u64::MAX), cmp.to_string());
    }

    /// Tests whether a matrix with a large negative entry works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = MatZ::from_str(&format!("[[-{}, 1, 3],[5, 6, 7]]", u64::MAX)).unwrap();

        assert_eq!(
            format!("[[-{}, 1, 3],[5, 6, 7]]", u64::MAX),
            cmp.to_string()
        )
    }

    /// Tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = MatZ::from_str("[[2, 1, 3],[5, 6, 7]]").unwrap();

        assert_eq!("[[2, 1, 3],[5, 6, 7]]", cmp.to_string());
    }

    /// Tests whether a matrix with negative entries works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = MatZ::from_str("[[-2, 1, 3],[5, -6, 7]]").unwrap();

        assert_eq!("[[-2, 1, 3],[5, -6, 7]]", cmp.to_string());
    }

    /// Tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_large_dimensions() {
        let cmp_1 = MatZ::from_str(&format!("[{}[5, 6, 7]]", "[1, 2, 3],".repeat(99))).unwrap();
        let cmp_2 = MatZ::from_str(&format!("[[{}1]]", "1, ".repeat(99))).unwrap();

        assert_eq!(
            format!("[{}[5, 6, 7]]", "[1, 2, 3],".repeat(99)),
            cmp_1.to_string()
        );
        assert_eq!(format!("[[{}1]]", "1, ".repeat(99)), cmp_2.to_string());
    }

    /// Tests whether a matrix that is created using a string, returns a
    /// string that can be used to create a [`MatZ`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = MatZ::from_str("[[-2, 1, 3],[5, -6, 7]]").unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(MatZ::from_str(&cmp_str_2).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "[[6, 1, 3],[5, 2, 7]]";
        let matrix = MatZ::from_str(cmp).unwrap();
        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();
        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}
