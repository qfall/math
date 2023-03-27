// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a matrix of type
//! [`MatPolyOverZ`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use crate::utils::parse::matrix_to_string;

use super::MatPolyOverZ;
use core::fmt;

impl fmt::Display for MatPolyOverZ {
    /// Allows to convert a matrix of type [`MatPolyOverZ`] into a [`String`].
    ///
    /// Returns the Matrix in form of a [`String`]. For matrix
    /// `[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]` the String looks
    ///  like this `[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]`.
    ///
    /// # Examples
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
    /// println!("{}", matrix);
    /// ```
    ///
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
    /// let matrix_string = matrix.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", matrix_to_string(self))
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::integer::MatPolyOverZ;
    use std::str::FromStr;

    /// tests whether a matrix with a large entry works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = MatPolyOverZ::from_str(&format!(
            "[[0, 1  {}, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
            u64::MAX
        ))
        .unwrap();

        assert_eq!(
            format!(
                "[[0, 1  {}, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
                u64::MAX
            ),
            cmp.to_string()
        )
    }

    /// tests whether a matrix with a large negative entry works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = MatPolyOverZ::from_str(&format!(
            "[[0, 1  -{}, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
            u64::MAX
        ))
        .unwrap();

        assert_eq!(
            format!(
                "[[0, 1  -{}, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
                u64::MAX
            ),
            cmp.to_string()
        )
    }

    /// tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();

        assert_eq!(
            "[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
            cmp.to_string()
        )
    }

    /// tests whether a matrix with negative entries works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp =
            MatPolyOverZ::from_str("[[0, 1  -42, 2  42 24],[3  17 24 42, 1  -17, 1  42]]").unwrap();

        assert_eq!(
            "[[0, 1  -42, 2  42 24],[3  17 24 42, 1  -17, 1  42]]",
            cmp.to_string()
        )
    }

    /// tests whether a large matrix works in a roundtrip
    #[test]
    fn working_big_dimensions() {
        let cmp1 = MatPolyOverZ::from_str(&format!(
            "[{}[3  17 24 42, 1  -17, 1  42]]",
            "[0, 1  42, 2  42 24],".repeat(99)
        ))
        .unwrap();
        let cmp2 = MatPolyOverZ::from_str(&format!("[[{}1  42]]", "1  42, ".repeat(99))).unwrap();

        assert_eq!(
            format!(
                "[{}[3  17 24 42, 1  -17, 1  42]]",
                "[0, 1  42, 2  42 24],".repeat(99)
            ),
            cmp1.to_string()
        );
        assert_eq!(
            format!("[[{}1  42]]", "1  42, ".repeat(99)),
            cmp2.to_string()
        );
    }

    /// tests whether a matrix that is created using a string, returns a
    /// string that can be used to create a [`MatZ`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp =
            MatPolyOverZ::from_str("[[0, 1  -42, 2  42 24],[3  17 24 42, 1  -17, 1  42]]").unwrap();

        let cmp_string2 = cmp.to_string();

        assert!(MatPolyOverZ::from_str(&cmp_string2).is_ok())
    }
}
