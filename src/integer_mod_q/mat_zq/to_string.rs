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

use crate::{integer::Z, utils::parse::matrix_to_string};

use super::MatZq;
use core::fmt;

impl fmt::Display for MatZq {
    /// Allows to convert a matrix of type [`MatZq`] into a [`String`].
    ///
    /// Returns the Matrix in form of a [`String`]. For matrix `[[1, 2, 3],[4, 5, 6]] mod 4`
    /// the String looks like this `[[1, 2, 3],[0, 1, 2]] mod 4`.
    ///
    /// # Examples
    /// ```
    /// use math::integer_mod_q::MatZq;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1,2,3],[4,5,6]] mod 4").unwrap();
    /// println!("{}", matrix);
    /// ```
    ///
    /// ```
    /// use math::integer_mod_q::MatZq;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1,2,3],[4,5,6]] mod 4").unwrap();
    /// let matrix_string = matrix.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let matrix = matrix_to_string::<Z, MatZq>(self);
        let modulus = self.get_mod().to_string();
        write!(f, "{} mod {}", matrix, modulus)
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// tests whether a matrix with a large entry works in a roundtrip
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

    /// tests whether a matrix with a large negative entry works in a roundtrip
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

    /// tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = MatZq::from_str("[[2, 1, 3],[5, 6, 7]] mod 4").unwrap();

        assert_eq!("[[2, 1, 3],[1, 2, 3]] mod 4", cmp.to_string())
    }

    /// tests whether a matrix with negative entries works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = MatZq::from_str("[[-2, 1, 3],[5, -6, 7]] mod 4").unwrap();

        assert_eq!("[[2, 1, 3],[1, 2, 3]] mod 4", cmp.to_string())
    }

    /// tests whether a matrix with a large modulus works in a roundtrip
    #[test]
    fn working_large_modulus() {
        let cmp = MatZq::from_str(&format!("[[1, 1, 3],[5, 6, 7]] mod {}", u64::MAX)).unwrap();

        assert_eq!(
            format!("[[1, 1, 3],[5, 6, 7]] mod {}", u64::MAX),
            cmp.to_string()
        )
    }

    /// tests whether a large matrix works in a roundtrip
    #[test]
    fn working_big_dimensions() {
        let cmp1 =
            MatZq::from_str(&format!("[{}[5, 6, 7]] mod 4", "[1, 2, 3],".repeat(99))).unwrap();
        let cmp2 = MatZq::from_str(&format!("[[{}1]] mod 4", "1, ".repeat(99))).unwrap();

        assert_eq!(
            format!("[{}[1, 2, 3]] mod 4", "[1, 2, 3],".repeat(99)),
            cmp1.to_string()
        );
        assert_eq!(format!("[[{}1]] mod 4", "1, ".repeat(99)), cmp2.to_string());
    }

    /// tests whether a matrix that is created using a string, returns a
    /// string that can be used to create a [`MatZq`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = MatZq::from_str("[[-2, 1, 3],[5, -6, 7]] mod 4").unwrap();

        let cmp_string2 = cmp.to_string();

        assert!(MatZq::from_str(&cmp_string2).is_ok())
    }
}
