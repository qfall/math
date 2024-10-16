// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`MatZq`] instances.

use super::MatZq;
use flint_sys::{
    fmpz_mat::fmpz_mat_is_one,
    fmpz_mod_mat::{fmpz_mod_mat_is_square, fmpz_mod_mat_is_zero},
};

impl MatZq {
    /// Checks if a [`MatZq`] is the identity matrix.
    ///
    /// Returns `true` if every diagonal entry of the upper square matrix is `1`
    /// and all other entries are `0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let value = MatZq::from_str("[[1, 0],[0, 1]] mod 17").unwrap();
    /// assert!(value.is_identity());
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let value = MatZq::from_str("[[1, 0],[0, 1],[0, 0]] mod 17").unwrap();
    /// assert!(value.is_identity());
    /// ```
    pub fn is_identity(&self) -> bool {
        unsafe { 1 == fmpz_mat_is_one(&self.matrix.mat[0]) }
    }

    /// Checks if a [`MatZq`] is a square matrix.
    ///
    /// Returns `true` if the number of rows and columns is identical.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let value = MatZq::from_str("[[4, 0],[0, 1]] mod 17").unwrap();
    /// assert!(value.is_square());
    /// ```
    pub fn is_square(&self) -> bool {
        1 == unsafe { fmpz_mod_mat_is_square(&self.matrix) }
    }

    /// Checks if every entry of a [`MatZq`] is `0`.
    ///
    /// Returns `true` if every entry is `0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let value = MatZq::from_str("[[0, 0],[0, 0]] mod 17").unwrap();
    /// assert!(value.is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        1 == unsafe { fmpz_mod_mat_is_zero(&self.matrix) }
    }
}

#[cfg(test)]
mod test_is_identity {
    use super::MatZq;
    use std::str::FromStr;

    /// Ensure that is_identity returns `true` for identity matrices.
    #[test]
    fn identity_detection() {
        let ident_1 = MatZq::from_str("[[1, 0],[0, 1]] mod 7").unwrap();
        let ident_2 = MatZq::from_str("[[1, 0],[0, 1],[0, 0]] mod 7").unwrap();

        assert!(ident_1.is_identity());
        assert!(ident_2.is_identity());
    }

    /// Ensure that is_identity returns `false` for non-identity matrices.
    #[test]
    fn identity_rejection() {
        let small = MatZq::from_str("[[0, 0],[2, 0]] mod 17").unwrap();
        let large = MatZq::from_str(&format!(
            "[[1, 0],[0, {}]] mod {}",
            (u128::MAX - 1) / 2 + 2,
            u128::MAX
        ))
        .unwrap(); // the last 64 bit represent `1`

        assert!(!small.is_identity());
        assert!(!large.is_identity());
    }
}

#[cfg(test)]
mod test_is_zero {
    use super::MatZq;
    use std::str::FromStr;

    /// Ensure that is_zero returns `true` for all zero matrices.
    #[test]
    fn zero_detection() {
        let zero_1 = MatZq::from_str("[[0, 0],[0, 0]] mod 7").unwrap();
        let zero_2 = MatZq::from_str("[[0, 0],[0, 0],[0, 0],[0, 0]] mod 7").unwrap();

        assert!(zero_1.is_zero());
        assert!(zero_2.is_zero());
    }

    /// Ensure that is_zero returns `false` for non-zero matrices.
    #[test]
    fn zero_rejection() {
        let small = MatZq::from_str("[[0, 0],[2, 0]] mod 7").unwrap();
        let large = MatZq::from_str(&format!(
            "[[0, 0],[{}, 0]] mod {}",
            (u128::MAX - 1) / 2 + 1,
            u128::MAX
        ))
        .unwrap();

        assert!(!small.is_zero());
        assert!(!large.is_zero());
    }
}

#[cfg(test)]
mod test_is_square {
    use super::MatZq;
    use std::str::FromStr;

    /// Ensure that is_square returns `true` for square matrices.
    #[test]
    fn square_detection() {
        let square_1 = MatZq::from_str("[[0, 4],[0, 0]] mod 10").unwrap();
        let square_2 = MatZq::from_str("[[0, 6, 4],[0, 0, 1],[4, 6, 1]] mod 7").unwrap();

        assert!(square_1.is_square());
        assert!(square_2.is_square());
    }

    /// Ensure that is_square returns `false` for non-square matrices.
    #[test]
    fn sqaure_rejection() {
        let small = MatZq::from_str("[[0, 0, 4],[2, 0, 1]] mod 7").unwrap();
        let large = MatZq::from_str(&format!(
            "[[9, 0],[{}, 0],[1, 4]] mod {}",
            (u128::MAX - 1) / 2 + 1,
            u128::MAX
        ))
        .unwrap();

        assert!(!small.is_square());
        assert!(!large.is_square());
    }
}
