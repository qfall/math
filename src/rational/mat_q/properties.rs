// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`MatQ`] instances.

use super::MatQ;
use flint_sys::fmpq_mat::{fmpq_mat_is_one, fmpq_mat_is_square, fmpq_mat_is_zero};

impl MatQ {
    /// Checks if a [`MatQ`] is the identity matrix.
    ///
    /// Returns true if every diagonal entry is `1` and all other entries are
    /// `0` and the matrix is a square matrix.
    ///
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let value = MatQ::from_str("[[1, 0],[0, 1]]").unwrap();
    /// assert!(value.is_identity())
    /// ```
    pub fn is_identity(&self) -> bool {
        self.is_square() && 1 == unsafe { fmpq_mat_is_one(&self.matrix) }
    }

    /// Checks if a [`MatQ`] is a square matrix.
    ///
    /// Returns true if the number of rows and columns is identical.
    ///
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let value = MatQ::from_str("[[4/7, 0],[5/8, 1/9]]").unwrap();
    /// assert!(value.is_square())
    /// ```
    pub fn is_square(&self) -> bool {
        1 == unsafe { fmpq_mat_is_square(&self.matrix) }
    }

    /// Checks if every entry of a [`MatQ`] is `0`.
    ///
    /// Returns true if every entry is `0`.
    ///
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let value = MatQ::from_str("[[0, 0],[0, 0]]").unwrap();
    /// assert!(value.is_zero())
    /// ```
    pub fn is_zero(&self) -> bool {
        1 == unsafe { fmpq_mat_is_zero(&self.matrix) }
    }
}

#[cfg(test)]
mod test_is_identity {
    use super::MatQ;
    use std::str::FromStr;

    /// ensure that is_identity returns `true` for identity matrices
    #[test]
    fn identity_detection() {
        let ident = MatQ::from_str("[[1, 0],[0, 1]]").unwrap();

        assert!(ident.is_identity());
    }

    /// ensure that is_identity returns `false` for non-identity matrices
    #[test]
    fn identity_rejection() {
        let small = MatQ::from_str("[[0, 0],[2/81, 0]]").unwrap();
        let large = MatQ::from_str(&format!("[[1, 0],[0, {}]]", (u128::MAX - 1) / 2 + 2)).unwrap();
        let nosquare = MatQ::from_str("[[1, 0],[0, 1],[0, 0]]").unwrap();

        assert!(!small.is_identity());
        assert!(!large.is_identity());
        assert!(!nosquare.is_identity());
    }
}

#[cfg(test)]
mod test_is_zero {
    use super::MatQ;
    use std::str::FromStr;

    /// ensure that is_zero returns `true` for all zero matrices
    #[test]
    fn zero_detection() {
        let zero = MatQ::from_str("[[0, 0],[0, 0]]").unwrap();

        assert!(zero.is_zero());
    }

    /// ensure that is_zero returns `false` for non-zero matrices
    #[test]
    fn zero_rejection() {
        let small = MatQ::from_str("[[0, 7/8],[2, 0]]").unwrap();
        let large = MatQ::from_str(&format!("[[0, 0],[{}, 0]]", (u128::MAX - 1) / 2 + 1)).unwrap();

        assert!(!small.is_zero());
        assert!(!large.is_zero());
    }
}

#[cfg(test)]
mod test_is_square {
    use super::MatQ;
    use std::str::FromStr;

    /// ensure that is_square returns `true` for square matrices
    #[test]
    fn square_detection() {
        let square1 = MatQ::from_str("[[0, 4/9],[0, 0]]").unwrap();
        let square2 = MatQ::from_str("[[0, 6/123, 4/7],[0, 0, 1/213],[4/341, 6/83, 1]]").unwrap();

        assert!(square1.is_square());
        assert!(square2.is_square());
    }

    /// ensure that is_square returns `false` for non-square matrices
    #[test]
    fn sqaure_rejection() {
        let small = MatQ::from_str("[[0, 5/6, 4],[2/7, 0, 1]]").unwrap();
        let large = MatQ::from_str("[[9, 0],[127/71, 0],[0, 0]]").unwrap();

        assert!(!small.is_square());
        assert!(!large.is_square());
    }
}
