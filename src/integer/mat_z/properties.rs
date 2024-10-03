// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`MatZ`] instances.

use super::MatZ;
use flint_sys::fmpz_mat::{fmpz_mat_is_one, fmpz_mat_is_square, fmpz_mat_is_zero};

impl MatZ {
    /// Checks if a [`MatZ`] is the identity matrix.
    ///
    /// Returns `true` if every diagonal entry of the matrix is `1`
    /// and every other entry is `0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let value = MatZ::identity(2, 2);
    /// assert!(value.is_identity());
    /// ```
    pub fn is_identity(&self) -> bool {
        1 == unsafe { fmpz_mat_is_one(&self.matrix) }
    }

    /// Checks if a [`MatZ`] is a square matrix.
    ///
    /// Returns `true` if the number of rows and columns is identical.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let value = MatZ::from_str("[[4, 0],[0, 1]]").unwrap();
    /// assert!(value.is_square());
    /// ```
    pub fn is_square(&self) -> bool {
        1 == unsafe { fmpz_mat_is_square(&self.matrix) }
    }

    /// Checks if every entry of a [`MatZ`] is `0`.
    ///
    /// Returns `true` if every entry of the matrix is `0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let value = MatZ::from_str("[[0, 0],[0, 0]]").unwrap();
    /// assert!(value.is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        1 == unsafe { fmpz_mat_is_zero(&self.matrix) }
    }
}

#[cfg(test)]
mod test_is_identity {
    use super::MatZ;
    use std::str::FromStr;

    /// Ensure that is_identity returns `true` for identity matrices.
    #[test]
    fn identity_detection() {
        let ident = MatZ::identity(2, 2);
        let nosquare = MatZ::from_str("[[1, 0],[0, 1],[0, 0]]").unwrap();

        assert!(ident.is_identity());
        assert!(nosquare.is_identity());
        assert!(MatZ::identity(1, 1).is_identity());
        assert!(MatZ::identity(2, 4).is_identity());
        assert!(MatZ::identity(4, 4).is_identity());
    }

    /// Ensure that is_identity returns `false` for non-identity matrices.
    #[test]
    fn identity_rejection() {
        let small = MatZ::from_str("[[0, 0],[2, 0]]").unwrap();
        let large = MatZ::from_str(&format!("[[1, 0],[0, {}]]", (u128::MAX - 1) / 2 + 2)).unwrap();

        assert!(!(small.is_identity()));
        assert!(!(large.is_identity()));
    }
}

#[cfg(test)]
mod test_is_zero {
    use super::MatZ;
    use std::str::FromStr;

    /// Ensure that is_zero returns `true` for all zero matrices.
    #[test]
    fn zero_detection() {
        let zero_1 = MatZ::from_str("[[0, 0],[0, 0],[0, 0]]").unwrap();
        let zero_2 = MatZ::from_str("[[0, 0, 0, 0],[0, 0, 0, 0]]").unwrap();
        let zero_3 = MatZ::from_str("[[0, 0],[0, 0]]").unwrap();

        assert!(zero_1.is_zero());
        assert!(zero_2.is_zero());
        assert!(zero_3.is_zero());
    }

    /// Ensure that is_zero returns `false` for non-zero matrices.
    #[test]
    fn zero_rejection() {
        let small = MatZ::from_str("[[0, 0],[2, 0]]").unwrap();
        let large = MatZ::from_str(&format!("[[0, 0],[{}, 0]]", (u128::MAX - 1) / 2 + 1)).unwrap();

        assert!(!small.is_zero());
        assert!(!large.is_zero());
    }
}

#[cfg(test)]
mod test_is_square {
    use super::MatZ;
    use std::str::FromStr;

    /// Ensure that is_square returns `true` for square matrices.
    #[test]
    fn square_detection() {
        let square_1 = MatZ::from_str("[[0, 4],[0, 0]]").unwrap();
        let square_2 = MatZ::from_str("[[0, 6, 4],[0, 0, 1],[4, 6, 1]]").unwrap();

        assert!(square_1.is_square());
        assert!(square_2.is_square());
    }

    /// Ensure that is_square returns `false` for non-square matrices.
    #[test]
    fn square_rejection() {
        let small = MatZ::from_str("[[0, 0, 4],[2, 0, 1]]").unwrap();
        let large =
            MatZ::from_str(&format!("[[9, 0],[{}, 0],[1, 4]]", (u128::MAX - 1) / 2 + 1)).unwrap();

        assert!(!small.is_square());
        assert!(!large.is_square());
    }
}
