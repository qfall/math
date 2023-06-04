// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to check certain properties of [`MatZ`]
//! This includes checks such as squareness.

use super::MatZ;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_mat::fmpz_mat_is_one;

impl MatZ {
    /// Checks if a [`MatZ`] is a identity matrix, i.e.
    /// all entries on the diagonal are `1` and `0` elsewhere.
    ///
    /// Returns `true` if the matrix is the identity and `false` otherwise.
    ///
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::integer::MatZ;
    ///
    /// let matrix = MatZ::from_str("[[1, 0],[0, 1]]").unwrap();
    /// let check = matrix.is_identity();
    /// # assert!(check)
    /// ```
    pub fn is_identity(&self) -> bool {
        // we have to test squareness manually, since FLINT does not check this
        // directly with their method
        unsafe { 0 != fmpz_mat_is_one(&self.matrix) && self.is_square() }
    }

    /// Checks if a [`MatZ`] is a square matrix, i.e.
    /// the number of rows and columns is identical.
    ///
    /// Returns `true` if the matrix is the square and `false` otherwise.
    ///
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::integer::MatZ;
    ///
    /// let matrix = MatZ::from_str("[[1, 0],[0, 1]]").unwrap();
    /// let check = matrix.is_square();
    /// # assert!(check)
    /// ```
    pub fn is_square(&self) -> bool {
        self.get_num_columns() == self.get_num_rows()
    }
}

#[cfg(test)]
mod test_is_identity {
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensure that true is returned for a 1x1, 2x2, 3x3 identity matrix
    #[test]
    fn identity_true() {
        let matrix_1x1 = MatZ::from_str("[[1]]").unwrap();
        let matrix_2x2 = MatZ::from_str("[[1, 0],[0, 1]]").unwrap();
        let matrix_3x3 = MatZ::from_str("[[1, 0, 0],[0, 1, 0],[0, 0, 1]]").unwrap();

        assert!(matrix_1x1.is_identity());
        assert!(matrix_2x2.is_identity());
        assert!(matrix_3x3.is_identity());
    }

    /// Ensure that matrices which are not square do not return true
    #[test]
    fn not_square() {
        let matrix_1x2 = MatZ::from_str("[[1, 0]]").unwrap();
        let matrix_2x1 = MatZ::from_str("[[1],[0]]").unwrap();
        let matrix_2x3 = MatZ::from_str("[[1, 0, 0],[0, 1, 0]]").unwrap();
        let matrix_3x2 = MatZ::from_str("[[1, 0],[0, 1],[0, 0]]").unwrap();

        assert!(!matrix_1x2.is_identity());
        assert!(!matrix_2x1.is_identity());
        assert!(!matrix_2x3.is_identity());
        assert!(!matrix_3x2.is_identity());
    }

    /// Ensure that matrices which are square but are not the identity matrix, return false
    #[test]
    fn not_identity() {
        let matrix_side_entry = MatZ::from_str("[[1, 1],[0, 1]]").unwrap();
        let matrix_negative_1 = MatZ::from_str("[[-1, 0],[0, 1]]").unwrap();
        let matrix_negative_2 = MatZ::from_str("[[-17, 0],[0, 1]]").unwrap();
        let matrix_higher_degree = MatZ::from_str("[[1, 0],[0, 42]]").unwrap();
        let matrix_matrix_positive = MatZ::from_str("[[17, 0],[0, 1]]").unwrap();
        let matrix_large_negative =
            MatZ::from_str(&format!("[[-{}, 0],[0, 1]]", u64::MAX)).unwrap();
        let matrix_large_positive = MatZ::from_str(&format!("[[{}, 0],[0, 1]]", u64::MAX)).unwrap();

        assert!(!matrix_side_entry.is_identity());
        assert!(!matrix_negative_1.is_identity());
        assert!(!matrix_negative_2.is_identity());
        assert!(!matrix_higher_degree.is_identity());
        assert!(!matrix_matrix_positive.is_identity());
        assert!(!matrix_large_negative.is_identity());
        assert!(!matrix_large_positive.is_identity());
    }
}

#[cfg(test)]
mod test_is_square {
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensure that square matrices return true
    #[test]
    fn square_matrix() {
        let matrix_negative = MatZ::from_str("[[-17, 0, 0],[0, 1, 0],[0, 0, 0]]").unwrap();
        let matrix_higher_degree = MatZ::from_str("[[1, 0],[0, 42]]").unwrap();
        let matrix_matrix_positive = MatZ::from_str("[[17]]").unwrap();
        let matrix_large_negative =
            MatZ::from_str(&format!("[[-{}, 0],[0, 1]]", u64::MAX)).unwrap();
        let matrix_large_positive = MatZ::from_str(&format!(
            "[[{}, 0, 0, 0],[0, 1, 0, 0],[0, 1, 0, 0],[0, 1, 0, 0]]",
            u64::MAX
        ))
        .unwrap();

        assert!(matrix_negative.is_square());
        assert!(matrix_matrix_positive.is_square());
        assert!(matrix_higher_degree.is_square());
        assert!(matrix_large_negative.is_square());
        assert!(matrix_large_positive.is_square());
    }

    /// Ensure that non-square matrices return false
    #[test]
    fn not_square_matrix() {
        let matrix_1x2 = MatZ::from_str("[[1, 1]]").unwrap();
        let matrix_2x1 = MatZ::from_str("[[1],[0]]").unwrap();
        let matrix_2x3 = MatZ::from_str("[[1, 0, 0],[0, 1, 0]]").unwrap();
        let matrix_3x2 = MatZ::from_str("[[1, 0],[0, 1],[0, 0]]").unwrap();

        assert!(!matrix_1x2.is_square());
        assert!(!matrix_2x1.is_square());
        assert!(!matrix_2x3.is_square());
        assert!(!matrix_3x2.is_square());
    }
}
