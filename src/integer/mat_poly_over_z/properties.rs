// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to check certain properties of [`MatPolyOverZ`]
//! This includes checks such as squareness.

use super::MatPolyOverZ;
use crate::{
    integer::Z,
    traits::{GetEntry, MatrixDimensions},
};
use flint_sys::fmpz_poly_mat::{fmpz_poly_mat_is_one, fmpz_poly_mat_is_zero, fmpz_poly_mat_rank};

impl MatPolyOverZ {
    /// Checks if a [`MatPolyOverZ`] is a identity matrix, i.e.
    /// all entries on the diagonal are the constant polynomial `1` and `0` elsewhere.
    ///
    /// Returns `true` if the matrix is the identity and `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1]]").unwrap();
    ///
    /// assert!(matrix.is_identity());
    /// ```
    pub fn is_identity(&self) -> bool {
        1 == unsafe { fmpz_poly_mat_is_one(&self.matrix) }
    }

    /// Checks if a [`MatPolyOverZ`] is a square matrix, i.e.
    /// the number of rows and columns is identical.
    ///
    /// Returns `true` if the number of rows and columns is identical.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1]]").unwrap();
    /// let check = matrix.is_square();
    /// # assert!(check);
    /// ```
    pub fn is_square(&self) -> bool {
        self.get_num_columns() == self.get_num_rows()
    }

    /// Checks if a [`MatPolyOverZ`] is a zero matrix, i.e.
    /// all entries are the constant polynomial `0` everywhere.
    ///
    /// Returns `true` if the matrix is zero and `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[0, 0],[0, 0]]").unwrap();
    /// let check = matrix.is_zero();
    /// # assert!(check);
    /// ```
    pub fn is_zero(&self) -> bool {
        // we have to test squareness manually, since FLINT does not check this
        // directly with their method
        unsafe { 0 != fmpz_poly_mat_is_zero(&self.matrix) }
    }

    /// Checks if a [`MatPolyOverZ`] is symmetric.
    ///
    /// Returns `true` if we have `a_ij == a_ji` for all i,j.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let value = MatPolyOverZ::identity(2,2);
    /// assert!(value.is_symmetric());
    /// ```
    pub fn is_symmetric(&self) -> bool {
        if !self.is_square() {
            return false;
        }
        for row in 0..self.get_num_rows() {
            for column in 0..row {
                if unsafe {
                    self.get_entry_unchecked(row, column) != self.get_entry_unchecked(column, row)
                } {
                    return false;
                }
            }
        }
        true
    }

    /// Returns the rank of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  1, 0, 0],[0, 0, 1  1]]").unwrap();
    ///
    /// let rank = matrix.rank();
    /// ```
    pub fn rank(&self) -> Z {
        Z::from(unsafe { fmpz_poly_mat_rank(&self.matrix) })
    }
}

#[cfg(test)]
mod test_is_identity {
    use crate::integer::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensure that true is returned for a 1x1, 2x2, 3x3, 2x3, 3x2 identity matrix.
    #[test]
    fn identity_true() {
        let matrix_1x1 = MatPolyOverZ::from_str("[[1  1]]").unwrap();
        let matrix_2x2 = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1]]").unwrap();
        let matrix_3x3 =
            MatPolyOverZ::from_str("[[1  1, 0, 0],[0, 1  1, 0],[0, 0, 1  1]]").unwrap();
        let matrix_2x3 = MatPolyOverZ::from_str("[[1  1, 0, 0],[0, 1  1, 0]]").unwrap();
        let matrix_3x2 = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1],[0, 0]]").unwrap();

        assert!(matrix_1x1.is_identity());
        assert!(matrix_2x2.is_identity());
        assert!(matrix_3x3.is_identity());
        assert!(matrix_2x3.is_identity());
        assert!(matrix_3x2.is_identity());
    }

    /// Ensure that matrices which are square but are not the identity matrix, return false.
    #[test]
    fn not_identity() {
        let matrix_side_entry = MatPolyOverZ::from_str("[[1  1, 1  1],[0, 1  1]]").unwrap();
        let matrix_negative_1 = MatPolyOverZ::from_str("[[1  -1, 0],[0, 1  1]]").unwrap();
        let matrix_negative_2 = MatPolyOverZ::from_str("[[1  -17, 0],[0, 1  1]]").unwrap();
        let matrix_higher_degree = MatPolyOverZ::from_str("[[1  1, 0],[0, 2  1 42]]").unwrap();
        let matrix_matrix_positive = MatPolyOverZ::from_str("[[1  17, 0],[0, 1  1]]").unwrap();
        let matrix_large_negative =
            MatPolyOverZ::from_str(&format!("[[1  -{}, 0],[0, 1  1]]", u64::MAX)).unwrap();
        let matrix_large_positive =
            MatPolyOverZ::from_str(&format!("[[1  {}, 0],[0, 1  1]]", u64::MAX)).unwrap();

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
    use crate::integer::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensure that square matrices return true
    #[test]
    fn square_matrix() {
        let matrix_negative =
            MatPolyOverZ::from_str("[[1  -17, 0, 0],[0, 1  1, 0],[0, 0, 0]]").unwrap();
        let matrix_higher_degree = MatPolyOverZ::from_str("[[1  1, 0],[0, 2  1 42]]").unwrap();
        let matrix_matrix_positive = MatPolyOverZ::from_str("[[1  17]]").unwrap();
        let matrix_large_negative =
            MatPolyOverZ::from_str(&format!("[[1  -{}, 0],[0, 1  1]]", u64::MAX)).unwrap();
        let matrix_large_positive = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 0, 0, 0],[0, 1  1, 0, 0],[0, 1  1, 0, 0],[0, 1  1, 0, 0]]",
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
        let matrix_1x2 = MatPolyOverZ::from_str("[[1  1, 0]]").unwrap();
        let matrix_2x1 = MatPolyOverZ::from_str("[[1  1],[0]]").unwrap();
        let matrix_2x3 = MatPolyOverZ::from_str("[[1  1, 0, 0],[0, 1  1, 0]]").unwrap();
        let matrix_3x2 = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1],[0, 0]]").unwrap();

        assert!(!matrix_1x2.is_square());
        assert!(!matrix_2x1.is_square());
        assert!(!matrix_2x3.is_square());
        assert!(!matrix_3x2.is_square());
    }
}

#[cfg(test)]
mod test_is_zero {
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensure that is_zero returns `true` for all zero matrices.
    #[test]
    fn zero_detection() {
        let zero = MatPolyOverZ::from_str("[[0, 0],[0, 0]]").unwrap();
        let zero_2 = MatPolyOverZ::from_str("[[0, 0],[0, 0],[0, 3  0 0 0]]").unwrap();

        assert!(zero.is_zero());
        assert!(zero_2.is_zero());
    }

    /// Ensure that is_zero returns `false` for non-zero matrices.
    #[test]
    fn zero_rejection() {
        let small = MatPolyOverZ::from_str("[[0, 0],[4  0 0 0 2, 0]]").unwrap();
        let large =
            MatPolyOverZ::from_str(&format!("[[0, 0],[1  {}, 0]]", (u128::MAX - 1) / 2 + 1))
                .unwrap();

        assert!(!small.is_zero());
        assert!(!large.is_zero());
    }
}

#[cfg(test)]
mod test_is_symmetric {
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensure that is_symmetric returns `false` for non-symmetric matrices.
    #[test]
    fn symmetric_rejection() {
        let mat_2x3 = MatPolyOverZ::from_str("[[0, 1  6, 2  1 4],[1  2, 0, 2  1 1]]").unwrap();
        let mat_2x2 = MatPolyOverZ::from_str("[[1  9, 0],[2  1 71, 0]]").unwrap();

        assert!(!mat_2x3.is_symmetric());
        assert!(!mat_2x2.is_symmetric());
    }

    /// Ensure that is_symmetric returns `true` for symmetric matrices.
    #[test]
    fn symmetric_detection() {
        let mat_2x2 = MatPolyOverZ::from_str(&format!(
            "[[2  1 {}, 2  3 {}],[2  3 {}, 3  1 {} 8]]",
            u64::MIN,
            u64::MAX,
            u64::MAX,
            i64::MAX
        ))
        .unwrap();

        assert!(mat_2x2.is_symmetric());
    }
}

#[cfg(test)]
mod test_rank {
    use crate::integer::{MatPolyOverZ, Z};
    use std::str::FromStr;

    /// Test whether the rank is correctly computed
    #[test]
    fn rank_works() {
        let mat_1 = MatPolyOverZ::from_str("[[1  5, 1  2],[1  2, 1  1]]").unwrap();
        let mat_2 = MatPolyOverZ::from_str(&format!(
            "[[2  {} 3, 0, 0, 0],[0, 0, 1  5, 1  7]]",
            i64::MIN
        ))
        .unwrap();
        let mat_3 = MatPolyOverZ::from_str("[[0],[0]]").unwrap();
        let mat_4 = MatPolyOverZ::from_str("[[0, 0],[0, 1  1]]").unwrap();
        let mat_5 = MatPolyOverZ::from_str("[[0, 1  1],[0, 1  5]]").unwrap();
        let mat_6 =
            MatPolyOverZ::from_str("[[1  6, 0, 1  1],[0, 1  1, 0],[2  1 5, 1  2, 0]]").unwrap();

        let rank_1 = mat_1.rank();
        let rank_2 = mat_2.rank();
        let rank_3 = mat_3.rank();
        let rank_4 = mat_4.rank();
        let rank_5 = mat_5.rank();
        let rank_6 = mat_6.rank();

        assert_eq!(Z::from(2), rank_1);
        assert_eq!(Z::from(2), rank_2);
        assert_eq!(Z::ZERO, rank_3);
        assert_eq!(Z::ONE, rank_4);
        assert_eq!(Z::ONE, rank_5);
        assert_eq!(Z::from(3), rank_6);
    }
}
