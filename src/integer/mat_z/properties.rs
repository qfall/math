// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`MatZ`] instances.

use super::MatZ;
use crate::{
    integer::Z,
    traits::{GetEntry, MatrixDimensions},
};
use flint_sys::fmpz_mat::{fmpz_mat_is_one, fmpz_mat_is_square, fmpz_mat_is_zero, fmpz_mat_rank};

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

    /// Checks if a [`MatZ`] is symmetric.
    ///
    /// Returns `true` if we have `a_ij == a_ji` for all i,j.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let value = MatZ::identity(2,2);
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
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZ::from_str("[[1, 2, 3],[4, 5, 6]]").unwrap();
    ///
    /// let rank = matrix.rank();
    /// ```
    pub fn rank(&self) -> Z {
        Z::from(unsafe { fmpz_mat_rank(&self.matrix) })
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

#[cfg(test)]
mod test_is_symmetric {
    use super::MatZ;
    use std::str::FromStr;

    /// Ensure that is_symmetric returns `false` for non-symmetric matrices.
    #[test]
    fn symmetric_rejection() {
        let mat_2x3 = MatZ::from_str("[[0, 5, 4],[2, 0, 1]]").unwrap();
        let mat_2x2 = MatZ::from_str("[[9, 0],[71, 0]]").unwrap();

        assert!(!mat_2x3.is_symmetric());
        assert!(!mat_2x2.is_symmetric());
    }

    /// Ensure that is_symmetric returns `true` for symmetric matrices.
    #[test]
    fn symmetric_detection() {
        let mat_2x2 = MatZ::from_str(&format!(
            "[[{}, {}],[{}, {}]]",
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
    use crate::integer::{MatZ, Z};
    use std::str::FromStr;

    /// Test whether the rank is correctly computed
    #[test]
    fn rank_works() {
        let mat_1 = MatZ::from_str("[[5, 2],[2, 1]]").unwrap();
        let mat_2 = MatZ::from_str(&format!("[[{}, 0, 2, 8],[0, 1, 5, 7]]", i64::MIN)).unwrap();
        let mat_3 = MatZ::from_str("[[0],[0]]").unwrap();
        let mat_4 = MatZ::from_str("[[0, 0],[0, 1]]").unwrap();
        let mat_5 = MatZ::from_str("[[0, 1],[0, 5]]").unwrap();
        let mat_6 = MatZ::from_str("[[6, 0, 1],[0, 1, 0],[1, 2, 3]]").unwrap();

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
