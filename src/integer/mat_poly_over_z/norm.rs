// Copyright 2025 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute several norms
//! defined on matrices.

use super::MatPolyOverZ;
use crate::{
    integer::Z,
    rational::Q,
    traits::{MatrixDimensions, MatrixGetEntry, MatrixGetSubmatrix},
};

impl MatPolyOverZ {
    /// Outputs the squared l_{2, ∞}-norm, i.e. it computes the squared Euclidean
    /// norm of each column of the matrix and returns the largest one.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatPolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let mat = MatPolyOverZ::from_str("[[1  2, 1  3],[1  2, 0]]").unwrap();
    ///
    /// let eucl_norm = mat.norm_l_2_infty_sqrd();
    ///
    /// // 3^2 + 0^2 = 9
    /// assert_eq!(Z::from(9), eucl_norm);
    /// ```
    pub fn norm_l_2_infty_sqrd(&self) -> Z {
        let mut max_sqrd_norm = Z::ZERO;
        for i in 0..self.get_num_columns() {
            let column = unsafe { self.get_column_unchecked(i) };
            let sqrd_norm = column.norm_eucl_sqrd().unwrap();
            if sqrd_norm > max_sqrd_norm {
                max_sqrd_norm = sqrd_norm;
            }
        }
        max_sqrd_norm
    }

    /// Outputs the l_{2, ∞}-norm, i.e. it computes the Euclidean
    /// norm of each column of the matrix and returns the largest one.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::MatPolyOverZ, rational::Q};
    /// use std::str::FromStr;
    ///
    /// let mat = MatPolyOverZ::from_str("[[1  2, 1  3],[1  2, 0]]").unwrap();
    ///
    /// let eucl_norm = mat.norm_l_2_infty();
    ///
    /// // sqrt(3^2 + 0^2) = 3
    /// assert_eq!(Q::from(3), eucl_norm);
    /// ```
    pub fn norm_l_2_infty(&self) -> Q {
        self.norm_l_2_infty_sqrd().sqrt()
    }

    /// Outputs the l_{∞, ∞}-norm, i.e. it computes the ∞-norm
    /// of each column of the matrix and returns the largest one.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatPolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let mat = MatPolyOverZ::from_str("[[1  2, 1  3],[1  2, 0]]").unwrap();
    ///
    /// let eucl_norm = mat.norm_l_infty_infty();
    ///
    /// // max{2, 3} = 3
    /// assert_eq!(Z::from(3), eucl_norm);
    /// ```
    pub fn norm_l_infty_infty(&self) -> Z {
        let mut max_norm = Z::ZERO;
        for i in 0..self.get_num_columns() {
            let column = unsafe { self.get_column_unchecked(i) };
            let norm = column.norm_infty().unwrap();
            if norm > max_norm {
                max_norm = norm;
            }
        }
        max_norm
    }

    /// Outputs the hamming weight of `self`, i.e. it computes the sum of all non-zero
    /// coefficients in each polynomial in the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mat = MatPolyOverZ::from_str("[[2  2 1, 2  3 0],[1  2, 0]]").unwrap();
    ///
    /// let hamming_weight = mat.hamming_weight();
    ///
    /// assert_eq!(4, hamming_weight);
    /// ```
    pub fn hamming_weight(&self) -> i64 {
        let mut hamming_weight = 0;
        for row in 0..self.get_num_rows() {
            for col in 0..self.get_num_columns() {
                let entry = unsafe { self.get_entry_unchecked(row, col) };
                hamming_weight += entry.hamming_weight();
            }
        }
        hamming_weight
    }
}

#[cfg(test)]
mod test_matrix_norms {
    use super::{MatPolyOverZ, Q, Z};
    use std::str::FromStr;

    /// Ensures that the squared l_{2, ∞}-norm is correctly computed.
    #[test]
    fn norm_sqrd_l_2_infty() {
        let mat = MatPolyOverZ::from_str(
            "[[1  3, 1  -2, 1  5],[1  -5, 1  -6, 2  2 1],[1  -4, 0, 0],[1  2, 0, 1  1]]",
        )
        .unwrap();

        let sqrd_norm = mat.norm_l_2_infty_sqrd();

        assert_eq!(Z::from(54), sqrd_norm);
    }

    /// Ensures that the l_{2, ∞}-norm is correctly computed.
    #[test]
    fn norm_l_2_infty() {
        let mat =
            MatPolyOverZ::from_str("[[1  -2, 3  -2 1 1],[1  -2, 1  -3],[1  -2, 0],[1  2, 0]]")
                .unwrap();

        let norm = mat.norm_l_2_infty();

        assert_eq!(Q::from(4), norm);
    }

    /// Ensures that the l_{∞, ∞}-norm is correctly computed.
    #[test]
    fn norm_l_infty_infty() {
        let mat = MatPolyOverZ::from_str("[[2  -2 1, 1  3],[1  2, 1  -5],[1  -2, 0]]").unwrap();

        let infty_norm = mat.norm_l_infty_infty();

        assert_eq!(Z::from(5), infty_norm);
    }
}

#[cfg(test)]
mod test_hamming_weight {
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensures that the hamming weight is computed correctly.
    #[test]
    fn hamming_weight() {
        let mat0 = MatPolyOverZ::new(3, 4);
        let mat1 = MatPolyOverZ::from_str("[[1  -2, 2  3 2],[2  2 0, 1  -5],[1  -2, 0]]").unwrap();

        let hw0 = mat0.hamming_weight();
        let hw1 = mat1.hamming_weight();

        assert_eq!(0, hw0);
        assert_eq!(6, hw1);
    }
}
