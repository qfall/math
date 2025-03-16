// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute several norms
//! defined on matrices.

use super::MatQ;
use crate::{
    rational::Q,
    traits::{MatrixDimensions, MatrixGetSubmatrix},
};

impl MatQ {
    /// Outputs the squared l_{2, ∞}-norm, i.e. it computes the squared Euclidean
    /// norm of each column of the matrix and returns the largest one.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{MatQ, Q};
    /// use std::str::FromStr;
    ///
    /// let vec = MatQ::from_str("[[2, 3],[-2/1, 0]]").unwrap();
    ///
    /// let eucl_norm = vec.norm_l_2_infty_sqrd();
    ///
    /// // 3^2 + 0^2 = 9
    /// assert_eq!(Q::from(9), eucl_norm);
    /// ```
    pub fn norm_l_2_infty_sqrd(&self) -> Q {
        let mut max_sqrd_norm = Q::ZERO;
        for i in 0..self.get_num_columns() {
            let column = self.get_column(i).unwrap();
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
    /// use qfall_math::rational::{Q, MatQ};
    /// use std::str::FromStr;
    ///
    /// let vec = MatQ::from_str("[[4/2, 3],[2, 0]]").unwrap();
    ///
    /// let eucl_norm = vec.norm_l_2_infty();
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
    /// use qfall_math::rational::{MatQ, Q};
    /// use std::str::FromStr;
    ///
    /// let vec = MatQ::from_str("[[2, 6/2],[2, 0]]").unwrap();
    ///
    /// let eucl_norm = vec.norm_l_infty_infty();
    ///
    /// // max{2, 3} = 3
    /// assert_eq!(Q::from(3), eucl_norm);
    /// ```
    pub fn norm_l_infty_infty(&self) -> Q {
        let mut max_norm = Q::ZERO;
        for i in 0..self.get_num_columns() {
            let column = self.get_column(i).unwrap();
            let norm = column.norm_infty().unwrap();
            if norm > max_norm {
                max_norm = norm;
            }
        }
        max_norm
    }
}

#[cfg(test)]
mod test_matrix_norms {
    use super::{MatQ, Q};
    use std::str::FromStr;

    /// Ensures that the squared l_{2, ∞}-norm is correctly computed.
    #[test]
    fn norm_sqrd_l_2_infty() {
        let mat = MatQ::from_str("[[3, -2/1, 5],[-10/2, -6, 2],[4/-1, 0/1, 0],[2, 0, 1]]").unwrap();

        let sqrd_norm = mat.norm_l_2_infty_sqrd();

        assert_eq!(Q::from(54), sqrd_norm);
    }

    /// Ensures that the l_{2, ∞}-norm is correctly computed.
    #[test]
    fn norm_l_2_infty() {
        let mat = MatQ::from_str("[[-2, -2/1],[-2, 3/-1],[-2, 0],[2, 0]]").unwrap();

        let norm = mat.norm_l_2_infty();

        assert_eq!(Q::from(4), norm);
    }

    /// Ensures that the l_{∞, ∞}-norm is correctly computed.
    #[test]
    fn norm_l_infty_infty() {
        let mat = MatQ::from_str("[[-4/2, 3/1],[2, -5],[-2, 0]]").unwrap();

        let infty_norm = mat.norm_l_infty_infty();

        assert_eq!(Q::from(5), infty_norm);
    }
}
