// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute several norms
//! defined on matrices.

use super::MatPolynomialRingZq;
use crate::{
    integer::Z,
    rational::Q,
    traits::{MatrixDimensions, MatrixGetSubmatrix},
};

impl MatPolynomialRingZq {
    /// Outputs the squared l_{2, ∞}-norm, i.e. it computes the squared Euclidean
    /// norm of each column of the matrix and returns the largest one.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq}, integer::{Z, MatPolyOverZ}};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 7").unwrap();
    /// let mat = MatPolyOverZ::from_str("[[1  2, 1  3],[1  2, 0]]").unwrap();
    /// let mat = MatPolynomialRingZq::from((&mat, &modulus));
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
    /// use qfall_math::{integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq}, integer::{Z, MatPolyOverZ}};
    /// use std::str::FromStr;
    /// # use qfall_math::rational::Q;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 5").unwrap();
    /// let mat = MatPolyOverZ::from_str("[[1  2, 1  3],[1  2, 1  0],[1  3, 1  4],[1  3, 1  4]]").unwrap();
    /// let mat = MatPolynomialRingZq::from((&mat, &modulus));
    ///
    /// let eucl_norm = mat.norm_l_2_infty();
    ///
    /// // sqrt(4 * 2^2) = 4
    /// assert_eq!(Q::from(4), eucl_norm);
    /// ```
    pub fn norm_l_2_infty(&self) -> Q {
        self.norm_l_2_infty_sqrd().sqrt()
    }

    /// Outputs the l_{∞, ∞}-norm, i.e. it computes the ∞-norm
    /// of each column of the matrix and returns the largest one.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq}, integer::{Z, MatPolyOverZ}};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 7").unwrap();
    /// let mat = MatPolyOverZ::from_str("[[1  2, 1  4],[1  2, 0]]").unwrap();
    /// let mat = MatPolynomialRingZq::from((&mat, &modulus));
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
}

#[cfg(test)]
mod test_matrix_norms {
    use super::{MatPolynomialRingZq, Q, Z};
    use crate::{integer::MatPolyOverZ, integer_mod_q::ModulusPolynomialRingZq};
    use std::str::FromStr;

    /// Ensures that the squared l_{2, ∞}-norm is correctly computed.
    #[test]
    fn norm_sqrd_l_2_infty() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 9").unwrap();
        let mat = MatPolyOverZ::from_str(
            "[[1  3, 1  -2, 1  5],[1  -5, 1  -6, 2  1 1],[1  -4, 0, 0],[1  2, 0, 3  1 1 1]]",
        )
        .unwrap();
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        let sqrd_norm = mat.norm_l_2_infty_sqrd();

        assert_eq!(Z::from(45), sqrd_norm);
    }

    /// Ensures that the l_{2, ∞}-norm is correctly computed.
    #[test]
    fn norm_l_2_infty() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 5").unwrap();
        let mat =
            MatPolyOverZ::from_str("[[1  -2, 4  -2 0 0 1],[1  -2, 1  -3],[1  -2, 0],[1  2, 0]]")
                .unwrap();
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        let norm = mat.norm_l_2_infty();

        assert_eq!(Q::from(4), norm);
    }

    /// Ensures that the l_{∞, ∞}-norm is correctly computed.
    #[test]
    fn norm_l_infty_infty() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 8").unwrap();
        let mat = MatPolyOverZ::from_str("[[2  -2 1, 1  3],[1  2, 1  -5],[1  -2, 0]]").unwrap();
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        let infty_norm = mat.norm_l_infty_infty();

        assert_eq!(Z::from(3), infty_norm);
    }
}
