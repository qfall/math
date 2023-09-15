// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `inverse` function.

use super::MatQ;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpq_mat::fmpq_mat_inv;

impl MatQ {
    /// Returns the inverse of the matrix if it exists (is square and
    /// has a determinant unequal to `0`) and `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatQ::from_str("[[1/2, 2],[3/4, 4]]").unwrap();
    /// let matrix_invert = matrix.inverse().unwrap();
    /// ```
    pub fn inverse(&self) -> Option<MatQ> {
        // check if matrix is square
        if self.get_num_rows() != self.get_num_columns() {
            return None;
        }

        // check if determinant is not `0`, create new matrix to store inverted result in
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns());
        match unsafe { fmpq_mat_inv(&mut out.matrix, &self.matrix) } {
            0 => None,
            _ => Some(out),
        }
    }
}

#[cfg(test)]
mod test_inverse {
    use crate::rational::MatQ;
    use std::str::FromStr;

    /// Test whether `inverse` correctly calculates an inverse matrix
    #[test]
    fn inverse_works() {
        let mat_1 = MatQ::from_str("[[5/3, 2, 0],[6, 1, 0],[0, 0, 1/2]]").unwrap();
        let mat_2 = MatQ::from_str(&format!("[[{}]]", i64::MAX)).unwrap();
        let mat_3 = MatQ::from_str("[[-1, 0],[0, 1]]").unwrap();

        let cmp_inv_1 = MatQ::from_str("[[-3/31, 6/31, 0],[18/31, -5/31, 0],[0, 0, 2]]").unwrap();
        let cmp_inv_2 = MatQ::from_str(&format!("[[1/{}]]", i64::MAX)).unwrap();
        let cmp_inv_3 = MatQ::from_str("[[-1, 0],[0, 1]]").unwrap();

        let inv_1 = mat_1.inverse().unwrap();
        let inv_2 = mat_2.inverse().unwrap();
        let inv_3 = mat_3.inverse().unwrap();

        assert_eq!(cmp_inv_1, inv_1);
        assert_eq!(cmp_inv_2, inv_2);
        assert_eq!(cmp_inv_3, inv_3);
    }

    /// Check if the multiplication of inverse and matrix result in an identity matrix
    #[test]
    fn inverse_correct() {
        let mat = MatQ::from_str("[[5/6, 2],[2/9, 1/3]]").unwrap();
        let cmp = MatQ::identity(2, 2);

        let inv = mat.inverse().unwrap();
        let diag = &mat * &inv;

        assert_eq!(cmp, diag);
    }

    /// Ensure that a matrix that is not square yields `None` on inversion.
    #[test]
    fn inv_none_not_squared() {
        let mat_1 = MatQ::from_str("[[1, 0, 1],[0, 1, 1]]").unwrap();
        let mat_2 = MatQ::from_str("[[1, 0],[0, 1],[1, 0]]").unwrap();

        assert!(mat_1.inverse().is_none());
        assert!(mat_2.inverse().is_none());
    }

    /// Ensure that a matrix that has a determinant of `0` yields `None` on inversion.
    #[test]
    fn inv_none_det_zero() {
        let mat = MatQ::from_str("[[2, 0],[0, 0]]").unwrap();

        assert!(mat.inverse().is_none());
    }
}
