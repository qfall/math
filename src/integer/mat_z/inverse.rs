// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `inverse` function.

use super::MatZ;
use crate::{
    rational::MatQ,
    traits::{GetNumColumns, GetNumRows},
};
use flint_sys::fmpq_mat::fmpq_mat_inv;

impl MatZ {
    /// Returns the inverse of the matrix if it exists (is square and
    /// has a determinant unequal to zero) and `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZ::from_str("[[1, 2],[3, 4]]").unwrap();
    /// let matrix_invert = matrix.inverse().unwrap();
    /// ```
    pub fn inverse(&self) -> Option<MatQ> {
        // check if matrix is square
        if self.get_num_rows() != self.get_num_columns() {
            return None;
        }

        // check if determinant is not `0`, create new matrix to store inverted result in
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns());
        match unsafe { fmpq_mat_inv(&mut out.matrix, &MatQ::from(self).matrix) } {
            0 => None,
            _ => Some(out),
        }
    }
}

#[cfg(test)]
mod test_inverse {
    use crate::{integer::MatZ, rational::MatQ};
    use std::str::FromStr;

    /// Test whether `inverse` correctly calculates an inverse matrix
    #[test]
    fn inverse_works() {
        let mat_1 = MatZ::from_str("[[5, 2, 0],[2, 1, 0],[0, 0, 1]]").unwrap();
        let mat_2 = MatZ::from_str(&format!("[[{}]]", i64::MAX)).unwrap();
        let mat_3 = MatZ::from_str("[[-1, 0],[0, 1]]").unwrap();

        let cmp_inv_1 = MatQ::from_str("[[1, -2, 0],[-2, 5, 0],[0, 0, 1]]").unwrap();
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
        let mat = MatZ::from_str("[[5, 2],[2, 1]]").unwrap();
        let mat_q = MatQ::from(&mat);
        let cmp = MatQ::identity(2, 2);

        let inv = mat.inverse().unwrap();
        let diag = &mat_q * &inv;

        assert_eq!(cmp, diag);
    }

    /// Ensure that a matrix that is not square yields `None` on inversion.
    #[test]
    fn inv_none_not_squared() {
        let mat_1 = MatZ::from_str("[[1, 0, 1],[0, 1, 1]]").unwrap();
        let mat_2 = MatZ::from_str("[[1, 0],[0, 1],[1, 0]]").unwrap();

        assert!(mat_1.inverse().is_none());
        assert!(mat_2.inverse().is_none());
    }

    /// Ensure that a matrix that has a determinant of `0` yields `None` on inversion.
    #[test]
    fn inv_none_det_zero() {
        let mat = MatZ::from_str("[[2, 0],[0, 0]]").unwrap();

        assert!(mat.inverse().is_none());
    }
}
