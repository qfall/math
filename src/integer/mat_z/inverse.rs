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
    error::MathError,
    integer::Z,
    rational::MatQ,
    traits::{GetNumColumns, GetNumRows},
};
use flint_sys::fmpq_mat::fmpq_mat_inv;

impl MatZ {
    /// Returns the inverse of the matrix if it exists (is squared and
    /// has a determinant unequal to zero).
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZ::from_str("[[1,2],[3,4]]").unwrap();
    /// let matrix_invert = matrix.invert().unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of rows and columns is not equal.
    /// - Returns a [`MathError`] of type [`NotInvertible`](MathError::NotInvertible)
    /// if the determinant of the matrix is `0`.
    pub fn invert(&self) -> Result<MatQ, MathError> {
        // check if matrix is square
        if self.get_num_rows() != self.get_num_columns() {
            return Err(MathError::MismatchingMatrixDimension(
                "The matrix is not invertible as it does not have square dimensions".to_string(),
            ));
        }

        // calculate determinant to check whether matrix is invertible or not
        let det = self.det();
        if det == Z::ZERO {
            return Err(MathError::NotInvertible(
                "The matrix is not invertible as its determinant is 0".to_string(),
            ));
        }

        // create new matrix to store inverted result in
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        unsafe {
            fmpq_mat_inv(&mut out.matrix, &MatQ::from(self).matrix);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_inverse {

    use crate::{integer::MatZ, rational::MatQ};
    use std::str::FromStr;

    /// Test whether invert correctly calculates an inverse matrix
    #[test]
    fn invert_works() {
        let mat1 = MatZ::from_str("[[5,2],[2,1]]").unwrap();
        let mat2 = MatZ::from_str(&format!("[[{},0],[0,1]]",i64::MAX)).unwrap();
        let mat3 = MatZ::from_str("[[-1,0],[0,1]]").unwrap();

        let cmp1 = MatQ::from_str("[[1,-2],[-2,5]]").unwrap();
        let cmp2 = MatQ::from_str(&format!("[[1/{},0],[0,1]]",i64::MAX)).unwrap();
        let cmp3 = MatQ::from_str("[[-1,0],[0,1]]").unwrap();

        let inv1 = mat1.invert().unwrap();
        let inv2 = mat2.invert().unwrap();
        let inv3 = mat3.invert().unwrap();

        assert_eq!(cmp1, inv1);
        assert_eq!(cmp2, inv2);
        assert_eq!(cmp3, inv3);
    }

    /// Check if the multiplication of inverse and matrix result in an identity matrix
    #[test]
    fn invert_correct() {
        let mat = MatZ::from_str("[[5,2],[2,1]]").unwrap();
        let mat_q = MatQ::from(&mat);
        let cmp = MatQ::from_str("[[1,0],[0,1]]").unwrap();

        let inv = mat.invert().unwrap();
        let diag = &mat_q * &inv;

        assert_eq!(cmp, diag);
    }

    /// Ensure that a matrix that is not square yields an Error on inversion.
    #[test]
    fn inv_error_not_squared() {
        let mat1 = MatZ::from_str("[[1,0,1],[0,1,1]]").unwrap();
        let mat2 = MatZ::from_str("[[1,0],[0,1],[1,0]]").unwrap();

        assert!(mat1.invert().is_err());
        assert!(mat2.invert().is_err());
    }

    /// Ensure that a matrix that has a determinant of '0' yields an Error on inversion.
    #[test]
    fn inv_error_det_zero() {
        let mat = MatZ::from_str("[[2,0],[0,0]]").unwrap();

        assert!(mat.invert().is_err());
    }
}
