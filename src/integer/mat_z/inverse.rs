// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `inverse` function.

use flint_sys::{
    fmpz::fmpz,
    fmpz_mat::{fmpz_mat_det, fmpz_mat_inv},
};

use crate::{
    error::MathError,
    integer::Z,
    traits::{GetNumColumns, GetNumRows},
};

use super::MatZ;

impl MatZ {
    /// Returns the inverse of the matrix if it exists (is squared and
    /// has a determinant unequal to zero) and has only [`Z`] values
    /// (has a determinant of '1' or '-1').
    ///
    /// # Example
    /// ```rust
    /// use qfall_math::integer::MatZ;
    /// use crate::qfall_math::traits::*;
    ///
    /// let mut matrix = MatZ::new(2, 2).unwrap();
    /// matrix.set_entry(0, 0, 1);
    /// matrix.set_entry(1, 1, 1);
    /// let matrix2 = matrix.invert().unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    pub fn invert(&self) -> Result<Self, MathError> {
        // check if matrix is squared
        if self.get_num_rows() != self.get_num_columns() {
            return Err(MathError::MismatchingMatrixDimension(
                "The matrix is not invertible as it does not have square dimensions.".to_string(),
            ));
        }

        // calculate determinant to check whether matrix is invertible or not
        let mut det = fmpz::default();
        unsafe {
            fmpz_mat_det(&mut det, &self.matrix);
        }
        let det = Z { value: det };
        if det == Z::ZERO {
            return Err(MathError::InvalidInversion(
                "The matrix is not invertible as its determinant is 0.".to_string(),
            ));
        }
        if det != Z::ONE && det != Z::MINUS_ONE {
            return Err(MathError::InvalidInversion(
                "The matrix is invertible, but not all of the invertible entries are integers."
                    .to_string(),
            ));
        }

        // create new matrix to store inverted result in
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        let mut den = fmpz::default();
        unsafe {
            fmpz_mat_inv(&mut out.matrix, &mut den, &self.matrix);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_inverse {
    use std::str::FromStr;

    use crate::integer::MatZ;

    /// test whether invert correctly calculates an inverse matrix if its
    /// entries are in [`Z`](crate::integer::Z)
    #[test]
    fn invert_works() {
        let mat = MatZ::from_str("[[5,2],[2,1]]").unwrap();
        let cmp = MatZ::from_str("[[1,-2],[-2,5]]").unwrap();

        let inv = mat.invert().unwrap();

        assert_eq!(cmp, inv);
    }

    /// check if the multiplication of inverse and matrix result in a diagonal
    /// matrix with uniform values on the diagonal
    #[test]
    fn invert_correct() {
        let mat = MatZ::from_str("[[5,2],[2,1]]").unwrap();
        let cmp = MatZ::from_str("[[1,0],[0,1]]").unwrap();

        let inv = mat.invert().unwrap();
        let diag = &mat * &inv;

        assert_eq!(cmp, diag);
    }

    /// Ensure that a matrix that is not a spare yields an Error on inversion.
    #[test]
    fn inv_error_not_squared() {
        let mat = MatZ::from_str("[[1,0,1],[0,1,1]]").unwrap();

        assert!(mat.invert().is_err());
    }

    /// Ensure that a matrix that has a determinant of '0' yields an Error on inversion.
    #[test]
    fn inv_error_det_zero() {
        let mat = MatZ::from_str("[[2,0],[0,1]]").unwrap();

        assert!(mat.invert().is_err());
    }

    /// Ensure that a matrix that has a determinant of '1' or '-1'
    /// yields an Error on inversion.
    #[test]
    fn inv_error_not_z() {
        let mat = MatZ::from_str("[[2,0],[0,1]]").unwrap();

        assert!(mat.invert().is_err());
    }
}
