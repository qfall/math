// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `determinant` function.

use super::MatZ;
use crate::{
    error::MathError,
    integer::Z,
    traits::{GetNumColumns, GetNumRows},
};
use flint_sys::fmpz_mat::fmpz_mat_det;

impl MatZ {
    /// Returns the determinant of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZ::from_str("[[1, 2],[3, 4]]").unwrap();
    /// let matrix_invert = matrix.det().unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of rows and columns is not equal.
    pub fn det(&self) -> Result<Z, MathError> {
        if self.get_num_rows() != self.get_num_columns() {
            return Err(MathError::MismatchingMatrixDimension(
                "The matrix is not square".to_string(),
            ));
        }

        let mut det = Z::default();
        unsafe {
            fmpz_mat_det(&mut det.value, &self.matrix);
        }
        Ok(det)
    }
}

#[cfg(test)]
mod test_determinant {
    use crate::integer::{MatZ, Z};
    use std::str::FromStr;

    /// Test whether the determinant is correctly computed
    #[test]
    fn determinant_works() {
        let mat1 = MatZ::from_str("[[5, 2],[2, 1]]").unwrap();
        let mat2 = MatZ::from_str(&format!("[[{}, 0],[0, 1]]", i64::MAX)).unwrap();
        let mat3 = MatZ::from_str(&format!("[[{}]]", i64::MIN)).unwrap();
        let mat4 = MatZ::from_str("[[0, 0],[0, 1]]").unwrap();
        let mat5 = MatZ::from_str("[[6, 0, 1],[0, 1, 0],[1, 2, 3]]").unwrap();

        let det1 = mat1.det().unwrap();
        let det2 = mat2.det().unwrap();
        let det3 = mat3.det().unwrap();
        let det4 = mat4.det().unwrap();
        let det5 = mat5.det().unwrap();

        let cmp1 = Z::ONE;
        let cmp2 = Z::from(i64::MAX);
        let cmp3 = Z::from(i64::MIN);
        let cmp4 = Z::ZERO;
        let cmp5 = Z::from(17);

        assert_eq!(cmp1, det1);
        assert_eq!(cmp2, det2);
        assert_eq!(cmp3, det3);
        assert_eq!(cmp4, det4);
        assert_eq!(cmp5, det5);
    }

    /// Ensure that an error is returned if the entered matrix is not square
    #[test]
    fn not_square_error() {
        let mat1 = MatZ::from_str("[[5],[2]]").unwrap();
        let mat2 = MatZ::from_str("[[2, 0],[0, 1],[8, -6]]").unwrap();

        assert!(mat1.det().is_err());
        assert!(mat2.det().is_err());
    }
}
