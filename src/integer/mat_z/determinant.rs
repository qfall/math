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
    /// Returns the determinant of the matrix or an error if
    /// the number of rows and columns is not equal.
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
    ///     if the number of rows and columns is not equal.
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
        let mat_1 = MatZ::from_str("[[5, 2],[2, 1]]").unwrap();
        let mat_2 = MatZ::from_str(&format!("[[{}, 0],[0, 1]]", i64::MAX)).unwrap();
        let mat_3 = MatZ::from_str(&format!("[[{}]]", i64::MIN)).unwrap();
        let mat_4 = MatZ::from_str("[[0, 0],[0, 1]]").unwrap();
        let mat_5 = MatZ::from_str("[[6, 0, 1],[0, 1, 0],[1, 2, 3]]").unwrap();

        let det_1 = mat_1.det().unwrap();
        let det_2 = mat_2.det().unwrap();
        let det_3 = mat_3.det().unwrap();
        let det_4 = mat_4.det().unwrap();
        let det_5 = mat_5.det().unwrap();

        let cmp_1 = Z::ONE;
        let cmp_2 = Z::from(i64::MAX);
        let cmp_3 = Z::from(i64::MIN);
        let cmp_4 = Z::ZERO;
        let cmp_5 = Z::from(17);

        assert_eq!(cmp_1, det_1);
        assert_eq!(cmp_2, det_2);
        assert_eq!(cmp_3, det_3);
        assert_eq!(cmp_4, det_4);
        assert_eq!(cmp_5, det_5);
    }

    /// Ensure that an error is returned if the entered matrix is not square
    #[test]
    fn not_square_error() {
        let mat_1 = MatZ::from_str("[[5],[2]]").unwrap();
        let mat_2 = MatZ::from_str("[[2, 0],[0, 1],[8, -6]]").unwrap();

        assert!(mat_1.det().is_err());
        assert!(mat_2.det().is_err());
    }
}
