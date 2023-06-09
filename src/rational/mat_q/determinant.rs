// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `determinant` function.

use super::MatQ;
use crate::{
    error::MathError,
    rational::Q,
    traits::{GetNumColumns, GetNumRows},
};
use flint_sys::fmpq_mat::fmpq_mat_det;

impl MatQ {
    /// Returns the determinant of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[1/2,2],[3/7,4]]").unwrap();
    /// let matrix_invert = matrix.det().unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of rows and columns is not equal.
    pub fn det(&self) -> Result<Q, MathError> {
        if self.get_num_rows() != self.get_num_columns() {
            return Err(MathError::MismatchingMatrixDimension(
                "The matrix is not square".to_string(),
            ));
        }

        let mut det = Q::default();
        unsafe {
            fmpq_mat_det(&mut det.value, &self.matrix);
        }
        Ok(det)
    }
}

#[cfg(test)]
mod test_determinant {
    use crate::rational::{MatQ, Q};
    use std::str::FromStr;

    /// Test whether the determinant is correctly computed
    #[test]
    fn determinant_works() {
        let mat1 = MatQ::from_str("[[10,2],[2,1/2]]").unwrap();
        let mat2 = MatQ::from_str(&format!("[[{},0],[0,1]]", i64::MAX)).unwrap();
        let mat3 = MatQ::from_str(&format!("[[-1/{}]]", i64::MIN)).unwrap();
        let mat4 = MatQ::from_str("[[0,0],[0,1]]").unwrap();
        let mat5 = MatQ::from_str("[[6,0,1],[0,1,0],[1,2,3]]").unwrap();

        let det1 = mat1.det().unwrap();
        let det2 = mat2.det().unwrap();
        let det3 = mat3.det().unwrap();
        let det4 = mat4.det().unwrap();
        let det5 = mat5.det().unwrap();

        let cmp1 = Q::ONE;
        let cmp2 = Q::from(i64::MAX);
        let cmp3 = Q::try_from((&-1, &i64::MIN)).unwrap();
        let cmp4 = Q::ZERO;
        let cmp5 = Q::from(17);

        assert_eq!(cmp1, det1);
        assert_eq!(cmp2, det2);
        assert_eq!(cmp3, det3);
        assert_eq!(cmp4, det4);
        assert_eq!(cmp5, det5);
    }

    /// Ensure that an error is returned if the entered matrix is not square
    #[test]
    fn not_square_error() {
        let mat1 = MatQ::from_str("[[5/7],[2]]").unwrap();
        let mat2 = MatQ::from_str("[[2,0],[0,1/8],[8/4,-6]]").unwrap();

        assert!(mat1.det().is_err());
        assert!(mat2.det().is_err());
    }
}
