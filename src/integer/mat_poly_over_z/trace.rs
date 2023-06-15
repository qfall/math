// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `trace` function.

use flint_sys::fmpz_poly_mat::fmpz_poly_mat_trace;

use super::MatPolyOverZ;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    traits::{GetNumColumns, GetNumRows},
};

impl MatPolyOverZ {
    /// Returns the trace of a matrix and an error,
    /// if the matrix is not square.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  42,2  1 2],[1  4, 0]]").unwrap();
    /// let trace = matrix.trace().unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// Returns a [`MathError`] of type
    /// [`NoSquareMatrix`](MathError::NoSquareMatrix)
    /// if the matrix is not a square matrix
    pub fn trace(&self) -> Result<PolyOverZ, MathError> {
        // check if matrix is square
        if self.get_num_rows() != self.get_num_columns() {
            return Err(MathError::NoSquareMatrix(self.to_string()));
        }

        let mut out = PolyOverZ::default();
        unsafe {
            fmpz_poly_mat_trace(&mut out.poly, &self.matrix);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_trace {
    use crate::integer::{MatPolyOverZ, PolyOverZ};
    use std::str::FromStr;

    /// Test whether `trace` correctly calculates the trace of a matrix
    #[test]
    fn trace_works() {
        let mat1 =
            MatPolyOverZ::from_str("[[2  4 5,1  2,0],[1  2,1  1,0],[0,3  1 2 3,1  1]]").unwrap();
        let mat2 = MatPolyOverZ::from_str("[[2  -1 -1,0],[0,2  1 1]]").unwrap();

        let trace1 = mat1.trace().unwrap();
        let trace2 = mat2.trace().unwrap();

        assert_eq!(PolyOverZ::from_str("2  6 5").unwrap(), trace1);
        assert_eq!(PolyOverZ::default(), trace2);
    }

    /// Test whether `trace` works for big values
    #[test]
    fn trace_big_values() {
        let mat1 = MatPolyOverZ::from_str(&format!(
            "[[2  -1 {},1  5],[3  1 2 3,1  {}]]",
            i64::MAX,
            i64::MAX
        ))
        .unwrap();
        let mat2 = MatPolyOverZ::from_str(&format!("[[1  {}]]", i64::MIN)).unwrap();
        let mat3 = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  5],[3  1 2 3,1  {}]]",
            i64::MIN,
            i64::MAX
        ))
        .unwrap();

        let trace1 = mat1.trace().unwrap();
        let trace2 = mat2.trace().unwrap();
        let trace3 = mat3.trace().unwrap();

        assert_eq!(
            PolyOverZ::from_str(&format!("2  {} {}", i64::MAX - 1, i64::MAX)).unwrap(),
            trace1
        );
        assert_eq!(
            PolyOverZ::from_str(&format!("1  {}", i64::MIN)).unwrap(),
            trace2
        );
        assert_eq!(PolyOverZ::from_str(&format!("1  {}", -1)).unwrap(), trace3);
    }

    /// Ensure that a matrix that is not square yields an error.
    #[test]
    fn trace_error_not_squared() {
        let mat1 = MatPolyOverZ::from_str("[[1  1,0,1  1],[0,1  2,1  3]]").unwrap();
        let mat2 = MatPolyOverZ::from_str("[[1  42,0],[0,3  17 9 8],[1  3,0]]").unwrap();

        assert!(mat1.trace().is_err());
        assert!(mat2.trace().is_err());
    }
}
