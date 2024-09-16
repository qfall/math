// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `trace` function.

use flint_sys::fmpq_mat::fmpq_mat_trace;

use super::MatQ;
use crate::{
    error::MathError,
    rational::Q,
    traits::{GetNumColumns, GetNumRows},
};

impl MatQ {
    /// Returns the trace of a matrix and an error,
    /// if the matrix is not square.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[1/2, 2],[3/7, 4]]").unwrap();
    /// let trace = matrix.trace().unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`NoSquareMatrix`](MathError::NoSquareMatrix)
    ///     if the matrix is not a square matrix
    pub fn trace(&self) -> Result<Q, MathError> {
        // check if matrix is square
        if self.get_num_rows() != self.get_num_columns() {
            return Err(MathError::NoSquareMatrix(self.to_string()));
        }

        let mut out = Q::default();
        unsafe {
            fmpq_mat_trace(&mut out.value, &self.matrix);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_trace {
    use crate::rational::{MatQ, Q};
    use std::str::FromStr;

    /// Test whether `trace` correctly calculates the trace of a matrix
    #[test]
    fn trace_works() {
        let mat_1 = MatQ::from_str("[[5/2, 2, 0],[2, 1/2, 0],[0, 0, 1/3]]").unwrap();
        let mat_2 = MatQ::from_str("[[-1, 0],[0, 1]]").unwrap();

        let trace_1 = mat_1.trace().unwrap();
        let trace_2 = mat_2.trace().unwrap();

        assert_eq!(Q::from((10, 3)), trace_1);
        assert_eq!(Q::ZERO, trace_2);
    }

    /// Test whether `trace` works for large values
    #[test]
    fn trace_large_values() {
        let mat_1 = MatQ::from_str(&format!("[[{}, 5],[1, {}]]", i64::MAX, i64::MAX)).unwrap();
        let mat_2 = MatQ::from_str(&format!("[[{}]]", i64::MIN)).unwrap();
        let mat_3 = MatQ::from_str(&format!("[[{}, 5],[1, 1/{}]]", i64::MIN, i64::MAX)).unwrap();

        let trace_1 = mat_1.trace().unwrap();
        let trace_2 = mat_2.trace().unwrap();
        let trace_3 = mat_3.trace().unwrap();

        assert_eq!(Q::from(2 * i64::MAX as u64), trace_1);
        assert_eq!(Q::from(i64::MIN), trace_2);
        assert_eq!(Q::from(i64::MIN) + Q::from((1, i64::MAX)), trace_3);
    }

    /// Ensure that a matrix that is not square yields an error.
    #[test]
    fn trace_error_not_squared() {
        let mat_1 = MatQ::from_str("[[1/2, 0, 1],[0, 1/9, 1]]").unwrap();
        let mat_2 = MatQ::from_str("[[2/8, 0],[0, 1],[1/7, 0]]").unwrap();

        assert!(mat_1.trace().is_err());
        assert!(mat_2.trace().is_err());
    }
}
