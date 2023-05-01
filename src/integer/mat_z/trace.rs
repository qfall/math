// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `trace` function.

use flint_sys::fmpz_mat::fmpz_mat_trace;

use super::MatZ;
use crate::{
    error::MathError,
    integer::Z,
    traits::{GetNumColumns, GetNumRows},
};

impl MatZ {
    /// Returns the trace of a matrix and an error,
    /// if the matrix is not square.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZ::from_str("[[1,2],[3,4]]").unwrap();
    /// let trace = matrix.trace().unwrap();
    /// ```
    pub fn trace(&self) -> Result<Z, MathError> {
        // check if matrix is square
        if self.get_num_rows() != self.get_num_columns() {
            return Err(MathError::NotSquare(self.to_string()));
        }

        let mut out = Z::default();
        unsafe {
            fmpz_mat_trace(&mut out.value, &self.matrix);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_trace {

    use crate::integer::{MatZ, Z};
    use std::str::FromStr;

    /// Test whether `trace` correctly calculates the trace of a matrix
    #[test]
    fn trace_works() {
        let mat1 = MatZ::from_str("[[5,2,0],[2,1,0],[0,0,1]]").unwrap();
        let mat2 = MatZ::from_str("[[-1,0],[0,1]]").unwrap();

        let trace1 = mat1.trace().unwrap();
        let trace2 = mat2.trace().unwrap();

        assert_eq!(Z::from(7), trace1);
        assert_eq!(Z::from(0), trace2);
    }

    /// Test whether `trace` works for big values
    #[test]
    fn trace_big_values() {
        let mat1 = MatZ::from_str(&format!("[[{},5],[1,{}]]", i64::MAX, i64::MAX)).unwrap();
        let mat2 = MatZ::from_str(&format!("[[{}]]", i64::MIN)).unwrap();
        let mat3 = MatZ::from_str(&format!("[[{},5],[1,{}]]", i64::MIN, i64::MAX)).unwrap();

        let trace1 = mat1.trace().unwrap();
        let trace2 = mat2.trace().unwrap();
        let trace3 = mat3.trace().unwrap();

        assert_eq!(Z::from(2 * i64::MAX as u64), trace1);
        assert_eq!(Z::from(i64::MIN), trace2);
        assert_eq!(Z::from(-1), trace3);
    }

    /// Ensure that a matrix that is not square yields an error.
    #[test]
    fn trace_error_not_squared() {
        let mat1 = MatZ::from_str("[[1,0,1],[0,1,1]]").unwrap();
        let mat2 = MatZ::from_str("[[1,0],[0,1],[1,0]]").unwrap();

        assert!(mat1.trace().is_err());
        assert!(mat2.trace().is_err());
    }
}
