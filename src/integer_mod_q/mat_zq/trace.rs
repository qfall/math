// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `trace` function.

use flint_sys::fmpz_mod_mat::fmpz_mod_mat_trace;

use super::MatZq;
use crate::{
    error::MathError,
    integer_mod_q::Zq,
    traits::{GetNumColumns, GetNumRows},
};

impl MatZq {
    /// Returns the trace of a matrix and an error,
    /// if the matrix is not square.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1,2],[3,4]] mod 5").unwrap();
    /// let trace = matrix.trace().unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// Returns a [`MathError`] of type
    /// [`NoSquareMatrix`](MathError::NoSquareMatrix)
    /// if the matrix is not a square matrix
    pub fn trace(&self) -> Result<Zq, MathError> {
        // check if matrix is square
        if self.get_num_rows() != self.get_num_columns() {
            return Err(MathError::NoSquareMatrix(self.to_string()));
        }

        let mut out = Zq::try_from_int_int(0, self.get_mod()).unwrap();
        unsafe {
            fmpz_mod_mat_trace(&mut out.value.value, &self.matrix);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_trace {

    use crate::integer_mod_q::{MatZq, Zq};
    use std::str::FromStr;

    /// Test whether `trace` correctly calculates the trace of a matrix
    #[test]
    fn trace_works() {
        let mat1 = MatZq::from_str("[[5,2,0],[2,8,0],[0,0,4]] mod 10").unwrap();
        let mat2 = MatZq::from_str("[[-1,0],[0,1]] mod 2").unwrap();

        let trace1 = mat1.trace().unwrap();
        let trace2 = mat2.trace().unwrap();

        assert_eq!(Zq::try_from_int_int(7, 10).unwrap(), trace1);
        assert_eq!(Zq::try_from_int_int(0, 2).unwrap(), trace2);
    }

    /// Test whether `trace` works for big values
    #[test]
    fn trace_big_values() {
        let mat1 = MatZq::from_str(&format!(
            "[[{},5],[1,{}]] mod {}",
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let mat2 = MatZq::from_str(&format!("[[{}]] mod {}", i64::MIN, u64::MAX)).unwrap();
        let mat3 = MatZq::from_str(&format!(
            "[[{},5],[1,{}]] mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();

        let trace1 = mat1.trace().unwrap();
        let trace2 = mat2.trace().unwrap();
        let trace3 = mat3.trace().unwrap();

        assert_eq!(
            Zq::try_from_int_int(2 * i64::MAX as u64, u64::MAX).unwrap(),
            trace1
        );
        assert_eq!(Zq::try_from_int_int(i64::MIN, u64::MAX).unwrap(), trace2);
        assert_eq!(Zq::try_from_int_int(-1, u64::MAX).unwrap(), trace3);
    }

    /// Ensure that a matrix that is not square yields an error.
    #[test]
    fn trace_error_not_squared() {
        let mat1 = MatZq::from_str("[[1,0,1],[0,1,1]] mod 42").unwrap();
        let mat2 = MatZq::from_str("[[1,0],[0,1],[1,0]] mod 17").unwrap();

        assert!(mat1.trace().is_err());
        assert!(mat2.trace().is_err());
    }
}
