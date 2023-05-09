// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Initialize a [`MatQ`] with common defaults, e.g., zero and identity.

use super::MatQ;
use crate::{error::MathError, utils::index::evaluate_index};
use flint_sys::fmpq_mat::{fmpq_mat_init, fmpq_mat_one};
use std::{fmt::Display, mem::MaybeUninit};

impl MatQ {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns and
    /// zeros as entries.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    ///
    /// Returns a [`MatQ`] or an error, if the number of rows or columns is
    /// less or equal to `0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    ///
    /// let matrix = MatQ::new(5, 10).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the number of rows or columns is `0`.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is negative or it does not fit into an [`i64`].
    pub fn new(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
    ) -> Result<Self, MathError> {
        let num_rows_i64 = evaluate_index(num_rows)?;
        let num_cols_i64 = evaluate_index(num_cols)?;

        if num_rows_i64 == 0 || num_cols_i64 == 0 {
            return Err(MathError::InvalidMatrix(format!(
                "({},{})",
                num_rows_i64, num_cols_i64,
            )));
        }

        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpq_mat_init(matrix.as_mut_ptr(), num_rows_i64, num_cols_i64);

            // Construct MatQ from previously initialized fmpq_mat
            Ok(MatQ {
                matrix: matrix.assume_init(),
            })
        }
    }

    /// Generate a `num_rows` times `num_columns` matrix with `1` on the
    /// diagonal and `0` anywhere else.
    ///
    /// Parameters:
    /// - `rum_rows`: the number of rows of the identity matrix
    /// - `num_columns`: the number of columns of the identity matrix
    ///
    /// Returns a matrix with `1` across the diagonal and `0` anywhere else.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    ///
    /// let matrix = MatQ::identity(2, 3).unwrap();
    ///
    /// let identity = MatQ::identity(10, 10).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix) or
    /// [`OutOfBounds`](MathError::OutOfBounds) if the provided number of rows and columns
    /// are not suited to create a matrix. For further information see [`MatQ::new`].
    pub fn identity(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
    ) -> Result<Self, MathError> {
        let mut out = MatQ::new(num_rows, num_cols)?;
        unsafe { fmpq_mat_one(&mut out.matrix) };
        Ok(out)
    }
}

#[cfg(test)]
mod test_new {
    use crate::rational::MatQ;

    /// Ensure that initialization works.
    #[test]
    fn initialization() {
        assert!(MatQ::new(2, 2).is_ok());
    }

    /// Ensure that a new zero matrix fails with `0` as input.
    #[test]
    fn error_zero() {
        let matrix1 = MatQ::new(1, 0);
        let matrix2 = MatQ::new(0, 1);
        let matrix3 = MatQ::new(0, 0);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
        assert!(matrix3.is_err());
    }
    // TODO add test for `0` entries
}

#[cfg(test)]
mod test_set_one {
    use crate::{
        rational::{MatQ, Q},
        traits::GetEntry,
    };

    /// Tests if an identity matrix is set from a zero matrix.
    #[test]
    fn identity() {
        let matrix = MatQ::identity(10, 10).unwrap();

        for i in 0..10 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(Q::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Q::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }
    }

    /// Tests if function works for a non-square matrix
    #[test]
    fn non_square_works() {
        let matrix = MatQ::identity(10, 7).unwrap();

        for i in 0..10 {
            for j in 0..7 {
                if i != j {
                    assert_eq!(Q::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Q::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }

        let matrix = MatQ::identity(7, 10).unwrap();

        for i in 0..7 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(Q::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Q::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }
    }
}
