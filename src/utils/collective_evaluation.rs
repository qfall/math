// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains functions to collectively evaluate parameters
//! instead of copying the same lines of code for error handling in each function.

use crate::error::MathError;

/// Evaluates whether `row0` and `row1` is smaller than `self_num_rows` and `other_num_rows`.
/// Additionally, whether `self_num_cols` equals `other_num_cols`.
///
/// Parameters:
/// - `callee`: specifies the name of the calling function
/// - `row0`: specifies a value that should be smaller than `self_num_rows`
/// - `row1`: specifies a value that should be smaller than `other_num_rows`
/// - `self_num_rows`: is evaluated against `row0`
/// - `other_num_rows`: is evaluated against `row1`
/// - `self_num_cols`: is used to check whether it equals `other_num_cols`
/// - `other_num_cols`: is evaluated against `self_num_cols`
///
/// Returns an empty `Ok` if `row0 < self_num_rows`, `row1 < other_num_rows`, and `self_num_cols == other_num_cols`.
/// Otherwise, a [`MathError`] is returned.
///
/// # Example
/// ```compile_fail
/// use qfall_math::utils::collective_evaluation::evaluate_matrix_set_row;
/// use qfall_math::integer_mod_q::MatZq;
/// use std::str::FromStr;
/// let mat1 = MatZq::from_str("[[1,2,3],[4,5,6]]").unwrap();
/// let mat2 = mat1.clone();
///
/// let _ = evaluate_matrix_set_row("set_row", 0, 1, row0, row1, mat1.get_num_rows(), mat2.get_num_rows(), mat1.get_num_columns(), mat2.get_num_columns());
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
/// if the number of rows is greater than the matrix dimensions or negative.
/// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
/// if the number of columns of `self` and `other` differ.
pub(crate) fn evaluate_matrix_set_row(
    callee: &str,
    row0: i64,
    row1: i64,
    self_num_rows: i64,
    other_num_rows: i64,
    self_num_cols: i64,
    other_num_cols: i64,
) -> Result<(), MathError> {
    if row0 >= self_num_rows {
        return Err(MathError::OutOfBounds(
            format!("smaller than {}", self_num_rows),
            row0.to_string(),
        ));
    }
    if row1 >= other_num_rows {
        return Err(MathError::OutOfBounds(
            format!("smaller than {}", other_num_rows),
            row1.to_string(),
        ));
    }
    if self_num_cols != other_num_cols {
        return Err(MathError::MismatchingMatrixDimension(format!(
            "as {} was called on two matrices with different number of columns {} and {}",
            callee, self_num_cols, other_num_cols
        )));
    }
    Ok(())
}
