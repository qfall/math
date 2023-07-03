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

/// Evaluates whether the provided indices are within a provided upper bound, e.g. refer to a valid entry
/// in a matrix, and check if the corresponding vectors in the matrix are of equal length.
/// This function checks whether:
/// - The `index_vector_0` and `index_vector_1` are both referencing a row/column within the matrix,
/// i.e. it is smaller than the number of rows/columns of the respective matrix entered by the upper bound.
/// - The referenced vectors are of equal length because replacing the vector is not properly defined otherwise
///
/// Parameters:
/// - `callee`: specifies the name of the calling function
/// - `index_vector_0`: specifies a value that should be smaller than `number_of_vectors_0`
/// - `index_vector_1`: specifies a value that should be smaller than `number_of_vectors_1`
/// - `number_of_vectors_0`: the upper bound for `index_vector_0`
/// - `number_of_vectors_1`: the upper bound for `index_vector_1`
/// - `length_vector_0`: is used to check whether it equals `length_vector_1`
/// - `length_vector_1`: is evaluated against `length_vector_0`
///
/// Returns an empty `Ok` if `row0 < self_num_rows`, `row1 < other_num_rows`, and
/// `self_num_cols == other_num_cols`. Otherwise, a [`MathError`] is returned.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::utils::collective_evaluation::evaluate_vec_dimensions_set_row_or_col;
/// use qfall_math::integer_mod_q::MatZq;
/// use std::str::FromStr;
/// let mat1 = MatZq::from_str("[[1,2,3],[4,5,6]]").unwrap();
/// let mat2 = mat1.clone();
///
/// let _ = evaluate_vec_dimensions_set_row_or_col(
///     "set_row",
///     0,
///     1,
///     mat1.get_num_rows(),
///     mat2.get_num_rows(),
///     mat1.get_num_columns(),
///     mat2.get_num_columns()
/// );
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
/// if the number of rows is greater than the matrix dimensions or negative.
/// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
/// if the number of columns of `self` and `other` differ.
pub(crate) fn evaluate_vec_dimensions_set_row_or_col(
    callee: &str,
    index_vector_0: i64,
    index_vector_1: i64,
    number_of_vectors_0: i64,
    number_of_vectors_1: i64,
    length_vector_0: i64,
    length_vector_1: i64,
) -> Result<(), MathError> {
    if index_vector_0 >= number_of_vectors_0 {
        return Err(MathError::OutOfBounds(
            format!("smaller than {number_of_vectors_0}"),
            index_vector_0.to_string(),
        ));
    }
    if index_vector_1 >= number_of_vectors_1 {
        return Err(MathError::OutOfBounds(
            format!("smaller than {number_of_vectors_1}"),
            index_vector_1.to_string(),
        ));
    }
    if length_vector_0 != length_vector_1 {
        return Err(MathError::MismatchingMatrixDimension(format!(
            "as {callee} was called on two matrices with different number of columns {length_vector_0} and {length_vector_1}",
        )));
    }
    Ok(())
}
