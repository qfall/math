// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implements methods to pre-process indices under certain conditions.

use crate::error::MathError;
use crate::traits::{GetNumColumns, GetNumRows};
use std::fmt::Display;

/// Converts index into an [`i64`] that must be greater than `0` and must fit into
/// an [`i64`].
///
/// Parameters:
/// - `index`: the index that has to be converted into an [`i64`].
///
/// Returns an [`i64`] representation of the index or an error, if the
/// index does not fulfill all conditions.
///
/// # Examples
/// ```
/// use qfall_math::utils::index::evaluate_index;
///
/// let index = evaluate_index(u32::MAX).unwrap();
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
///     either the index is negative or it does not fit into an [`i64`].
pub fn evaluate_index(index: impl TryInto<i64> + Display) -> Result<i64, MathError> {
    // the index must fit into an [`i64`]

    let index: i64 = if cfg!(debug_assertions) {
        // Only executed in debug mode
        let index_str = index.to_string();
        match index.try_into() {
            Ok(index) => index,
            _ => {
                return Err(MathError::OutOfBounds(
                    "fit into a i64".to_owned(),
                    index_str,
                ))
            }
        }
    } else {
        // Only executed when NOT in debug mode
        match index.try_into() {
            Ok(index) => index,
            _ => {
                return Err(MathError::OutOfBounds(
                    "fit into a i64".to_owned(),
                    "rerun in debug mode to obtain the incorrect index".to_owned(),
                ))
            }
        }
    };

    // negative indices can not be addressed
    if index < 0 {
        return Err(MathError::OutOfBounds(
            "be at least zero".to_owned(),
            index.to_string(),
        ));
    }
    Ok(index)
}

/// Converts index1 and index2 into [`i64`] that must be greater than `0` and must fit into
/// an [`i64`].
///
/// Parameters:
/// - `index1`: the first index that has to be converted into an [`i64`].
/// - `index2`: the second index that has to be converted into an [`i64`].
///
/// Returns an [`i64`] representation of index1 and index2 or an error, if the
/// indices do not fulfill all conditions.
///
/// # Examples
/// ```
/// use qfall_math::utils::index::evaluate_indices;
///
/// let (index1, index2) = evaluate_indices(u32::MAX, 3).unwrap();
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
///     either the index is negative or it does not fit into an [`i64`].
pub fn evaluate_indices(
    index1: impl TryInto<i64> + Display,
    index2: impl TryInto<i64> + Display,
) -> Result<(i64, i64), MathError> {
    let index1_i64 = evaluate_index(index1)?;
    let index2_i64 = evaluate_index(index2)?;

    Ok((index1_i64, index2_i64))
}

/// Evaluates whether the provided row and column are referencing an entry in a matrix.
///
/// Parameters:
/// - `matrix`: specifies the matrix in which the entry is located
/// - `row`: specifies the row in which the entry is located
/// - `column`: specifies the column in which the entry is located
///
/// Returns the indices as a pair of [`i64`] if they reference an entry and return
/// an error otherwise.
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
///     if the number of rows or columns is greater than the matrix or negative.
pub fn evaluate_indices_for_matrix<S: GetNumRows + GetNumColumns>(
    matrix: &S,
    row: impl TryInto<i64> + Display,
    column: impl TryInto<i64> + Display,
) -> Result<(i64, i64), MathError> {
    let mut row_i64: i64 = match row.try_into() {
        Ok(index) => index,
        _ => {
            return Err(MathError::OutOfBounds(
                "fit into a i64".to_owned(),
                "unknown for performance reasons".to_owned(),
            ))
        }
    };

    let mut column_i64: i64 = match column.try_into() {
        Ok(index) => index,
        _ => {
            return Err(MathError::OutOfBounds(
                "fit into a i64".to_owned(),
                "unknown for performance reasons".to_owned(),
            ))
        }
    };

    if row_i64 < 0 {
        row_i64 += matrix.get_num_rows();
        if row_i64 < 0 {
            return Err(MathError::OutOfBounds(
                format!(
                    "be larger or equal to ({}, {})",
                    -matrix.get_num_rows(),
                    -matrix.get_num_columns()
                ),
                format!("({}, {})", row_i64 + matrix.get_num_rows(), column_i64),
            ));
        }
    }
    if column_i64 < 0 {
        column_i64 += matrix.get_num_columns();
        if column_i64 < 0 {
            return Err(MathError::OutOfBounds(
                format!(
                    "be larger or equal to ({}, {})",
                    -matrix.get_num_rows(),
                    -matrix.get_num_columns()
                ),
                format!("({}, {})", row_i64, column_i64 + matrix.get_num_columns()),
            ));
        }
    }

    if matrix.get_num_rows() <= row_i64 || matrix.get_num_columns() <= column_i64 {
        return Err(MathError::OutOfBounds(
            format!(
                "be smaller than ({}, {})",
                matrix.get_num_rows(),
                matrix.get_num_columns()
            ),
            format!("({row_i64}, {column_i64})"),
        ));
    }
    Ok((row_i64, column_i64))
}

#[cfg(test)]
mod test_eval_index {
    use super::evaluate_index;
    use crate::integer::Z;

    /// Tests that negative indices are not accepted
    #[test]
    fn is_err_negative() {
        assert!(evaluate_index(i32::MIN).is_err());
    }

    /// Tests that the function can be called with several types
    #[test]
    fn is_ok_several_types() {
        assert!(evaluate_index(i8::MAX).is_ok());
        assert!(evaluate_index(i16::MAX).is_ok());
        assert!(evaluate_index(i32::MAX).is_ok());
        assert!(evaluate_index(i64::MAX).is_ok());
        assert!(evaluate_index(u8::MAX).is_ok());
        assert!(evaluate_index(u16::MAX).is_ok());
        assert!(evaluate_index(u32::MAX).is_ok());

        assert!(evaluate_index(Z::from(10)).is_ok());
    }

    /// Ensure that integers which can not be converted to an [`i64`]
    /// are not accepted
    #[test]
    fn does_not_fit() {
        assert!(evaluate_index(u64::MAX).is_err());
    }
}

#[cfg(test)]
mod test_eval_indices {
    use super::evaluate_indices_for_matrix;
    use crate::integer::MatZ;

    /// Test that negative addressing works.
    #[test]
    fn small_negative() {
        let matrix = MatZ::new(10, 10);

        let (a, b) = evaluate_indices_for_matrix(&matrix, -1, -10)
            .expect("No error with small negative index.");

        assert_eq!(a, 9);
        assert_eq!(b, 0);
    }

    /// Assert that an error is returned if either the row or column
    /// are just out of bounds.
    #[test]
    fn negative_out_of_bounds() {
        let matrix = MatZ::new(1, 1);

        assert!(evaluate_indices_for_matrix(&matrix, 0, -2).is_err());
        assert!(evaluate_indices_for_matrix(&matrix, -2, 0).is_err());
        assert!(evaluate_indices_for_matrix(&matrix, -2, -2).is_err());
    }

    /// Tests that the function can be called with several types.
    #[test]
    fn is_ok_several_types() {
        let matrix = MatZ::new(i16::MAX, u8::MAX);

        assert!(evaluate_indices_for_matrix(&matrix, 3i8, 0).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 3i16, 0).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 3i32, 0).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 3i64, 0).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 3u8, 0).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 3u16, 0).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 3u32, 0).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 3u64, 0).is_ok());

        assert!(evaluate_indices_for_matrix(&matrix, 0, 3i8).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 0, 3i16).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 0, 3i32).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 0, 3i64).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 0, 3u8).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 0, 3u16).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 0, 3u32).is_ok());
        assert!(evaluate_indices_for_matrix(&matrix, 0, 3u64).is_ok());
    }

    /// Ensure that integers which can not be converted to an [`i64`]
    /// are not accepted
    #[test]
    fn does_not_fit() {
        let matrix = MatZ::new(3, 3);

        assert!(evaluate_indices_for_matrix(&matrix, u64::MAX, 0).is_err());
        assert!(evaluate_indices_for_matrix(&matrix, 0, u64::MAX).is_err());
    }
}
