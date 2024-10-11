// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatZ`] matrix from other types.
//!
//! The explicit functions contain the documentation.

use super::MatZ;
use crate::{
    error::MathError,
    integer::Z,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::{
        dimensions::find_matrix_dimensions,
        index::evaluate_indices,
        parse::{matrix_from_utf8_fill_bytes, parse_matrix_string},
    },
};
use std::{fmt::Display, str::FromStr};

impl FromStr for MatZ {
    type Err = MathError;

    /// Creates a [`MatZ`] matrix with entries in [`Z`] from a [`String`].
    ///
    /// Parameters:
    /// - `string`: the matrix of form: `"[[1, 2, 3],[4, 5, 6]]"`
    ///     for a 2x3 matrix with entries 1, 2, 3 in the first row and 4, 5, 6
    ///     in the second row.
    ///
    /// Returns a [`MatZ`] or an error if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too large (must fit into [`i64`]),
    /// the number of entries in rows is unequal or if an entry is not formatted correctly.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1, 2, 3],[3, 4, 5]]");
    /// let matrix = MatZ::from_str(&string).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
    ///     - if the matrix is not formatted in a suitable way,
    ///     - if the number of rows or columns is too large (must fit into i64),
    ///     - if the number of entries in rows is unequal, or
    ///     - if an entry is not formatted correctly.
    ///         For further information see [`Z::from_str`].
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    ///     For further information see [`MatZ::new`].
    fn from_str(string: &str) -> Result<Self, MathError> {
        let string_matrix = parse_matrix_string(string)?;
        let (num_rows, num_cols) = find_matrix_dimensions(&string_matrix)?;
        let mut matrix = MatZ::new(num_rows, num_cols);

        // fill entries of matrix according to entries in string_matrix
        for (row_num, row) in string_matrix.iter().enumerate() {
            for (col_num, entry) in row.iter().enumerate() {
                let z_entry = Z::from_str(entry)?;
                matrix.set_entry(row_num, col_num, z_entry)?;
            }
        }
        Ok(matrix)
    }
}

impl From<&MatZ> for MatZ {
    /// Alias for [`MatZ::clone`].
    fn from(value: &MatZ) -> Self {
        value.clone()
    }
}

impl MatZ {
    /// Create a [`MatZ`] from a [`String`], i.e. its UTF8-Encoding.
    /// This function can only construct positive or zero integers, but not negative ones.
    /// If the number of bytes and number of entries does not line up, we pad the message
    /// with `'0'`s.
    /// The inverse of this function is [`Z::to_utf8`].
    ///
    /// Parameters:
    /// - `message`: specifies the message that is transformed via its UTF8-Encoding
    ///   to a new [`MatZ`] instance.
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    ///
    /// Returns a [`MatZ`] with corresponding entries to the message's UTF8-Encoding.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// let message = "hello!";
    ///  
    /// let value = MatZ::from_utf8(&message, 2, 1);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    ///     For further information see [`MatZ::new`].
    pub fn from_utf8(
        message: &str,
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
    ) -> Self {
        let (num_rows_i64, num_cols_i64) = evaluate_indices(num_rows, num_cols).unwrap();
        let mut mat = MatZ::new(num_rows_i64, num_cols_i64);
        let num_columns = mat.get_num_columns() as usize;
        let nr_entries = mat.get_num_rows() as usize * num_columns;

        // This error can't be triggered as no modulus is provided.
        let (byte_vector, nr_bytes_per_entry) =
            matrix_from_utf8_fill_bytes(message, nr_entries, None).unwrap();

        // Fill rows going from left to right, entry by entry
        for row in 0..mat.get_num_rows() as usize {
            let offset_row = row * num_columns * nr_bytes_per_entry;
            for col in 0..num_columns {
                let entry_value = Z::from_bytes(
                    &byte_vector[offset_row + nr_bytes_per_entry * col
                        ..offset_row + nr_bytes_per_entry * (col + 1)],
                );
                mat.set_entry(row, col, entry_value).unwrap();
            }
        }

        mat
    }
}

#[cfg(test)]
mod test_from_str {
    use crate::{
        integer::{MatZ, Z},
        traits::GetEntry,
    };
    use std::str::FromStr;

    /// Ensure that initialization works.
    #[test]
    fn init_works() {
        let matrix_str = "[[1, 2, 3],[3, 4, 5]]";

        assert_eq!(
            Z::ONE,
            MatZ::from_str(matrix_str).unwrap().get_entry(0, 0).unwrap()
        );
    }

    /// Ensure that initialization with positive numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_large_numbers() {
        let matrix_string = format!("[[{}, 2, 3],[3, 4, 5]]", u64::MAX);

        assert_eq!(
            Z::from(u64::MAX),
            MatZ::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that initialization with negative numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_small_numbers() {
        let matrix_string = format!("[[-{}, 2, 3],[3, 4, 5]]", u64::MAX);

        let entry = format!("-{}", u64::MAX);

        assert_eq!(
            Z::from_str(&entry).unwrap(),
            MatZ::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that entries can have leading and trailing whitespaces.
    #[test]
    fn whitespaces_in_entries_works() {
        let matrix_str = "[[  1, 2 ,  3  ],[3 , 4, 5 ]]";

        assert_eq!(
            Z::ONE,
            MatZ::from_str(matrix_str).unwrap().get_entry(0, 0).unwrap()
        );
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_str_1 = "[1, 2, 3],[3, 4, 5]]";
        let matrix_str_2 = "[[1, 2, 3][3, 4, 5]]";
        let matrix_str_3 = "[[1, 2, 3], 3, 4, 5]";
        let matrix_str_4 = "[1, 2, 3, 4, 5]";
        let matrix_str_5 = "[ [1, 2, 3],[3, 4, 5]]";
        let matrix_str_6 = "[[1, 2, 3],[3, 4, 5]8]";
        let matrix_str_7 = "";
        let matrix_str_8 = "[]";
        let matrix_str_9 = "[[]]";

        assert!(MatZ::from_str(matrix_str_1).is_err());
        assert!(MatZ::from_str(matrix_str_2).is_err());
        assert!(MatZ::from_str(matrix_str_3).is_err());
        assert!(MatZ::from_str(matrix_str_4).is_err());
        assert!(MatZ::from_str(matrix_str_5).is_err());
        assert!(MatZ::from_str(matrix_str_6).is_err());
        assert!(MatZ::from_str(matrix_str_7).is_err());
        assert!(MatZ::from_str(matrix_str_8).is_err());
        assert!(MatZ::from_str(matrix_str_9).is_err());
    }
}

#[cfg(test)]
/// Test the implementation of [`MatZ::from_utf8`] briefly.
/// This module omits tests that were already provided for [`Z::from_bytes`]
/// and [`crate::utils::parse::matrix_from_utf8_fill_bytes`].
mod test_from_utf8 {
    use super::{MatZ, Z};
    use crate::traits::GetEntry;
    use std::str::FromStr;

    /// Ensures that a wide range of (special) characters are correctly transformed correctly.
    #[test]
    fn characters() {
        let message = "flag{text#1234567890! a_zA-Z$€?/:;,.<>+*}";

        let matrix = MatZ::from_utf8(message, 1, 1);
        let value = matrix.get_entry(0, 0).unwrap();

        // easy trick s.t. we don't have to initialize a huge [`Z`] value
        // while this test should still fail if the value changes
        let value_zq = value.modulo(65537);

        assert_eq!(Z::from(58285), value_zq);
    }

    /// Ensure that the empty string results in a zero value.
    #[test]
    fn empty_string() {
        let message = "";

        let matrix = MatZ::from_utf8(message, 1, 1);
        let value = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::ZERO, value);
    }

    /// Ensures correct conversion of bytes and their order.
    #[test]
    fn conversion_and_order() {
        let message = "{10_chars}";
        let cmp_matrix = MatZ::from_str("[[12667, 24368],[26723, 29281],[32115, 12336]]").unwrap();

        let matrix = MatZ::from_utf8(message, 3, 2);

        assert_eq!(cmp_matrix, matrix);
    }
}
