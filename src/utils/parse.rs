// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implements methods to parse a [`String`] e.g. matrix strings.

use crate::{
    error::{MathError, StringConversionError},
    traits::{MatrixDimensions, MatrixGetEntry},
};
use regex::Regex;
use std::fmt::Display;
use string_builder::Builder;

/// Takes the string of a matrix as input and parses it for easy use.
///
/// The input should look like `[[1, 2, 3],[4, 5, 6]]` to get a matrix with
/// strings as entries.
/// Entries of the matrix can contain all symbols but `[`, `]` and `,`.
///
/// Parameters:
/// - `string`: a matrix as a string
///
/// Returns the matrix in form of a two dimensional vector with the entries
/// stored as strings or an error if the matrix is not formatted correctly.
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
///   if the matrix is not formatted in a suitable way.
pub(crate) fn parse_matrix_string(string: &str) -> Result<Vec<Vec<String>>, MathError> {
    // check if the matrix format is correct
    let entry_str = r"([^\[\],]+)";
    let row_str = format!(r"\[({entry_str},)*({entry_str})\]");
    let matrix_str = format!(r"^\[({row_str},\s?)*({row_str})\]$");
    let regex = Regex::new(&matrix_str).expect("The regular expression could not be processed.");

    // explanation of this regex:
    // it checks whether the string start with a '[' and ends with a ']'
    // we differ between the first/several and the last row (as there is no comma after the last row)
    // each row needs to start with a '[' and end with a ']'
    // we differ between the first/several and the last entry in each row (as there is no comma after the last entry)
    // each entry can contain any symbol but `[`, `]` and `,`. It needs to have at least one symbol.
    if !regex.is_match(string) {
        Err(StringConversionError::InvalidMatrix(
            "The matrix is not formatted in a suitable way.".to_owned(),
        ))?;
    }

    // delete `[[` in front and `]]` in the end and split the matrix into rows
    let string = string.replace("], [", "],[");
    let rows = string[2..string.len() - 2].split("],[");

    let mut matrix: Vec<Vec<String>> = Vec::new();
    for row in rows {
        //split the row into entries of the matrix
        let entries = row.split(',');

        let mut row_vec: Vec<String> = Vec::new();
        for entry in entries {
            // delete leading and trailing whitespaces from the entry and
            // adds it to the row vector
            row_vec.push(entry.trim().to_owned());
        }
        // adds the row vector to the matrix
        matrix.push(row_vec);
    }

    Ok(matrix)
}

/// Takes a matrix as input and converts it to a [`String`].
///
/// Parameters:
/// - `matrix`: a matrix e.g. [`MatZ`](crate::integer::MatZ), [`MatQ`](crate::rational::MatQ).
///
/// Returns the Matrix in form of a [`String`]. For matrix `[[1, 2, 3],[4, 5, 6]]`
/// the String looks like this `[[1, 2, 3],[4, 5, 6]]`.
pub(crate) fn matrix_to_string<
    S: Display + Clone,
    T: MatrixGetEntry<S> + MatrixDimensions + MatrixDimensions,
>(
    matrix: &T,
) -> String {
    let mut builder = Builder::default();

    builder.append('[');

    for row in 0..matrix.get_num_rows() {
        builder.append('[');

        for col in 0..matrix.get_num_columns() {
            builder.append(format!(
                "{}",
                matrix
                    .get_entry(row, col)
                    .expect("Rows or columns are not matching the dimensions of the matrix.")
            ));
            if col < matrix.get_num_columns() - 1 {
                builder.append(", ");
            }
        }

        if row < matrix.get_num_rows() - 1 {
            builder.append("],");
        } else {
            builder.append(']');
        }
    }
    builder.append(']');

    builder
        .string()
        .expect("Matrix string contains invalid bytes.")
}

/// Adds `0`-padding to the UTF8-Encoding of the `message` until every entry of
/// the matrix has the same number of bytes assigned to it.
///
/// Parameters:
/// - `message`: a [`String`] whose UTF8-Encoding should be encoded in a matrix.
/// - `nr_entries`: the number of entries in the matrix, i.e. `nr_rows * nr_columns`.
///
/// Returns a padded byte [`Vec<u8>`] with the same number of bytes assigned to
/// every entry of the matrix and the number of bytes per entry as [`usize`].
///
/// # Panics ...
/// - if `nr_entries` is smaller than or equal to `0`.
pub(crate) fn matrix_from_utf8_fill_bytes(message: &str, nr_entries: usize) -> (Vec<u8>, usize) {
    assert!(nr_entries > 0);

    let msg_bytes = message.as_bytes();

    let bytes_per_entry = msg_bytes.len() as f64 / nr_entries as f64;
    // Rounding is applied for the case if there was a small loss in precision
    let num_bytes_to_fill =
        ((bytes_per_entry.ceil() - bytes_per_entry) * nr_entries as f64).round() as usize;

    let mut bytes: Vec<u8> = vec![];
    for msg_byte in msg_bytes {
        bytes.push(*msg_byte);
    }
    for _i in 0..num_bytes_to_fill {
        // 48 encodes `0`
        bytes.push(48u8);
    }

    (bytes, bytes_per_entry.ceil() as usize)
}

/// Prints at most 4 rows and columns of a matrix.
/// It prints the first three and last one respectively.
/// For example: a matrix A = [[a00, a01, a02, a03, a04, a05],[a10, a11, a02, a13, a14, a15]]
/// would be returned as a readable string of the form:
/// ```txt
/// [
///   [a00, a01, a02, ..., a05],
///   [a10, a11, a12, ..., a15],
/// ]
/// ```
/// If the matrix only has up to 4 rows or columns, they are not cut or interleaved with '...'.
///
/// This function is only relevant internally for pretty debug statements.
///
/// Parameters:
/// - `matrix`: a matrix, e.g. [`MatZ`](crate::integer::MatZ), [`MatQ`](crate::rational::MatQ).
///
/// Returns the Matrix as a simplified [`String`].
pub(crate) fn print_debug_3x3_p1<
    S: Display + Clone,
    T: MatrixGetEntry<S> + MatrixDimensions + MatrixDimensions,
>(
    matrix: &T,
) -> String {
    let rows = matrix.get_num_rows();
    let cols = matrix.get_num_columns();

    let mut result = String::from("[\n");

    for i in 0..rows {
        if rows > 4 && i == 3 {
            result.push_str("  [...],\n");
            continue;
        }
        if rows > 4 && i > 3 && i < rows - 1 {
            // skip all rows from [4, rows - 1]
            continue;
        }

        result.push_str("  [");

        for j in 0..cols {
            if cols > 4 && j == 3 {
                result.push_str(", ..., ");
                continue;
            }
            if cols > 4 && j > 3 && j < cols - 1 {
                // skip all columns from [4, columns - 1]
                continue;
            }

            let entry = matrix.get_entry(i, j).unwrap();
            result.push_str(&format!("{entry}"));

            let is_last = if cols <= 4 {
                j == cols - 1
            } else {
                j == 2 || j == cols - 1
            };

            if !is_last {
                result.push_str(", ");
            }
        }

        result.push(']');
        if i < rows - 1 {
            result.push(',');
        }
        result.push('\n');
    }

    result.push(']');
    result
}

#[cfg(test)]
mod test_parse_matrix_string {
    use crate::utils::parse::parse_matrix_string;

    // Ensure that correct strings of a matrix are accepted.
    #[test]
    fn correct_matrix_work() {
        let matrix_str_1 = "[[1, 2, 3],[3, 4, 5]]";
        let matrix_str_2 = "[[1/3, -2/7, 3],[3, 4, -5/-2]]";
        let matrix_str_3 = "[[4  0 1 2 3, 2  0 1],[1  5, 2  7 8]]";
        let matrix_str_4 = "[[sdclin, =§&%, +57n4],[+dk<, 37 ffew, 8fh2n]]";
        let matrix_str_5 = "[[0],[1]]";

        assert!(parse_matrix_string(matrix_str_1).is_ok());
        assert!(parse_matrix_string(matrix_str_2).is_ok());
        assert!(parse_matrix_string(matrix_str_3).is_ok());
        assert!(parse_matrix_string(matrix_str_4).is_ok());
        assert!(parse_matrix_string(matrix_str_5).is_ok());
    }

    // Ensure that incorrect strings of a matrix are rejected.
    #[test]
    fn incorrect_entries_error() {
        let matrix_str_1 = "[1, 2, 3],[3, 4, 5]";
        let matrix_str_2 = "[1/3, -2/7, 3,[3, 4, -5/-2]]";
        let matrix_str_3 = "[1, [2], 3],[3, 4, 5]";
        let matrix_str_4 = "[1, 2, 3][3, 4, 5]";

        assert!(parse_matrix_string(matrix_str_1).is_err());
        assert!(parse_matrix_string(matrix_str_2).is_err());
        assert!(parse_matrix_string(matrix_str_3).is_err());
        assert!(parse_matrix_string(matrix_str_4).is_err());
    }

    // Ensure that correct strings of a matrix are prepared correctly.
    #[test]
    fn correct_matrix_format() {
        let matrix_str_1 = "[[1, 2, 3],[3, 4, 5]]";
        let matrix_str_2 = "[[1/3, -2/7, 3],[3, 4, -5/-2]]";
        let matrix_str_3 = "[[4  0 1 2 3, 2  0 1],[1  5, 2  7 8]]";
        let matrix_str_4 = "[[sdclin, =§&%, +57n4],[+dk<, 37 ffew, 8fh2n]]";

        assert_eq!(
            parse_matrix_string(matrix_str_1).unwrap()[0][0],
            "1".to_owned()
        );
        assert_eq!(
            parse_matrix_string(matrix_str_2).unwrap()[0][1],
            "-2/7".to_owned()
        );
        assert_eq!(
            parse_matrix_string(matrix_str_3).unwrap()[1][0],
            "1  5".to_owned()
        );
        assert_eq!(
            parse_matrix_string(matrix_str_4).unwrap()[1][2],
            "8fh2n".to_owned()
        );
    }
}

#[cfg(test)]
mod test_matrix_to_string {
    use crate::{integer::MatZ, utils::parse::matrix_to_string};
    use std::str::FromStr;

    /// Tests whether a matrix with a large entry works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = MatZ::from_str(&format!("[[{}, 1, 3],[5, 6, 7]]", u64::MAX)).unwrap();

        assert_eq!(
            format!("[[{}, 1, 3],[5, 6, 7]]", u64::MAX),
            matrix_to_string(&cmp)
        )
    }

    /// Tests whether a matrix with a large negative entry works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = MatZ::from_str(&format!("[[-{}, 1, 3],[5, 6, 7]]", u64::MAX)).unwrap();

        assert_eq!(
            format!("[[-{}, 1, 3],[5, 6, 7]]", u64::MAX),
            matrix_to_string(&cmp)
        )
    }

    /// Tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = MatZ::from_str("[[2, 1, 3],[5, 6, 7]]").unwrap();

        assert_eq!("[[2, 1, 3],[5, 6, 7]]", matrix_to_string(&cmp));
    }

    /// Tests whether a matrix with negative entries works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = MatZ::from_str("[[-2, 1, 3],[5, -6, 7]]").unwrap();

        assert_eq!("[[-2, 1, 3],[5, -6, 7]]", matrix_to_string(&cmp));
    }

    /// Tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_large_dimensions() {
        let cmp_1 = MatZ::from_str(&format!("[{}[5, 6, 7]]", "[1, 2, 3],".repeat(99))).unwrap();
        let cmp_2 = MatZ::from_str(&format!("[[{}1]]", "1, ".repeat(99))).unwrap();

        assert_eq!(
            format!("[{}[5, 6, 7]]", "[1, 2, 3],".repeat(99)),
            matrix_to_string(&cmp_1)
        );
        assert_eq!(
            format!("[[{}1]]", "1, ".repeat(99)),
            matrix_to_string(&cmp_2)
        );
    }

    /// Tests whether a matrix that is created using a string, returns a
    /// string that can be used to create a [`MatZ`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = MatZ::from_str("[[-2, 1, 3],[5, -6, 7]]").unwrap();

        let cmp_str_2 = matrix_to_string(&cmp);

        assert!(MatZ::from_str(&cmp_str_2).is_ok());
    }
}

#[cfg(test)]
mod test_matrix_from_utf8_fill_bytes {
    use super::matrix_from_utf8_fill_bytes;

    /// A static test to ensure the UTF8-Decoding works properly and the correct padding is applied.
    #[test]
    fn static_padding_no_modulus() {
        let message = "five5";
        let matrix_size = 8;

        let (byte_vector, _) = matrix_from_utf8_fill_bytes(message, matrix_size);

        assert_eq!(vec![102, 105, 118, 101, 53, 48, 48, 48], byte_vector);
    }

    /// Ensures that a correct number of bytes is added s.t. every entry
    /// in the matrix has the same number of bytes allocated.
    /// Furthermore, it tests whether the `0`-padding was applied.
    #[test]
    fn padding_no_modulus() {
        let messages = ["abc", "12345", "flag{12345}"];
        let matrix_sizes: [usize; 3] = [6, 12, 15];

        for message in messages {
            for matrix_size in matrix_sizes {
                let (byte_vector, nr_bytes_per_entry) =
                    matrix_from_utf8_fill_bytes(message, matrix_size);

                assert_eq!(byte_vector.len() / matrix_size, nr_bytes_per_entry);
                assert_eq!(
                    0.0f32,
                    (byte_vector.len() as f32 / matrix_size as f32).fract()
                );
                assert_eq!(48u8, byte_vector[byte_vector.len() - 1]);
            }
        }
    }

    /// Ensures that no bytes are added if it isn't necessary, i.e.
    /// if every entry is naturally allocated the same number of bytes.
    #[test]
    fn no_padding_no_modulus() {
        let messages = ["abcdef", "123456", "flag{123456}"];
        let matrix_sizes: [usize; 2] = [3, 6];

        for message in messages {
            for matrix_size in matrix_sizes {
                let (byte_vector, nr_bytes_per_entry) =
                    matrix_from_utf8_fill_bytes(message, matrix_size);

                assert_eq!(byte_vector.len() / matrix_size, nr_bytes_per_entry);
                assert_eq!(
                    0.0f32,
                    (byte_vector.len() as f32 / matrix_size as f32).fract()
                );
                assert_ne!(48u8, byte_vector[byte_vector.len() - 1]);
            }
        }
    }

    /// Ensures that an empty message results in an empty byte-vector.
    #[test]
    fn empty_string() {
        let message = "";
        let matrix_size = 2;
        let cmp_vec: Vec<u8> = vec![];

        let (byte_vector, nr_bytes_per_entry) = matrix_from_utf8_fill_bytes(message, matrix_size);

        assert_eq!(cmp_vec, byte_vector);
        assert_eq!(0, nr_bytes_per_entry);
    }

    /// Ensures that matrices with matrix_size 0 panic.
    #[test]
    #[should_panic]
    fn matrix_size_zero() {
        let message = "abc";
        let matrix_size = 0;

        let _ = matrix_from_utf8_fill_bytes(message, matrix_size);
    }
}

#[cfg(test)]
mod test_debug_string {
    use std::str::FromStr;

    use crate::{integer::MatZ, utils::parse::print_debug_3x3_p1};

    /// Ensure that the entire matrix is printed if the matrix is smaller or equal than a 4x4
    #[test]
    fn print_full_matrix() {
        let matrix_str = "[[1, 2, 3, 4],[3, 4, 5, 6]]";
        let mat = MatZ::from_str(matrix_str).unwrap();

        let cmp_str = "[\n  [1, 2, 3, 4],\n  [3, 4, 5, 6]\n]";
        assert_eq!(cmp_str, print_debug_3x3_p1(&mat))
    }

    /// Ensure that matrices with more than 4 rows are shortened
    #[test]
    fn print_reduced_rows() {
        let matrix_str = "[[1, 2, 3, 4],[3, 4, 5, 6],[3, 4, 5, 6],[3, 4, 5, 6],[3, 4, 5, 6]]";
        let mat = MatZ::from_str(matrix_str).unwrap();

        let cmp_str =
            "[\n  [1, 2, 3, 4],\n  [3, 4, 5, 6],\n  [3, 4, 5, 6],\n  [...],\n  [3, 4, 5, 6]\n]";
        assert_eq!(cmp_str, print_debug_3x3_p1(&mat))
    }

    /// Ensure that matrices with more than 4 columns are shortened
    #[test]
    fn print_reduced_columns() {
        let matrix_str = "[[1, 2, 3, 4, 5, 6, 7, 8],[3, 4, 5, 6, 7, 8, 9, 10]]";
        let mat = MatZ::from_str(matrix_str).unwrap();

        let cmp_str = "[\n  [1, 2, 3, ..., 8],\n  [3, 4, 5, ..., 10]\n]";
        assert_eq!(cmp_str, print_debug_3x3_p1(&mat))
    }
}
