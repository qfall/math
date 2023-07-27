// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implements methods to parse a [`String`] e.g. matrix strings.

use crate::{
    error::MathError,
    traits::{GetEntry, GetNumColumns, GetNumRows},
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
/// Returns the Matrix in form of a two dimensional vector with the entries
/// stored as strings or an error, if the matrix is not formatted correctly.
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
/// if the matrix is not formatted in a suitable way.
pub(crate) fn parse_matrix_string(string: &str) -> Result<Vec<Vec<String>>, MathError> {
    // check if the matrix format is correct
    let entry_str = r"([^\[\],]+)";
    let row_str = format!(r"\[({entry_str},)*({entry_str})\]");
    let matrix_str = format!(r"^\[({row_str},)*({row_str})\]$");
    let regex = Regex::new(&matrix_str).expect("The regular expression could not be processed.");

    // explanation of this regex:
    // it checks whether the string start with a '[' and ends with a ']'
    // we differ between the first/several and the last row (as there is no comma after the last row)
    // each row needs to start with a '[' and end with a ']'
    // we differ between the first/several and the last entry in each row (as there is no comma after the last entry)
    // each entry can contain any symbol but `[`, `]` and `,`. It needs to have at least one symbol.
    if !regex.is_match(string) {
        return Err(MathError::InvalidMatrix(
            "The matrix is not formatted in a suitable way.".to_owned(),
        ));
    }

    // delete `[[` in front and `]]` in the end and split the matrix into rows
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
pub(crate) fn matrix_to_string<S: Display, T: GetEntry<S> + GetNumRows + GetNumColumns>(
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

#[cfg(test)]
mod test_parse_matrix_string {
    use crate::utils::parse::parse_matrix_string;

    // Ensure that correct strings of a matrix are accepted.
    #[test]
    fn correct_matrix_work() {
        let matrix_str1 = "[[1, 2, 3],[3, 4, 5]]";
        let matrix_str2 = "[[1/3, -2/7, 3],[3, 4, -5/-2]]";
        let matrix_str3 = "[[4  0 1 2 3, 2  0 1],[1  5, 2  7 8]]";
        let matrix_str4 = "[[sdclin, =§&%, +57n4],[+dk<, 37 ffew, 8fh2n]]";
        let matrix_str5 = "[[0],[1]]";

        assert!(parse_matrix_string(matrix_str1).is_ok());
        assert!(parse_matrix_string(matrix_str2).is_ok());
        assert!(parse_matrix_string(matrix_str3).is_ok());
        assert!(parse_matrix_string(matrix_str4).is_ok());
        assert!(parse_matrix_string(matrix_str5).is_ok());
    }

    // Ensure that incorrect strings of a matrix are rejected.
    #[test]
    fn incorrect_entries_error() {
        let matrix_str1 = "[1, 2, 3],[3, 4, 5]";
        let matrix_str2 = "[1/3, -2/7, 3,[3, 4, -5/-2]]";
        let matrix_str3 = "[1, [2], 3],[3, 4, 5]";
        let matrix_str4 = "[1, 2, 3][3, 4, 5]";

        assert!(parse_matrix_string(matrix_str1).is_err());
        assert!(parse_matrix_string(matrix_str2).is_err());
        assert!(parse_matrix_string(matrix_str3).is_err());
        assert!(parse_matrix_string(matrix_str4).is_err());
    }

    // Ensure that correct strings of a matrix are prepared correctly.
    #[test]
    fn correct_matrix_format() {
        let matrix_str1 = "[[1, 2, 3],[3, 4, 5]]";
        let matrix_str2 = "[[1/3, -2/7, 3],[3, 4, -5/-2]]";
        let matrix_str3 = "[[4  0 1 2 3, 2  0 1],[1  5, 2  7 8]]";
        let matrix_str4 = "[[sdclin, =§&%, +57n4],[+dk<, 37 ffew, 8fh2n]]";

        assert_eq!(
            parse_matrix_string(matrix_str1).unwrap()[0][0],
            "1".to_owned()
        );
        assert_eq!(
            parse_matrix_string(matrix_str2).unwrap()[0][1],
            "-2/7".to_owned()
        );
        assert_eq!(
            parse_matrix_string(matrix_str3).unwrap()[1][0],
            "1  5".to_owned()
        );
        assert_eq!(
            parse_matrix_string(matrix_str4).unwrap()[1][2],
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

        assert_eq!("[[2, 1, 3],[5, 6, 7]]", matrix_to_string(&cmp))
    }

    /// Tests whether a matrix with negative entries works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = MatZ::from_str("[[-2, 1, 3],[5, -6, 7]]").unwrap();

        assert_eq!("[[-2, 1, 3],[5, -6, 7]]", matrix_to_string(&cmp));
    }

    /// Tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_big_dimensions() {
        let cmp1 = MatZ::from_str(&format!("[{}[5, 6, 7]]", "[1, 2, 3],".repeat(99))).unwrap();
        let cmp2 = MatZ::from_str(&format!("[[{}1]]", "1, ".repeat(99))).unwrap();

        assert_eq!(
            format!("[{}[5, 6, 7]]", "[1, 2, 3],".repeat(99)),
            matrix_to_string(&cmp1)
        );
        assert_eq!(
            format!("[[{}1]]", "1, ".repeat(99)),
            matrix_to_string(&cmp2)
        );
    }

    /// Tests whether a matrix that is created using a string, returns a
    /// string that can be used to create a [`MatZ`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = MatZ::from_str("[[-2, 1, 3],[5, -6, 7]]").unwrap();

        let cmp_string2 = matrix_to_string(&cmp);

        assert!(MatZ::from_str(&cmp_string2).is_ok())
    }
}
