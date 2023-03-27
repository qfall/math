// Copyright © 2023 Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implements methods to parse a [`String`] e.g. matrix strings.

use crate::error::MathError;
use regex::Regex;

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
#[allow(dead_code)]
pub(crate) fn parse_matrix_string(string: &str) -> Result<Vec<Vec<String>>, MathError> {
    // check if the matrix format is correct
    let entry_str = r"([^\[\],]+)";
    let row_str = format!(r"\[({},)*({})\]", entry_str, entry_str);
    let matrix_str = format!(r"^\[({},)*({})\]$", row_str, row_str);
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

pub(crate) fn parse_vector_string(string: &str) -> Result<Vec<String>, MathError> {
    // check if the matrix format is correct
    let entry_str = r"([^\[\],]+)";
    let row_str = format!(r"^\[({},)*({})\]$", entry_str, entry_str);
    let regex = Regex::new(&row_str).expect("The regular expression could not be processed.");

    // explanation of this regex:
    // it checks whether the string start with a '[' and ends with a ']'
    // we differ between the first/several and the last entry the vector (as there is no comma after the last entry)
    // each entry can contain any symbol but `[`, `]` and `,`. It needs to have at least one symbol.
    if !regex.is_match(string) {
        return Err(MathError::InvalidMatrix(
            "The matrix is not formatted in a suitable way.".to_owned(),
        ));
    }

    // delete `[` in front and `]` in the end and split the string into its entries
    let entries = string[1..string.len() - 1].split(',');

    let mut vector: Vec<String> = Vec::new();
    for entry in entries {
        // delete leading and trailing whitespaces from the entry and
        // adds it to the row vector
        vector.push(entry.trim().to_owned());
    }

    Ok(vector)
}

#[cfg(test)]
mod test_parse_matrix_string {
    use crate::utils::parse::parse_matrix_string;

    // Ensure that correct strings of a matrix are accepted.
    #[test]
    fn correct_matrix_work() {
        let matrix_string1 = String::from("[[1, 2, 3],[3, 4, 5]]");
        let matrix_string2 = String::from("[[1/3, -2/7, 3],[3, 4, -5/-2]]");
        let matrix_string3 = String::from("[[4  0 1 2 3, 2  0 1],[1  5, 2  7 8]]");
        let matrix_string4 = String::from("[[sdclin, =§&%, +57n4],[+dk<, 37 ffew, 8fh2n]]");

        assert!(parse_matrix_string(&matrix_string1).is_ok());
        assert!(parse_matrix_string(&matrix_string2).is_ok());
        assert!(parse_matrix_string(&matrix_string3).is_ok());
        assert!(parse_matrix_string(&matrix_string4).is_ok());
    }

    // Ensure that incorrect strings of a matrix are rejected.
    #[test]
    fn incorrect_entries_error() {
        let matrix_string1 = String::from("[1, 2, 3],[3, 4, 5]");
        let matrix_string2 = String::from("[1/3, -2/7, 3,[3, 4, -5/-2]]");
        let matrix_string3 = String::from("[1, [2], 3],[3, 4, 5]");
        let matrix_string4 = String::from("[1, 2, 3][3, 4, 5]");

        assert!(parse_matrix_string(&matrix_string1).is_err());
        assert!(parse_matrix_string(&matrix_string2).is_err());
        assert!(parse_matrix_string(&matrix_string3).is_err());
        assert!(parse_matrix_string(&matrix_string4).is_err());
    }

    // Ensure that correct strings of a matrix are prepared correctly.
    #[test]
    fn correct_matrix_format() {
        let matrix_string1 = String::from("[[1, 2, 3],[3, 4, 5]]");
        let matrix_string2 = String::from("[[1/3, -2/7, 3],[3, 4, -5/-2]]");
        let matrix_string3 = String::from("[[4  0 1 2 3, 2  0 1],[1  5, 2  7 8]]");
        let matrix_string4 = String::from("[[sdclin, =§&%, +57n4],[+dk<, 37 ffew, 8fh2n]]");

        assert_eq!(
            parse_matrix_string(&matrix_string1).unwrap()[0][0],
            "1".to_owned()
        );
        assert_eq!(
            parse_matrix_string(&matrix_string2).unwrap()[0][1],
            "-2/7".to_owned()
        );
        assert_eq!(
            parse_matrix_string(&matrix_string3).unwrap()[1][0],
            "1  5".to_owned()
        );
        assert_eq!(
            parse_matrix_string(&matrix_string4).unwrap()[1][2],
            "8fh2n".to_owned()
        );
    }
}

#[cfg(test)]
mod test_parse_vector_string {
    use crate::utils::parse::parse_vector_string;

    // Ensure that correct strings of a vector are accepted.
    #[test]
    fn correct_vector_work() {
        let vector_string1 = String::from("[1, 2, 3]");
        let vector_string2 = String::from("[1/3, -2/7, 3]");
        let vector_string3 = String::from("[4  0 1 2 3, 2  0 1]");
        let vector_string4 = String::from("[sdclin, =§&%, +57n4]");

        assert!(parse_vector_string(&vector_string1).is_ok());
        assert!(parse_vector_string(&vector_string2).is_ok());
        assert!(parse_vector_string(&vector_string3).is_ok());
        assert!(parse_vector_string(&vector_string4).is_ok());
    }

    // Ensure that incorrect strings of a vector are rejected.
    #[test]
    fn incorrect_entries_error() {
        let vector_string1 = String::from("[1, 2, 3],");
        let vector_string2 = String::from("[1/3, -2/7, 3,[3, 4, -5/-2]]");
        let vector_string3 = String::from("[1, [2], 3],[3, 4, 5]");
        let vector_string4 = String::from("[1, 2, 3][3, 4, 5]");
        let vector_string5 = String::from("[[1, 2, 3]]");

        assert!(parse_vector_string(&vector_string1).is_err());
        assert!(parse_vector_string(&vector_string2).is_err());
        assert!(parse_vector_string(&vector_string3).is_err());
        assert!(parse_vector_string(&vector_string4).is_err());
        assert!(parse_vector_string(&vector_string5).is_err());
    }

    // Ensure that correct strings of a vector are prepared correctly.
    #[test]
    fn correct_vector_format() {
        let vector_string1 = String::from("[1, 2, 3]");
        let vector_string2 = String::from("[1/3, -2/7, 3,3, 4, -5/-2]");
        let vector_string3 = String::from("[4  0 1 2 3, 2  0 1,1  5, 2  7 8]");
        let vector_string4 = String::from("[sdclin, +dk<, 37 ffew, 8fh2n]");

        assert_eq!(
            parse_vector_string(&vector_string1).unwrap()[0],
            "1".to_owned()
        );
        assert_eq!(
            parse_vector_string(&vector_string2).unwrap()[1],
            "-2/7".to_owned()
        );
        assert_eq!(
            parse_vector_string(&vector_string3).unwrap()[2],
            "1  5".to_owned()
        );
        assert_eq!(
            parse_vector_string(&vector_string4).unwrap()[3],
            "8fh2n".to_owned()
        );
    }
}
