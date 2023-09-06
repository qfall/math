// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implements methods for finding matrix dimensions and enums for detecting vector directions.

use crate::error::{MathError, StringConversionError};

/// Returns the dimensions of a matrix.
/// Takes `[[1, 2, 3],[4, 5, 6]]` as input and outputs `(2, 3)` accordingly.
///
/// Parameters:
/// - `string`: the string of the matrix
///
/// Returns an error if the number of rows or columns is too large
/// (must fit into [`i64`]) or if the number of entries in rows is unequal.
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
/// if the number of rows or columns is too large (must fit into [`i64`]) or
/// if the number of entries in rows is unequal.
#[allow(dead_code)]
pub(crate) fn find_matrix_dimensions<T>(matrix: &Vec<Vec<T>>) -> Result<(i64, i64), MathError> {
    let num_rows = matrix.len();

    let num_rows: i64 = match num_rows.try_into() {
        Ok(num_rows) => num_rows,
        _ => {
            return Err(MathError::StringConversionError(
                StringConversionError::InvalidMatrix(
                    "Number of rows is too large (must fit into [`i64`]).".to_owned(),
                ),
            ))
        }
    };

    let mut num_cols: usize = 0;
    for row in matrix {
        if num_cols == 0 {
            num_cols = row.len();
        } else if num_cols != row.len() {
            return Err(MathError::StringConversionError(
                StringConversionError::InvalidMatrix(
                    "Number of entries in rows is unequal.".to_owned(),
                ),
            ));
        }
    }
    match num_cols.try_into() {
        Ok(num_cols) => Ok((num_rows, num_cols)),
        _ => Err(MathError::StringConversionError(
            StringConversionError::InvalidMatrix(
                "Number of columns is too large (must fit into [`i64`]).".to_owned(),
            ),
        )),
    }
}

#[cfg(test)]
mod test_find_matrix_dimensions {
    use crate::utils::{dimensions::find_matrix_dimensions, parse::parse_matrix_string};

    // Ensure that correct prepared strings of a matrix are accepted.
    #[test]
    fn correct_matrix_works() {
        let matrix_str_1 = "[[1, 2, 3],[3, 4, 5]]";
        let matrix_str_2 = "[[1/3, -2/7, 3],[3, 4, -5/-2]]";
        let matrix_str_3 = "[[4  0 1 2 3, 2  0 1],[1  5, 2  7 8]]";
        let matrix_str_4 = "[[sdclin, =§&%, +57n4],[+dk<, 37 ffew, 8fh2n]]";

        let matrix_1 = parse_matrix_string(matrix_str_1).unwrap();
        let matrix_2 = parse_matrix_string(matrix_str_2).unwrap();
        let matrix_3 = parse_matrix_string(matrix_str_3).unwrap();
        let matrix_4 = parse_matrix_string(matrix_str_4).unwrap();

        assert_eq!(find_matrix_dimensions(&matrix_1).unwrap().0, 2);
        assert_eq!(find_matrix_dimensions(&matrix_1).unwrap().1, 3);
        assert_eq!(find_matrix_dimensions(&matrix_2).unwrap().0, 2);
        assert_eq!(find_matrix_dimensions(&matrix_2).unwrap().1, 3);
        assert_eq!(find_matrix_dimensions(&matrix_3).unwrap().0, 2);
        assert_eq!(find_matrix_dimensions(&matrix_3).unwrap().1, 2);
        assert_eq!(find_matrix_dimensions(&matrix_4).unwrap().0, 2);
        assert_eq!(find_matrix_dimensions(&matrix_4).unwrap().1, 3);
    }

    // Ensure that a matrix with an incorrect number of entries in rows is rejected.
    #[test]
    fn incorrect_rows_error() {
        let matrix_1: Vec<Vec<i64>> = [vec![0; 2], vec![0; 3]].to_vec();

        assert!(find_matrix_dimensions(&matrix_1).is_err());
    }

    // Ensure that dimensions can be detected in large matrices.
    #[test]
    fn large_matrix_works() {
        let mut s_1 = "[[".to_string();
        s_1.push_str(&"1,".repeat(650000));
        s_1.push_str("1]]");
        let mut s_2 = "[".to_string();
        s_2.push_str(&"[1, 1],".repeat(650000));
        s_2.push_str("[1, 1]]");

        let m_1 = parse_matrix_string(&s_1).unwrap();
        let m_2 = parse_matrix_string(&s_2).unwrap();

        assert!(find_matrix_dimensions(&m_1).is_ok());
        assert!(find_matrix_dimensions(&m_2).is_ok());

        assert_eq!(find_matrix_dimensions(&m_1).unwrap().1, 650001);
        assert_eq!(find_matrix_dimensions(&m_2).unwrap().0, 650001);
    }
}
