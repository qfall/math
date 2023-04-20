// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implements methods for finding matrix dimensions and enums for detecting vector directions.

use crate::error::MathError;

/// Returns the dimensions of a matrix.
/// Takes `[[1, 2, 3],[4, 5, 6]]` as input and outputs `(2,3)` accordingly.
///
/// Parameters:
/// - `string`: the string of the matrix
///
/// Returns an error if the number of rows or columns is too big
/// (must fit into [`i64`]) or if the number of entries in rows is unequal.
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
/// if the number of rows or columns is too big (must fit into [`i64`]) or
/// if the number of entries in rows is unequal.
#[allow(dead_code)]
pub(crate) fn find_matrix_dimensions<T>(matrix: &Vec<Vec<T>>) -> Result<(i64, i64), MathError> {
    let num_rows = matrix.len();

    let num_rows: i64 = match num_rows.try_into() {
        Ok(num_rows) => num_rows,
        _ => {
            return Err(MathError::InvalidMatrix(
                "Number of rows is too big (must fit into [`i64`]).".to_owned(),
            ))
        }
    };

    let mut num_cols: usize = 0;
    for row in matrix {
        if num_cols == 0 {
            num_cols = row.len();
        } else if num_cols != row.len() {
            return Err(MathError::InvalidMatrix(
                "Number of entries in rows is unequal.".to_owned(),
            ));
        }
    }
    match num_cols.try_into() {
        Ok(num_cols) => Ok((num_rows, num_cols)),
        _ => Err(MathError::InvalidMatrix(
            "Number of columns is too big (must fit into [`i64`]).".to_owned(),
        )),
    }
}

#[cfg(test)]
mod test_find_matrix_dimensions {
    use crate::utils::{dimensions::find_matrix_dimensions, parse::parse_matrix_string};

    // Ensure that correct prepared strings of a matrix are accepted.
    #[test]
    fn correct_matrix_works() {
        let matrix_str1 = "[[1, 2, 3],[3, 4, 5]]";
        let matrix_str2 = "[[1/3, -2/7, 3],[3, 4, -5/-2]]";
        let matrix_str3 = "[[4  0 1 2 3, 2  0 1],[1  5, 2  7 8]]";
        let matrix_str4 = "[[sdclin, =§&%, +57n4],[+dk<, 37 ffew, 8fh2n]]";

        let matrix1 = parse_matrix_string(matrix_str1).unwrap();
        let matrix2 = parse_matrix_string(matrix_str2).unwrap();
        let matrix3 = parse_matrix_string(matrix_str3).unwrap();
        let matrix4 = parse_matrix_string(matrix_str4).unwrap();

        assert_eq!(find_matrix_dimensions(&matrix1).unwrap().0, 2);
        assert_eq!(find_matrix_dimensions(&matrix1).unwrap().1, 3);
        assert_eq!(find_matrix_dimensions(&matrix2).unwrap().0, 2);
        assert_eq!(find_matrix_dimensions(&matrix2).unwrap().1, 3);
        assert_eq!(find_matrix_dimensions(&matrix3).unwrap().0, 2);
        assert_eq!(find_matrix_dimensions(&matrix3).unwrap().1, 2);
        assert_eq!(find_matrix_dimensions(&matrix4).unwrap().0, 2);
        assert_eq!(find_matrix_dimensions(&matrix4).unwrap().1, 3);
    }

    // Ensure that a matrix with an incorrect number of entries in rows is rejected.
    #[test]
    fn incorrect_rows_error() {
        let matrix1: Vec<Vec<i64>> = [vec![0; 2], vec![0; 3]].to_vec();

        assert!(find_matrix_dimensions(&matrix1).is_err());
    }

    // Ensure that dimensions can be detected in big matrices.
    #[test]
    fn big_matrix_works() {
        let mut s1 = "[[".to_string();
        s1.push_str(&"1,".repeat(650000));
        s1.push_str("1]]");
        let mut s2 = "[".to_string();
        s2.push_str(&"[1,1],".repeat(650000));
        s2.push_str("[1,1]]");

        let m1 = parse_matrix_string(&s1).unwrap();
        let m2 = parse_matrix_string(&s2).unwrap();

        assert!(find_matrix_dimensions(&m1).is_ok());
        assert!(find_matrix_dimensions(&m2).is_ok());

        assert_eq!(find_matrix_dimensions(&m1).unwrap().1, 650001);
        assert_eq!(find_matrix_dimensions(&m2).unwrap().0, 650001);
    }
}
