// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatPolyOverZ`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::MatPolyOverZ;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    traits::SetEntry,
    utils::{
        coordinate::evaluate_coordinate, dimensions::find_matrix_dimensions,
        parse::parse_matrix_string,
    },
};
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_init;
use std::{fmt::Display, mem::MaybeUninit, str::FromStr};

impl MatPolyOverZ {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns and
    /// zeros as entries, where each entry is a [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    ///
    /// Returns a [`MatPolyOverZ`] or an error, if the number of rows or columns is
    /// less or equal to `0`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let matrix = MatPolyOverZ::new(5, 10).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the number of rows or columns is `0`.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is negative or it does not fit into an [`i64`].
    pub fn new(
        num_rows: impl TryInto<i64> + Display + Copy,
        num_cols: impl TryInto<i64> + Display + Copy,
    ) -> Result<Self, MathError> {
        let num_rows_i64 = evaluate_coordinate(num_rows)?;
        let num_cols_i64 = evaluate_coordinate(num_cols)?;

        if num_rows_i64 == 0 || num_cols_i64 == 0 {
            return Err(MathError::InvalidMatrix(format!(
                "The provided matrix has dimensions ({},{})",
                num_rows, num_cols,
            )));
        }

        // Initialize variable with MaybeUn-initialized value to check
        // correctness of initialization later
        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_poly_mat_init(matrix.as_mut_ptr(), num_rows_i64, num_cols_i64);

            // Construct MatPolyOverZ from previously initialized fmpz_poly_mat
            Ok(MatPolyOverZ {
                matrix: matrix.assume_init(),
            })
        }
    }
}

impl FromStr for MatPolyOverZ {
    type Err = MathError;

    /// Creates a [`MatPolyOverZ`] matrix from a [`String`].
    /// The format of that string looks like <br>
    /// `[[poly1,poly2,poly3],[poly4,poly5,poly6]]` for a 2x3 matrix
    /// where thirst three polynomials are in the first row and the second three are
    /// in the second row.
    ///
    /// Parameters:
    /// - `string`: the matrix as a string
    ///
    /// Returns a [`MatPolyOverZ`] or an error, if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too big (must fit into [`i64`]),
    /// the number of entries in rows is unequal or if the regular expression
    /// inside of the function could not be processed.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]");
    /// let matrix = MatPolyOverZ::from_str(&string).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::InvalidStringToPolyInput`],
    /// [`InvalidStringToPolyMissingWhitespace`](MathError::InvalidStringToPolyMissingWhitespace) or
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if the entries are not formatted correctly. For further details see [`PolyOverZ::from_str`]
    /// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too big (must fit into [`i64`]) or
    /// if the number of entries in rows is unequal.
    fn from_str(string: &str) -> Result<Self, MathError> {
        let string_matrix = parse_matrix_string(string)?;
        let (num_rows, num_cols) = find_matrix_dimensions(&string_matrix)?;
        let mut matrix = MatPolyOverZ::new(num_rows, num_cols)?;

        // fill entries of matrix according to entries in string_matrix
        for (row_num, row) in string_matrix.iter().enumerate() {
            for (col_num, entry) in row.iter().enumerate() {
                let z_entry = PolyOverZ::from_str(entry)?;
                matrix.set_entry(row_num, col_num, z_entry)?;
            }
        }
        Ok(matrix)
    }
}

#[cfg(test)]
mod test_new {
    use crate::{integer::MatPolyOverZ, traits::GetEntry};

    /// Ensure that entries of a new matrix are `0`.
    #[test]
    fn entry_zero() {
        let matrix = MatPolyOverZ::new(2, 2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(0, 1).unwrap();
        let entry3 = matrix.get_entry(1, 0).unwrap();
        let entry4 = matrix.get_entry(1, 1).unwrap();

        assert_eq!("0", entry1.to_string());
        assert_eq!("0", entry2.to_string());
        assert_eq!("0", entry3.to_string());
        assert_eq!("0", entry4.to_string());
    }

    /// Ensure that a new zero matrix fails with `0` as input.
    #[test]
    fn error_zero() {
        let matrix1 = MatPolyOverZ::new(1, 0);
        let matrix2 = MatPolyOverZ::new(0, 1);
        let matrix3 = MatPolyOverZ::new(0, 0);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
        assert!(matrix3.is_err());
    }
}

#[cfg(test)]
mod test_from_str {
    use crate::{integer::MatPolyOverZ, traits::GetEntry};
    use std::str::FromStr;

    /// Ensure that initialization works.
    #[test]
    fn init_works() {
        let matrix_string1 =
            String::from("[[1  42, 2  24 42, 2  24 42],[2  24 42, 2  24 42, 2  24 42]]");

        assert_eq!(
            "1  42",
            MatPolyOverZ::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
                .to_string(),
        );
    }

    /// Ensure that initialization with polynomials with positive coefficients that are
    /// larger than [`i64`] works.
    #[test]
    fn init_works_large_numbers() {
        let entry = format!("1  {}", u64::MAX);
        let matrix_string1 = format!(
            "[[{}, 2  24 42, 2  24 42],[2  24 42, 2  24 42, 2  24 42]]",
            entry,
        );

        assert_eq!(
            entry,
            MatPolyOverZ::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
                .to_string(),
        );
    }

    /// Ensure that initialization with polynomials with negative coefficients that
    /// are larger than [`i64`] works.
    #[test]
    fn init_works_small_numbers() {
        let entry = format!("1  -{}", u64::MAX);
        let matrix_string1 = format!(
            "[[{}, 2  24 42, 2  24 42],[2  24 42, 2  24 42, 2  24 42]]",
            entry,
        );

        assert_eq!(
            entry,
            MatPolyOverZ::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
                .to_string(),
        );
    }

    /// Ensure that entries can have whitespaces leading and trailing.
    #[test]
    fn whitespaces_in_entries_works() {
        let entry = format!("1  {}            ", u64::MAX);
        let matrix_string1 = format!(
            "[[{},     2  24 42, 2  24 42     ],[  2  24 42, 2  24 42  ,   2  24 42]]",
            entry,
        );

        assert_eq!(
            format!("1  {}", u64::MAX),
            MatPolyOverZ::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
                .to_string(),
        );
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_string1 = String::from("[[1  42,224 42,2  24 42][2  24 42,2  24 42,2  24 42]]");
        let matrix_string2 = String::from("[[1  42,224 42,2  24 42],2  24 42,2  24 42,2  24 42]]");
        let matrix_string3 = String::from("[1  42,224 42,2  24 42,2  24 42,2  24 42,2  24 42]");
        let matrix_string4 = String::from("[[1  42,224 42,2  24 42,2  24 42,2  24 42,2  24 42]");
        let matrix_string5 =
            String::from("[ [1  42,224 42,2  24 42],[2  24 42,2  24 42,2  24 42]]");
        let matrix_string6 = String::from("[[1  42,224 42,2  24 42],[2  24 42,2  24 42,2  24 4]2]");
        let matrix_string7 = String::from("");
        let matrix_string8 = String::from("[]");
        let matrix_string9 = String::from("[[]]");

        assert!(MatPolyOverZ::from_str(&matrix_string1).is_err());
        assert!(MatPolyOverZ::from_str(&matrix_string2).is_err());
        assert!(MatPolyOverZ::from_str(&matrix_string3).is_err());
        assert!(MatPolyOverZ::from_str(&matrix_string4).is_err());
        assert!(MatPolyOverZ::from_str(&matrix_string5).is_err());
        assert!(MatPolyOverZ::from_str(&matrix_string6).is_err());
        assert!(MatPolyOverZ::from_str(&matrix_string7).is_err());
        assert!(MatPolyOverZ::from_str(&matrix_string8).is_err());
        assert!(MatPolyOverZ::from_str(&matrix_string9).is_err());
    }
}
