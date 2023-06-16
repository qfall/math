// Copyright © 2023 Marvin Beckmann, Sven Moog
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
    integer::{MatZ, PolyOverZ},
    traits::*,
    utils::{dimensions::find_matrix_dimensions, parse::parse_matrix_string},
};
use std::str::FromStr;

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
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
    /// ```
    ///
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let str1 = "[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]";
    /// let matrix = MatPolyOverZ::from_str(str1).unwrap();
    /// ```
    ///
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
    /// if the matrix is not formatted in a suitable way, or
    /// if the number of entries in rows is unequal.
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    /// For further information see [`MatPolyOverZ::new`].
    fn from_str(string: &str) -> Result<Self, MathError> {
        let string_matrix = parse_matrix_string(string)?;
        let (num_rows, num_cols) = find_matrix_dimensions(&string_matrix)?;
        let mut matrix = MatPolyOverZ::new(num_rows, num_cols);

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

impl From<&MatZ> for MatPolyOverZ {
    /// Initialize a [`MatPolyOverZ`] with constant polynomials defined by a [`MatZ`].
    ///
    /// # Parameters
    /// - `constants`: A matrix with constant integers.
    ///
    /// Returns a matrix of polynomial that all have the first coefficient
    /// set to the value in the constants matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatZ, MatPolyOverZ};
    ///
    /// let mat_z = MatZ::identity(10,10).unwrap();
    /// let mat_poly = MatPolyOverZ::from(&mat_z);
    /// ```
    fn from(constants: &MatZ) -> Self {
        let num_rows = constants.get_num_rows();
        let num_columns = constants.get_num_columns();
        let mut out = MatPolyOverZ::new(num_rows, constants.get_num_columns()).unwrap();

        for row in 0..num_rows {
            for column in 0..num_columns {
                out.set_entry(
                    row,
                    column,
                    PolyOverZ::from(constants.get_entry(row, column).unwrap()),
                )
                .unwrap();
            }
        }

        out
    }
}

#[cfg(test)]
mod test_from_str {
    use crate::{integer::MatPolyOverZ, traits::GetEntry};
    use std::str::FromStr;

    /// Ensure that initialization works.
    #[test]
    fn init_works() {
        let matrix_str = "[[1  42, 2  24 42, 2  24 42],[2  24 42, 2  24 42, 2  24 42]]";

        assert_eq!(
            "1  42",
            MatPolyOverZ::from_str(matrix_str)
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
        let matrix_str1 = "[[1  42,224 42,2  24 42][2  24 42,2  24 42,2  24 42]]";
        let matrix_str2 = "[[1  42,224 42,2  24 42],2  24 42,2  24 42,2  24 42]]";
        let matrix_str3 = "[1  42,224 42,2  24 42,2  24 42,2  24 42,2  24 42]";
        let matrix_str4 = "[[1  42,224 42,2  24 42,2  24 42,2  24 42,2  24 42]";
        let matrix_str5 = "[ [1  42,224 42,2  242,2  24 42,2  24 42]]";
        let matrix_str6 = "[[1  42,224 42,2  24 42],[2  24 42,2  24 42,2  24 4]2]";
        let matrix_str7 = "";
        let matrix_str8 = "[]";
        let matrix_str9 = "[[]]";

        assert!(MatPolyOverZ::from_str(matrix_str1).is_err());
        assert!(MatPolyOverZ::from_str(matrix_str2).is_err());
        assert!(MatPolyOverZ::from_str(matrix_str3).is_err());
        assert!(MatPolyOverZ::from_str(matrix_str4).is_err());
        assert!(MatPolyOverZ::from_str(matrix_str5).is_err());
        assert!(MatPolyOverZ::from_str(matrix_str6).is_err());
        assert!(MatPolyOverZ::from_str(matrix_str7).is_err());
        assert!(MatPolyOverZ::from_str(matrix_str8).is_err());
        assert!(MatPolyOverZ::from_str(matrix_str9).is_err());
    }
}

#[cfg(test)]
mod test_from_matz {
    use super::*;
    #[test]
    fn small() {
        let matz_str = "[[1,2,3],[4,5,6]]";
        let matz = MatZ::from_str(matz_str).unwrap();

        let mat_poly = MatPolyOverZ::from(&matz);

        let poly_mat_cmp_str = "[[1  1, 1  2, 1  3],[1  4, 1  5, 1  6]]";
        let mat_poly_cmp = MatPolyOverZ::from_str(poly_mat_cmp_str).unwrap();
        assert_eq!(mat_poly, mat_poly_cmp);
    }

    #[test]
    fn large() {
        let matz_str = format!("[[{}],[{}]]", u64::MAX, i64::MIN);
        let matz = MatZ::from_str(&matz_str).unwrap();

        let mat_poly = MatPolyOverZ::from(&matz);

        let poly_mat_cmp_str = format!("[[1  {}],[1  {}]]", u64::MAX, i64::MIN);
        let mat_poly_cmp = MatPolyOverZ::from_str(&poly_mat_cmp_str).unwrap();
        assert_eq!(mat_poly, mat_poly_cmp);
    }

    #[test]
    fn zero() {
        let matz = MatZ::new(100, 100).unwrap();

        let mat_poly = MatPolyOverZ::from(&matz);

        let mat_poly_cmp = MatPolyOverZ::new(100, 100).unwrap();
        assert_eq!(mat_poly, mat_poly_cmp);
    }
}
