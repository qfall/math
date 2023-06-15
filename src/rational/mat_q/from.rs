// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatQ`](crate::rational::MatQ) value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::MatQ;
use crate::{
    error::MathError,
    integer::MatZ,
    rational::Q,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::{dimensions::find_matrix_dimensions, parse::parse_matrix_string},
};
use flint_sys::fmpq_mat::fmpq_mat_set_fmpz_mat;
use std::str::FromStr;

impl MatQ {
    /// Create a [`MatQ`] from a [`MatZ`].
    ///
    /// Parameters:
    /// - `matrix`: the matrix from which the entries are taken
    ///
    /// Returns the new matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let m = MatZ::from_str("[[1, 2],[3, -1]]").unwrap();
    ///
    /// let a = MatQ::from_mat_z(&m);
    /// ```
    pub fn from_mat_z(matrix: &MatZ) -> Self {
        let mut out = MatQ::new(matrix.get_num_rows(), matrix.get_num_columns()).unwrap();
        unsafe { fmpq_mat_set_fmpz_mat(&mut out.matrix, &matrix.matrix) };
        out
    }
}

impl FromStr for MatQ {
    type Err = MathError;

    /// Creates a [`MatQ`] matrix with entries in [`Q`] from a [`String`].
    /// The format of that string looks like this <br> `[[1/2,2/3,3/4],[4/5,5/6,6/7]]` for a 2x3 matrix
    /// with entries 1/2,2/3,3/4 in the first row and 4/5,5/6,6/7 in the second row.
    ///
    /// Parameters:
    /// - `string`: the matrix as a string
    ///
    /// Returns a [`MatQ`] or an error, if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too big (must fit into [`i64`]),
    /// the number of entries in rows is unequal or if the regular expression
    /// inside of the function could not be processed.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[1/2,2/3,3/4],[4/5,5/6,6/7]]").unwrap();
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let str1 = "[[1/2,2/3,3/4],[4/5,5/6,6/7]]";
    /// let matrix = MatQ::from_str(str1).unwrap();
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1/2,2/3,3/4],[4/5,5/6,6/7]]");
    /// let matrix = MatQ::from_str(&string).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too big (must fit into [`i64`]) or
    /// if the number of entries in rows is unequal.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if an entry contains a Nul byte.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToZInput`](MathError::InvalidStringToZInput)
    /// if an entry is not formatted correctly.
    fn from_str(string: &str) -> Result<Self, MathError> {
        let string_matrix = parse_matrix_string(string)?;
        let (num_rows, num_cols) = find_matrix_dimensions(&string_matrix)?;
        let mut matrix = MatQ::new(num_rows, num_cols)?;

        // fill entries of matrix according to entries in string_matrix
        for (row_num, row) in string_matrix.iter().enumerate() {
            for (col_num, entry) in row.iter().enumerate() {
                let q_entry = Q::from_str(entry)?;
                matrix.set_entry(row_num, col_num, q_entry)?;
            }
        }
        Ok(matrix)
    }
}

impl From<&MatZ> for MatQ {
    /// Convert [`MatZ`] to [`MatQ`] using [`MatQ::from_mat_z`].
    fn from(matrix: &MatZ) -> Self {
        Self::from_mat_z(matrix)
    }
}

#[cfg(test)]
mod test_from_mat_zq {
    use crate::{
        integer::{MatZ, Z},
        rational::{MatQ, Q},
        traits::{GetEntry, GetNumColumns, GetNumRows, SetEntry},
    };

    /// Test if the dimensions are taken over correctly
    #[test]
    fn dimensions() {
        let matz = MatZ::new(15, 17);

        let matq_1 = MatQ::from(&matz);
        let matq_2 = MatQ::from_mat_z(&matz);

        assert_eq!(15, matq_1.get_num_rows());
        assert_eq!(17, matq_1.get_num_columns());
        assert_eq!(15, matq_2.get_num_rows());
        assert_eq!(17, matq_2.get_num_columns());
    }

    /// Test if entries are taken over correctly
    #[test]
    fn entries_taken_over_correctly() {
        let mut matz = MatZ::new(2, 2);
        matz.set_entry(0, 0, u64::MAX - 58).unwrap();
        matz.set_entry(0, 1, i64::MIN).unwrap();

        let matq_1 = MatQ::from(&matz);
        let matq_2 = MatQ::from_mat_z(&matz);

        assert_eq!(Q::from(Z::from(i64::MIN)), matq_1.get_entry(0, 1).unwrap());
        assert_eq!(
            Q::from(Z::from(u64::MAX - 58)),
            matq_1.get_entry(0, 0).unwrap()
        );
        assert_eq!(Q::from(Z::from(i64::MIN)), matq_2.get_entry(0, 1).unwrap());
        assert_eq!(
            Q::from(Z::from(u64::MAX - 58)),
            matq_2.get_entry(0, 0).unwrap()
        );
    }
}

#[cfg(test)]
mod test_from_str {
    use crate::{
        integer::Z,
        rational::{MatQ, Q},
        traits::GetEntry,
    };
    use std::str::FromStr;

    /// Ensure that initialization works.
    #[test]
    fn init_works() {
        let matrix_str1 = "[[1/2,2/3,3/4],[4/5,5/6,6/7]]";

        assert_eq!(
            Q::from_str("1/2").unwrap(),
            MatQ::from_str(matrix_str1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that initialization works with integers.
    #[test]
    fn init_integer_works() {
        let matrix_str1 = "[[1, 2, 3],[3, 4, 5]]";

        assert_eq!(
            Z::ONE,
            Z {
                value: MatQ::from_str(matrix_str1)
                    .unwrap()
                    .get_entry(0, 0)
                    .unwrap()
                    .value
                    .num
            }
        );

        assert_eq!(
            Z::ONE,
            Z {
                value: MatQ::from_str(matrix_str1)
                    .unwrap()
                    .get_entry(0, 0)
                    .unwrap()
                    .value
                    .den
            }
        );
    }

    /// Ensure that initialization with positive numerators and denominators
    /// that are larger than [`i64`] works.
    #[test]
    fn init_works_large_numbers() {
        let matrix_string = format!("[[{}/1, 1/{}, 3],[3, 4, 5]]", u64::MAX, u64::MAX);

        assert_eq!(
            Z::from_str(&format!("{}", u64::MAX)).unwrap(),
            Z {
                value: MatQ::from_str(&matrix_string)
                    .unwrap()
                    .get_entry(0, 0)
                    .unwrap()
                    .value
                    .num
            }
        );

        assert_eq!(
            Z::from_str(&format!("{}", u64::MAX)).unwrap(),
            Z {
                value: MatQ::from_str(&matrix_string)
                    .unwrap()
                    .get_entry(0, 1)
                    .unwrap()
                    .value
                    .den
            }
        );
    }

    /// Ensure that initialization with negative large numerators and denominators
    /// that are larger than [`i64`] works.
    #[test]
    fn init_works_small_numbers() {
        let matrix_string = format!("[[-{}/1, 1/-{}, 3],[3, 4, 5]]", u64::MAX, u64::MAX);

        assert_eq!(
            Q::from_str(&format!("-{}", u64::MAX)).unwrap(),
            MatQ::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );

        assert_eq!(
            Q::from_str(&format!("1/-{}", u64::MAX)).unwrap(),
            MatQ::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 1)
                .unwrap()
        );
    }

    /// Ensure that entries can have leading and trailing whitespaces.
    #[test]
    fn whitespaces_in_entries_works() {
        let matrix_str1 = "[[  1/2, 2/3 ,  3/4  ],[3/4 ,4/5,5/6 ]]";

        assert_eq!(
            Q::from_str("1/2").unwrap(),
            MatQ::from_str(matrix_str1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_str1 = "[1/2, 2, 3],[3, 4/7, 5]]";
        let matrix_str2 = "[[1, 2/9, 3][3, 4, 5/5]]";
        let matrix_str3 = "[[1, 2, 3/2],3, 4, 5]";
        let matrix_str4 = "[1, 2, 3, 4/5, 5]";
        let matrix_str5 = "[ [1, 2/8, 3],[3, 4, 5]]";
        let matrix_str6 = "[[1, 2, 3],[3, 4/9, 5]8]";
        let matrix_str7 = "";
        let matrix_str8 = "[]";
        let matrix_str9 = "[[]]";

        assert!(MatQ::from_str(matrix_str1).is_err());
        assert!(MatQ::from_str(matrix_str2).is_err());
        assert!(MatQ::from_str(matrix_str3).is_err());
        assert!(MatQ::from_str(matrix_str4).is_err());
        assert!(MatQ::from_str(matrix_str5).is_err());
        assert!(MatQ::from_str(matrix_str6).is_err());
        assert!(MatQ::from_str(matrix_str7).is_err());
        assert!(MatQ::from_str(matrix_str8).is_err());
        assert!(MatQ::from_str(matrix_str9).is_err());
    }
}
