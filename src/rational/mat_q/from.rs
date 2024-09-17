// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatQ`] value from other types.
//!
//! The explicit functions contain the documentation.

use super::MatQ;
use crate::{
    error::MathError,
    integer::MatZ,
    macros::for_others::implement_for_owned,
    rational::Q,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::{dimensions::find_matrix_dimensions, parse::parse_matrix_string},
};
use flint_sys::fmpq_mat::fmpq_mat_set_fmpz_mat;
use std::str::FromStr;

impl FromStr for MatQ {
    type Err = MathError;

    /// Creates a [`MatQ`] matrix with entries in [`Q`] from a [`String`].
    ///
    /// Parameters:
    /// - `string`: the matrix of form: `"[[1/2, 2/3, 3/4],[4/5, 5/6, 6/7]"` 
    ///     for a 2x3 matrix with entries 1/2, 2/3, 3/4 in the first row 
    ///     and 4/5, 5/6, 6/7 in the second row.
    ///
    /// Returns a [`MatQ`] or an error, if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too large (must fit into [`i64`]),
    /// the number of entries in rows is unequal or if the regular expression
    /// inside of the function could not be processed.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[1/2, 2/3, 3/4],[4/5, 5/6, 6/7]]").unwrap();
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let str_1 = "[[1/2, 2/3, 3/4],[4/5, 5/6, 6/7]]";
    /// let matrix = MatQ::from_str(str_1).unwrap();
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1/2, 2/3, 3/4],[4/5, 5/6, 6/7]]");
    /// let matrix = MatQ::from_str(&string).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
    ///     - if the matrix is not formatted in a suitable way,
    ///     - if the number of rows or columns is too large (must fit into i64),
    ///     - if the number of entries in rows is unequal, or
    ///     - if an entry is not formatted correctly.
    ///         For further information see [`Q::from_str`].
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    ///     For further information see [`MatQ::new`].
    fn from_str(string: &str) -> Result<Self, MathError> {
        let string_matrix = parse_matrix_string(string)?;
        let (num_rows, num_cols) = find_matrix_dimensions(&string_matrix)?;
        let mut matrix = MatQ::new(num_rows, num_cols);

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
    /// Creates a [`MatQ`] from a [`MatZ`].
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
    /// let a = MatQ::from(&m);
    /// ```
    fn from(matrix: &MatZ) -> Self {
        let mut out = MatQ::new(matrix.get_num_rows(), matrix.get_num_columns());
        unsafe { fmpq_mat_set_fmpz_mat(&mut out.matrix, &matrix.matrix) };
        out
    }
}

implement_for_owned!(MatZ, MatQ, From);

impl From<&MatQ> for MatQ {
    /// Alias for [`MatQ::clone`].
    fn from(value: &MatQ) -> Self {
        value.clone()
    }
}

#[cfg(test)]
mod test_from_mat_zq {
    use crate::{
        integer::MatZ,
        rational::{MatQ, Q},
        traits::{GetEntry, GetNumColumns, GetNumRows, SetEntry},
    };
    use std::str::FromStr;

    /// Test if the dimensions are taken over correctly
    #[test]
    fn dimensions() {
        let matz = MatZ::new(15, 17);

        let matq_1 = MatQ::from(&matz);

        assert_eq!(15, matq_1.get_num_rows());
        assert_eq!(17, matq_1.get_num_columns());
    }

    /// Test if entries are taken over correctly
    #[test]
    fn entries_taken_over_correctly() {
        let mut matz = MatZ::new(2, 2);
        matz.set_entry(0, 0, u64::MAX - 58).unwrap();
        matz.set_entry(0, 1, i64::MIN).unwrap();

        let matq_1 = MatQ::from(&matz);

        assert_eq!(Q::from(i64::MIN), matq_1.get_entry(0, 1).unwrap());
        assert_eq!(Q::from(u64::MAX - 58), matq_1.get_entry(0, 0).unwrap());
    }

    /// Ensure that the conversion works for owned values
    #[test]
    fn availability() {
        let m = MatZ::from_str("[[1, 2],[3, -1]]").unwrap();

        let _ = MatQ::from(m);
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
        let matrix_str_1 = "[[1/2, 2/3, 3/4],[4/5, 5/6, 6/7]]";

        assert_eq!(
            Q::from((1, 2)),
            MatQ::from_str(matrix_str_1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that initialization works with integers.
    #[test]
    fn init_integer_works() {
        let matrix_str_1 = "[[1, 2, 3],[3, 4, 5]]";

        assert_eq!(
            Z::ONE,
            Z {
                value: MatQ::from_str(matrix_str_1)
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
                value: MatQ::from_str(matrix_str_1)
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
        let matrix_str_1 = "[[  1/2, 2/3 ,  3/4  ],[3/4 , 4/5, 5/6 ]]";

        assert_eq!(
            Q::from((1, 2)),
            MatQ::from_str(matrix_str_1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_str_1 = "[1/2, 2, 3],[3, 4/7, 5]]";
        let matrix_str_2 = "[[1, 2/9, 3][3, 4, 5/5]]";
        let matrix_str_3 = "[[1, 2, 3/2], 3, 4, 5]";
        let matrix_str_4 = "[1, 2, 3, 4/5, 5]";
        let matrix_str_5 = "[ [1, 2/8, 3],[3, 4, 5]]";
        let matrix_str_6 = "[[1, 2, 3],[3, 4/9, 5]8]";
        let matrix_str_7 = "";
        let matrix_str_8 = "[]";
        let matrix_str_9 = "[[]]";

        assert!(MatQ::from_str(matrix_str_1).is_err());
        assert!(MatQ::from_str(matrix_str_2).is_err());
        assert!(MatQ::from_str(matrix_str_3).is_err());
        assert!(MatQ::from_str(matrix_str_4).is_err());
        assert!(MatQ::from_str(matrix_str_5).is_err());
        assert!(MatQ::from_str(matrix_str_6).is_err());
        assert!(MatQ::from_str(matrix_str_7).is_err());
        assert!(MatQ::from_str(matrix_str_8).is_err());
        assert!(MatQ::from_str(matrix_str_9).is_err());
    }
}
