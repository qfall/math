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
    integer_mod_q::MatZq,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::{dimensions::find_matrix_dimensions, parse::parse_matrix_string},
};
use flint_sys::fmpz_mat::fmpz_mat_set;
use std::str::FromStr;

impl MatZ {
    /// Create a [`MatZ`] from a [`MatZq`].
    ///
    /// The output matrix entries values will be in the range `[0, Modulus)`.
    /// Use [`MatZq::get_closest_to_zero_representative`] if they should be
    /// close to `0`.
    ///
    /// Parameters:
    /// - `matrix`: the matrix from which the entries are taken
    ///
    /// Returns the new matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let m = MatZq::from_str("[[1, 2],[3, -1]] mod 5").unwrap();
    ///
    /// let a = MatZ::from_mat_zq(&m);
    /// ```
    pub fn from_mat_zq(matrix: &MatZq) -> Self {
        let mut out = MatZ::new(matrix.get_num_rows(), matrix.get_num_columns());
        unsafe { fmpz_mat_set(&mut out.matrix, &matrix.matrix.mat[0]) };
        out
    }
}

impl FromStr for MatZ {
    type Err = MathError;

    /// Creates a [`MatZ`] matrix with entries in [`Z`] from a [`String`].
    /// The format of that string looks like this `[[1, 2, 3],[4, 5, 6]]` for a 2x3 matrix
    /// with entries 1, 2, 3 in the first row and 4, 5, 6 in the second row.
    ///
    /// Parameters:
    /// - `string`: the matrix as a string
    ///
    /// Returns a [`MatZ`] or an error, if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too large (must fit into [`i64`]),
    /// the number of entries in rows is unequal or if the regular expression
    /// inside of the function could not be processed.
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
    ///     - if the number of entries in rows is unequal,
    ///     - if an entry is not formatted correctly.
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

impl From<&MatZq> for MatZ {
    /// Convert [`MatZq`] to [`MatZ`] using [`MatZ::from_mat_zq`].
    fn from(matrix: &MatZq) -> Self {
        Self::from_mat_zq(matrix)
    }
}

#[cfg(test)]
mod test_from_mat_zq {
    use crate::{
        integer::{MatZ, Z},
        integer_mod_q::MatZq,
        traits::{GetEntry, GetNumColumns, GetNumRows, SetEntry},
    };

    /// Test if the dimensions are taken over correctly
    #[test]
    fn dimensions() {
        let matzq = MatZq::new(15, 17, 13);

        let matz_1 = MatZ::from(&matzq);
        let matz_2 = MatZ::from_mat_zq(&matzq);

        assert_eq!(15, matz_1.get_num_rows());
        assert_eq!(17, matz_1.get_num_columns());
        assert_eq!(15, matz_2.get_num_rows());
        assert_eq!(17, matz_2.get_num_columns());
    }

    /// Test if entries are taken over correctly
    #[test]
    fn entries_taken_over_correctly() {
        let mut matzq = MatZq::new(2, 2, u64::MAX);
        matzq.set_entry(0, 0, u64::MAX - 58).unwrap();
        matzq.set_entry(0, 1, -1).unwrap();

        let matz_1 = MatZ::from(&matzq);
        let matz_2 = MatZ::from_mat_zq(&matzq);

        assert_eq!(Z::from(u64::MAX - 1), matz_1.get_entry(0, 1).unwrap());
        assert_eq!(Z::from(u64::MAX - 58), matz_1.get_entry(0, 0).unwrap());
        assert_eq!(Z::from(u64::MAX - 1), matz_2.get_entry(0, 1).unwrap());
        assert_eq!(Z::from(u64::MAX - 58), matz_2.get_entry(0, 0).unwrap());
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
