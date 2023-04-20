// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatZ`](crate::integer::MatZ) matrix from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::MatZ;
use crate::{
    error::MathError,
    integer::Z,
    integer_mod_q::MatZq,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::{
        dimensions::find_matrix_dimensions, index::evaluate_index, parse::parse_matrix_string,
    },
};
use flint_sys::fmpz_mat::{
    fmpz_mat_one, {fmpz_mat_init, fmpz_mat_set},
};
use std::{fmt::Display, mem::MaybeUninit, str::FromStr};

impl MatZ {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns and
    /// zeros as entries.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    ///
    /// Returns a [`MatZ`] or an error, if the number of rows or columns is
    /// less or equal to `0`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let matrix = MatZ::new(5, 10).unwrap();
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
        let num_rows_i64 = evaluate_index(num_rows)?;
        let num_cols_i64 = evaluate_index(num_cols)?;

        if num_rows_i64 == 0 || num_cols_i64 == 0 {
            return Err(MathError::InvalidMatrix(
                "A matrix can not contain 0 rows or 0 columns".to_string(),
            ));
        }

        // initialize variable with MaybeUn-initialized value to check
        // correctness of initialization later
        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_mat_init(matrix.as_mut_ptr(), num_rows_i64, num_cols_i64);

            // Construct MatZ from previously initialized fmpz_mat
            Ok(MatZ {
                matrix: matrix.assume_init(),
            })
        }
    }

    /// Create a [`MatZ`] from a [`MatZq`].
    ///
    /// Parameters:
    /// - `matrix`: the matrix from which the entries are taken
    ///
    /// Returns the new matrix.
    ///
    /// # Example
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
        let mut out = MatZ::new(matrix.get_num_rows(), matrix.get_num_columns()).unwrap();
        unsafe { fmpz_mat_set(&mut out.matrix, &matrix.matrix.mat[0]) };
        out
    }

    /// Generate a `num_rows` times `num_columns` matrix with `1` on the
    /// diagonal and `0` anywhere else.
    ///
    /// Parameters:
    /// - `rum_rows`: the number of rows of the identity matrix
    /// - `num_columns`: the number of columns of the identity matrix
    ///
    /// Returns a matrix with `1` across the diagonal and `0` anywhere else.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let matrix = MatZ::identity(2, 3).unwrap();
    ///
    /// let identity = MatZ::identity(10, 10).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix) or
    /// [`OutOfBounds`](MathError::OutOfBounds) if the provided number of rows and columns
    /// are not suited to create a matrix. For further information see [`MatZ::new`].
    pub fn identity(
        num_rows: impl TryInto<i64> + Display + Copy,
        num_cols: impl TryInto<i64> + Display + Copy,
    ) -> Result<Self, MathError> {
        let mut out = MatZ::new(num_rows, num_cols)?;
        unsafe { fmpz_mat_one(&mut out.matrix) };
        Ok(out)
    }
}

impl FromStr for MatZ {
    type Err = MathError;

    /// Creates a [`MatZ`] matrix with entries in [`Z`] from a [`String`].
    /// The format of that string looks like this `[[1,2,3],[4,5,6]]` for a 2x3 matrix
    /// with entries 1, 2, 3 in the first row and 4, 5, 6 in the second row.
    ///
    /// Parameters:
    /// - `string`: the matrix as a string
    ///
    /// Returns a [`MatZ`] or an error, if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too big (must fit into [`i64`]),
    /// the number of entries in rows is unequal or if the regular expression
    /// inside of the function could not be processed.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1, 2, 3],[3, 4, 5]]");
    /// let matrix = MatZ::from_str(&string).unwrap();
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
        let mut matrix = MatZ::new(num_rows, num_cols)?;

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
mod test_new {
    use crate::{
        integer::{MatZ, Z},
        traits::GetEntry,
    };

    /// Ensure that entries of a new matrix are `0`.
    #[test]
    fn entry_zero() {
        let matrix = MatZ::new(2, 2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(0, 1).unwrap();
        let entry3 = matrix.get_entry(1, 0).unwrap();
        let entry4 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::ZERO, entry1);
        assert_eq!(Z::ZERO, entry2);
        assert_eq!(Z::ZERO, entry3);
        assert_eq!(Z::ZERO, entry4);
    }

    /// Ensure that a new zero matrix fails with `0` as input.
    #[test]
    fn error_zero() {
        let matrix1 = MatZ::new(1, 0);
        let matrix2 = MatZ::new(0, 1);
        let matrix3 = MatZ::new(0, 0);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
        assert!(matrix3.is_err());
    }
}

#[cfg(test)]
mod test_from_mat_zq {
    use crate::{
        integer::{MatZ, Z},
        integer_mod_q::MatZq,
        traits::{GetEntry, GetNumColumns, GetNumRows, SetEntry},
    };

    /// test if the dimensions are taken over correctly
    #[test]
    fn dimensions() {
        let matzq = MatZq::new(15, 17, 13).unwrap();

        let matz_1 = MatZ::from(&matzq);
        let matz_2 = MatZ::from_mat_zq(&matzq);

        assert_eq!(15, matz_1.get_num_rows());
        assert_eq!(17, matz_1.get_num_columns());
        assert_eq!(15, matz_2.get_num_rows());
        assert_eq!(17, matz_2.get_num_columns());
    }

    /// test if entries are taken over correctly
    #[test]
    fn entries_taken_over_correctly() {
        let mut matzq = MatZq::new(2, 2, u64::MAX).unwrap();
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
mod test_set_one {
    use crate::{
        integer::{MatZ, Z},
        traits::GetEntry,
    };

    /// Tests if an identity matrix is set from a zero matrix.
    #[test]
    fn identity() {
        let matrix = MatZ::identity(10, 10).unwrap();

        for i in 0..10 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }
    }

    /// Tests if function works for a non-square matrix
    #[test]
    fn non_square_works() {
        let matrix = MatZ::identity(10, 7).unwrap();

        for i in 0..10 {
            for j in 0..7 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }

        let matrix = MatZ::identity(7, 10).unwrap();

        for i in 0..7 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }
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
        let matrix_string1 = String::from("[[1, 2, 3],[3, 4, 5]]");

        assert_eq!(
            Z::ONE,
            MatZ::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
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
        let matrix_string1 = String::from("[[  1, 2 ,  3  ],[3 ,4,5 ]]");

        assert_eq!(
            Z::ONE,
            MatZ::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_string1 = String::from("[1, 2, 3],[3, 4, 5]]");
        let matrix_string2 = String::from("[[1, 2, 3][3, 4, 5]]");
        let matrix_string3 = String::from("[[1, 2, 3],3, 4, 5]");
        let matrix_string4 = String::from("[1, 2, 3, 4, 5]");
        let matrix_string5 = String::from("[ [1, 2, 3],[3, 4, 5]]");
        let matrix_string6 = String::from("[[1, 2, 3],[3, 4, 5]8]");
        let matrix_string7 = String::from("");
        let matrix_string8 = String::from("[]");
        let matrix_string9 = String::from("[[]]");

        assert!(MatZ::from_str(&matrix_string1).is_err());
        assert!(MatZ::from_str(&matrix_string2).is_err());
        assert!(MatZ::from_str(&matrix_string3).is_err());
        assert!(MatZ::from_str(&matrix_string4).is_err());
        assert!(MatZ::from_str(&matrix_string5).is_err());
        assert!(MatZ::from_str(&matrix_string6).is_err());
        assert!(MatZ::from_str(&matrix_string7).is_err());
        assert!(MatZ::from_str(&matrix_string8).is_err());
        assert!(MatZ::from_str(&matrix_string9).is_err());
    }
}
