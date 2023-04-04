// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatZq`](crate::integer_mod_q::MatZq) value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::MatZq;
use crate::{
    error::MathError,
    integer::Z,
    traits::SetEntry,
    utils::{
        dimensions::find_matrix_dimensions, index::evaluate_index, parse::parse_matrix_string,
    },
};
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_init;
use std::{fmt::Display, mem::MaybeUninit, str::FromStr};

impl MatZq {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns,
    /// zeros as entries and `modulus` as the modulus.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    /// - `modulus`: the common modulus of the matrix entries
    ///
    /// Returns a [`MatZq`] or an error, if the number of rows or columns is
    /// less than `1`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::new(5, 10, 7).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the number of rows or columns is `0`.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is negative or it does not fit into an [`i64`].
    /// - Returns a [`MathError`] of type [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the provided value is not greater than `0`.
    pub fn new(
        num_rows: impl TryInto<i64> + Display + Copy,
        num_cols: impl TryInto<i64> + Display + Copy,
        modulus: impl Into<Z>,
    ) -> Result<Self, MathError> {
        // TODO add separate function
        let num_rows_i64 = evaluate_index(num_rows)?;
        let num_cols_i64 = evaluate_index(num_cols)?;

        if num_rows_i64 == 0 || num_cols_i64 == 0 {
            return Err(MathError::InvalidMatrix(format!(
                "({},{})",
                num_rows, num_cols,
            )));
        }

        let modulus = std::convert::Into::<Z>::into(modulus);

        if modulus < Z::ONE {
            return Err(MathError::InvalidIntToModulus(format!("{}", modulus)));
        }

        // initialize variable with MaybeUn-initialized value to check
        // correctness of initialization later
        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_mod_mat_init(
                matrix.as_mut_ptr(),
                num_rows_i64,
                num_cols_i64,
                &modulus.value,
            );

            Ok(MatZq {
                matrix: matrix.assume_init(),
            })
        }
    }
}

impl FromStr for MatZq {
    type Err = MathError;

    /// Creates a [`MatZq`] matrix with entries in [`Zq`](crate::integer_mod_q::Zq) from a [`String`].
    /// The format of that string looks like this <br> `[[1,2,3],[4,5,6]] mod 4` for a 2x3 matrix
    /// with entries 1,2,3 in the first row, 4,5,6 in the second row and 4 as modulus.
    ///
    /// Parameters:
    /// - `string`: the matrix as a string
    ///
    /// Returns a [`MatZq`] or an error, if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too big (must fit into [`i64`]),
    /// the number of entries in rows is unequal or if the regular expression
    /// inside of the function could not be processed.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1,2,3],[4,5,6]] mod 4");
    /// let matrix = MatZq::from_str(&string).unwrap();
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
    /// if the modulus or an entry is not formatted correctly.
    /// - Returns a [`MathError`] of type
    /// [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the modulus is not greater than '0'.
    fn from_str(string: &str) -> Result<Self, MathError> {
        let (matrix, modulus) = match string.split_once("mod") {
            Some((matrix, modulus)) => (matrix, modulus),
            None => {
                return Err(MathError::InvalidStringToMatZqInput(format!(
                    "The word 'mod' could not be found: {}",
                    string.to_owned()
                )))
            }
        };

        let modulus = Z::from_str(modulus.trim())?;

        let string_matrix = parse_matrix_string(matrix.trim())?;
        let (num_rows, num_cols) = find_matrix_dimensions(&string_matrix)?;
        let mut matrix = MatZq::new(num_rows, num_cols, modulus)?;

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

#[cfg(test)]
mod test_new {
    use crate::{integer::Z, integer_mod_q::MatZq, traits::GetEntry};

    /// Ensure that initialization works.
    #[test]
    fn initialization() {
        assert!(MatZq::new(2, 2, 3).is_ok());
    }

    /// Ensure that entries of a new matrix are `0`.
    #[test]
    fn entry_zero() {
        let matrix = MatZq::new(2, 2, 3).unwrap();

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
        let matrix1 = MatZq::new(1, 0, 3);
        let matrix2 = MatZq::new(0, 1, 3);
        let matrix3 = MatZq::new(0, 0, 3);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
        assert!(matrix3.is_err());
    }

    /// Ensure that an invalid modulus yields an error.
    #[test]
    fn invalid_modulus_error() {
        assert!(MatZq::new(2, 2, -3).is_err());
        assert!(MatZq::new(2, 2, 0).is_err());
    }
}

#[cfg(test)]
mod test_from_str {
    use crate::{integer::Z, integer_mod_q::MatZq, traits::GetEntry};
    use std::str::FromStr;

    /// Ensure that initialization works.
    #[test]
    fn init_works() {
        let matrix_string1 = String::from("[[1, 2, 3],[3, 4, 5]] mod 6");

        assert_eq!(
            Z::ONE,
            MatZq::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that entries are correctly reduced.
    #[test]
    fn reduce_works() {
        let matrix_string1 = String::from("[[1, 2, 3],[3, 4, 5]] mod 3");

        assert_eq!(
            Z::ONE,
            MatZq::from_str(&matrix_string1)
                .unwrap()
                .get_entry(1, 1)
                .unwrap()
        );
    }

    /// Ensure that initialization with positive numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_large_numbers() {
        let matrix_string = format!("[[{}, 2, 3],[3, 4, 5]] mod {}", u64::MAX - 1, u64::MAX);

        assert_eq!(
            Z::from(u64::MAX - 1),
            MatZq::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that initialization with negative numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_small_numbers() {
        let matrix_string = format!("[[-{}, 2, 3],[3, 4, 5]] mod {}", u64::MAX - 1, u64::MAX);

        assert_eq!(
            Z::ONE,
            MatZq::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that initialization with moduli that are larger than [`i64`] works.
    #[test]
    fn init_works_large_modulus() {
        let matrix_string = format!("[[1, 2, 3],[3, 4, 5]] mod {}", u64::MAX);

        assert_eq!(
            Z::ONE,
            MatZq::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that entries can have leading and trailing whitespaces.
    #[test]
    fn whitespaces_in_entries_works() {
        let matrix_string1 = String::from("[[  1, 2 ,  3  ],[3 ,4,5 ]]  mod  6 ");

        assert_eq!(
            Z::ONE,
            MatZq::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_string1 = String::from("[1, 2, 3],[3, 4, 5]] mod 6");
        let matrix_string2 = String::from("[[1, 2, 3][3, 4, 5]] mod 6");
        let matrix_string3 = String::from("[[1, 2, 3],3, 4, 5] mod 6");
        let matrix_string4 = String::from("[1, 2, 3, 4, 5] mod 6");
        let matrix_string5 = String::from("[ [1, 2, 3],[3, 4, 5]] mod 6");
        let matrix_string6 = String::from("[[1, 2, 3],[3, 4, 5]8] mod 6");
        let matrix_string7 = String::from("[[1, 2, 3],[3, 4, 5]] md 6");
        let matrix_string8 = String::from(" mod 6");
        let matrix_string9 = String::from("");
        let matrix_string10 = String::from("[] mod 6");
        let matrix_string11 = String::from("[[]] mod 6");

        assert!(MatZq::from_str(&matrix_string1).is_err());
        assert!(MatZq::from_str(&matrix_string2).is_err());
        assert!(MatZq::from_str(&matrix_string3).is_err());
        assert!(MatZq::from_str(&matrix_string4).is_err());
        assert!(MatZq::from_str(&matrix_string5).is_err());
        assert!(MatZq::from_str(&matrix_string6).is_err());
        assert!(MatZq::from_str(&matrix_string7).is_err());
        assert!(MatZq::from_str(&matrix_string8).is_err());
        assert!(MatZq::from_str(&matrix_string9).is_err());
        assert!(MatZq::from_str(&matrix_string10).is_err());
        assert!(MatZq::from_str(&matrix_string11).is_err());
    }
}
