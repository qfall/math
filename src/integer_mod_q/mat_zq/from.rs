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
    integer::{MatZ, Z},
    integer_mod_q::Modulus,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::{dimensions::find_matrix_dimensions, parse::parse_matrix_string},
};
use flint_sys::{fmpz_mat::fmpz_mat_set, fmpz_mod_mat::_fmpz_mod_mat_reduce};
use std::str::FromStr;

impl MatZq {
    /// Create a [`MatZq`] from a [`MatZ`] and a [`Modulus`].
    ///
    /// Parameters:
    /// - `matrix`: the matrix from which the entries are taken
    /// - `modulus`: the modulus of the matrix
    ///
    /// Returns the new matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let m = MatZ::from_str("[[1, 2],[3, -1]]").unwrap();
    /// let modulus = Modulus::from(17);
    ///
    /// let a = MatZq::from_mat_z_modulus(&m, &modulus);
    /// ```
    pub fn from_mat_z_modulus(matrix: &MatZ, modulus: &Modulus) -> Self {
        let mut out = MatZq::new(matrix.get_num_rows(), matrix.get_num_columns(), modulus).unwrap();
        unsafe {
            fmpz_mat_set(&mut out.matrix.mat[0], &matrix.matrix);
            _fmpz_mod_mat_reduce(&mut out.matrix);
        }
        out
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
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1,2,3],[4,5,6]] mod 4").unwrap();
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let str1 = "[[1,2,3],[4,5,6]] mod 4";
    /// let matrix = MatZq::from_str(str1).unwrap();
    /// ```
    ///
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
    /// if the modulus is not greater than `1`.
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

impl From<(&MatZ, &Modulus)> for MatZq {
    /// Convert [`MatZ`] and [`Modulus`] to [`MatZq`] using [`MatZq::from_mat_z_modulus`].
    fn from((matrix, modulus): (&MatZ, &Modulus)) -> Self {
        MatZq::from_mat_z_modulus(matrix, modulus)
    }
}

#[cfg(test)]
mod test_from_mat_z_modulus {
    use crate::{
        integer::{MatZ, Z},
        integer_mod_q::{MatZq, Modulus},
        traits::{GetEntry, GetNumColumns, GetNumRows, SetEntry},
    };

    /// test if the dimensions are taken over correctly
    #[test]
    fn dimensions() {
        let matz = MatZ::new(15, 17).unwrap();
        let modulus = Modulus::from(17);

        let matzq_1 = MatZq::from((&matz, &modulus));
        let matzq_2 = MatZq::from_mat_z_modulus(&matz, &modulus);

        assert_eq!(15, matzq_1.get_num_rows());
        assert_eq!(17, matzq_1.get_num_columns());
        assert_eq!(15, matzq_2.get_num_rows());
        assert_eq!(17, matzq_2.get_num_columns());
    }

    /// test if entries are taken over correctly
    #[test]
    fn entries_taken_over_correctly() {
        let mut matz = MatZ::new(2, 2).unwrap();
        let modulus = Modulus::from(u64::MAX);

        matz.set_entry(0, 0, u64::MAX - 58).unwrap();
        matz.set_entry(0, 1, -1).unwrap();

        let matzq_1 = MatZq::from((&matz, &modulus));
        let matzq_2 = MatZq::from_mat_z_modulus(&matz, &modulus);

        assert_eq!(Z::from(u64::MAX - 1), matzq_1.get_entry(0, 1).unwrap());
        assert_eq!(Z::from(u64::MAX - 58), matzq_1.get_entry(0, 0).unwrap());
        assert_eq!(Z::from(u64::MAX - 1), matzq_2.get_entry(0, 1).unwrap());
        assert_eq!(Z::from(u64::MAX - 58), matzq_2.get_entry(0, 0).unwrap());
    }
}

#[cfg(test)]
mod test_from_str {
    use crate::{integer::Z, integer_mod_q::MatZq, traits::GetEntry};
    use std::str::FromStr;

    /// Ensure that initialization works.
    #[test]
    fn init_works() {
        let matrix_str1 = "[[1, 2, 3],[3, 4, 5]] mod 6";

        assert_eq!(
            Z::ONE,
            MatZq::from_str(matrix_str1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that entries are correctly reduced.
    #[test]
    fn reduce_works() {
        let matrix_str1 = "[[1, 2, 3],[3, 4, 5]] mod 3";

        assert_eq!(
            Z::ONE,
            MatZq::from_str(matrix_str1)
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
        let matrix_str1 = "[[  1, 2 ,  3  ],[3 ,4,5 ]]  mod  6 ";

        assert_eq!(
            Z::ONE,
            MatZq::from_str(matrix_str1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_str1 = "[1, 2, 3],[3, 4, 5]] mod 6";
        let matrix_str2 = "[[1, 2, 3][3, 4, 5]] mod 6";
        let matrix_str3 = "[[1, 2, 3],3, 4, 5] mod 6";
        let matrix_str4 = "[1, 2, 3, 4, 5] mod 6";
        let matrix_str5 = "[ [1, 2, 3],[3, 4, 5]] mod 6";
        let matrix_str6 = "[[1, 2, 3],[3, 4, 5]8] mod 6";
        let matrix_str7 = "[[1, 2, 3],[3, 4, 5]] md 6";
        let matrix_str8 = " mod 6";
        let matrix_str9 = "";
        let matrix_str10 = "[] mod 6";
        let matrix_str11 = "[[]] mod 6";

        assert!(MatZq::from_str(matrix_str1).is_err());
        assert!(MatZq::from_str(matrix_str2).is_err());
        assert!(MatZq::from_str(matrix_str3).is_err());
        assert!(MatZq::from_str(matrix_str4).is_err());
        assert!(MatZq::from_str(matrix_str5).is_err());
        assert!(MatZq::from_str(matrix_str6).is_err());
        assert!(MatZq::from_str(matrix_str7).is_err());
        assert!(MatZq::from_str(matrix_str8).is_err());
        assert!(MatZq::from_str(matrix_str9).is_err());
        assert!(MatZq::from_str(matrix_str10).is_err());
        assert!(MatZq::from_str(matrix_str11).is_err());
    }
}
