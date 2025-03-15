// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatZq`] value from other types.
//!
//! The explicit functions contain the documentation.

use super::MatZq;
use crate::{
    error::{MathError, StringConversionError},
    integer::{MatZ, Z},
    integer_mod_q::Modulus,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::{
        dimensions::find_matrix_dimensions,
        index::evaluate_indices,
        parse::{matrix_from_utf8_fill_bytes, parse_matrix_string},
    },
};
use flint_sys::{fmpz_mat::fmpz_mat_set, fmpz_mod_mat::_fmpz_mod_mat_reduce};
use std::{fmt::Display, str::FromStr};

impl FromStr for MatZq {
    type Err = MathError;

    /// Creates a [`MatZq`] matrix with entries in [`Zq`](crate::integer_mod_q::Zq) from a [`String`].
    ///
    /// Parameters:
    /// - `string`: the matrix of form: `"[[1, 2, 3],[4, 5, 6]] mod 4"` for a 2x3 matrix
    ///     with entries 1, 2, 3 in the first row, 4, 5, 6 in the second row and 4 as modulus.
    ///
    /// Note that the strings for entries and the modulus are trimmed,
    /// i.e. all whitespaces around all values are ignored.
    ///
    /// Returns a [`MatZq`] or an error if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too large (must fit into [`i64`]),
    /// the number of entries in rows is unequal or if the modulus or an entry is not formatted correctly.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 4").unwrap();
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let str_1 = "[[1, 2, 3],[4, 5, 6]] mod 4";
    /// let matrix = MatZq::from_str(str_1).unwrap();
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1, 2, 3],[4, 5, 6]] mod 4");
    /// let matrix = MatZq::from_str(&string).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
    ///     - if the matrix is not formatted in a suitable way,
    ///     - if the number of rows or columns is too large (must fit into i64),
    ///     - if the number of entries in rows is unequal,
    ///     - if the delimiter `mod` could not be found, or
    ///     - if the modulus or an entry is not formatted correctly.
    ///         For further information see [`Z::from_str`].
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns or the modulus are not suited to create a matrix.
    ///     For further information see [`MatZq::new`].
    /// - if the modulus is smaller than `2`.
    fn from_str(string: &str) -> Result<Self, MathError> {
        let (matrix, modulus) = match string.split_once("mod") {
            Some((matrix, modulus)) => (matrix, modulus),
            None => {
                return Err(StringConversionError::InvalidMatrix(format!(
                    "The word 'mod' could not be found: {string}"
                )))?
            }
        };

        let modulus = Z::from_str(modulus.trim())?;

        let string_matrix = parse_matrix_string(matrix.trim())?;
        let (num_rows, num_cols) = find_matrix_dimensions(&string_matrix)?;
        let mut matrix = MatZq::new(num_rows, num_cols, modulus);

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

impl<Mod: Into<Modulus>> From<(&MatZ, Mod)> for MatZq {
    /// Creates a [`MatZq`] from a [`MatZ`] and a value that implements [`Into<Modulus>`].
    ///
    /// Parameters:
    /// - `matrix`: the matrix from which the entries are taken
    /// - `modulus`: the modulus of the matrix
    ///
    /// Returns a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let m = MatZ::from_str("[[1, 2],[3, -1]]").unwrap();
    ///
    /// let a = MatZq::from((&m, 17));
    /// ```
    fn from((matrix, modulus): (&MatZ, Mod)) -> Self {
        let mut out = MatZq::new(matrix.get_num_rows(), matrix.get_num_columns(), modulus);
        unsafe {
            fmpz_mat_set(&mut out.matrix.mat[0], &matrix.matrix);
            _fmpz_mod_mat_reduce(&mut out.matrix);
        }
        out
    }
}

impl<Mod: Into<Modulus>> From<(MatZ, Mod)> for MatZq {
    /// Creates a [`MatZq`] from a [`MatZ`] and a value that implements [`Into<Modulus>`].
    ///
    /// Parameters:
    /// - `matrix`: the matrix from which the entries are taken
    /// - `modulus`: the modulus of the matrix
    ///
    /// Returns a new [`MatZq`] matrix with entries from the [`MatZ`] instance modulo `modulus`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let m = MatZ::from_str("[[1, 2],[3, -1]]").unwrap();
    ///
    /// let a = MatZq::from((m, 17));
    /// ```
    fn from((matrix, modulus): (MatZ, Mod)) -> Self {
        MatZq::from((&matrix, modulus))
    }
}

impl From<&MatZq> for MatZq {
    /// Alias for [`MatZq::clone`].
    fn from(value: &MatZq) -> Self {
        value.clone()
    }
}

impl MatZq {
    /// Create a [`MatZq`] from a [`String`], i.e. its UTF8-Encoding.
    /// This function can only construct positive or zero integers, but not negative ones.
    /// If the number of bytes and number of entries does not line up, we pad the message
    /// with `'0'`s.
    /// The inverse of this function is [`MatZq::to_utf8`].
    ///
    /// **WARNING:** This implementation requires the `modulus` to be larger than
    /// any single entry in the matrix. This function will denote the same number of bytes
    /// to every entry and sequentially move through your `message` to encode them.
    /// If a decimal presentation of these bytes is ever larger than the specified `modulus`,
    /// the function will return an error.
    ///
    /// Parameters:
    /// - `message`: specifies the message that is transformed via its UTF8-Encoding
    ///   to a new [`MatZq`] instance.
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    /// - `modulus`: specifies the modulus of the matrix, it is required to be larger
    ///     than any entry of the matrix
    ///
    /// Returns a [`MatZq`] with corresponding entries to the message's UTF8-Encoding or
    /// a [`ConversionError`](MathError::ConversionError) if the modulus isn't larger than
    /// every single entry of the matrix after distributing the (potentially padded) UTF8-Bytes
    /// equally over the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// let message = "hello!";
    ///  
    /// let matrix = MatZq::from_utf8(&message, 3, 2, 257).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
    ///     if the modulus isn't larger than the largest entry of the matrix after equally
    ///     distributing the (potentially padded) UTF8-Conversion over the matrix.
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    ///     For further information see [`MatZq::new`].
    pub fn from_utf8(
        message: &str,
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: impl Into<Modulus>,
    ) -> Result<Self, MathError> {
        let (num_rows_i64, num_cols_i64) = evaluate_indices(num_rows, num_cols).unwrap();
        let mut mat = MatZq::new(num_rows_i64, num_cols_i64, modulus);
        let num_columns = mat.get_num_columns() as usize;
        let nr_entries = mat.get_num_rows() as usize * num_columns;
        let modulus_as_z = Z::from(mat.get_mod());

        let (byte_vector, nr_bytes_per_entry) = matrix_from_utf8_fill_bytes(message, nr_entries);

        // Fill rows going from left to right, entry by entry
        for row in 0..mat.get_num_rows() as usize {
            let offset_row = row * num_columns * nr_bytes_per_entry;
            for col in 0..num_columns {
                let entry_value = Z::from_bytes(
                    &byte_vector[offset_row + nr_bytes_per_entry * col
                        ..offset_row + nr_bytes_per_entry * (col + 1)],
                );
                if modulus_as_z > entry_value {
                    unsafe { mat.set_entry_unchecked(row as i64, col as i64, entry_value) };
                } else {
                    return Err(MathError::ConversionError(
                        "The provided modulus is smaller than the UTF8-Encoding of your message."
                            .to_owned(),
                    ));
                }
            }
        }

        Ok(mat)
    }
}

#[cfg(test)]
mod test_from_mat_z_modulus {
    use crate::{
        integer::{MatZ, Z},
        integer_mod_q::{MatZq, Modulus},
        traits::{GetEntry, GetNumColumns, GetNumRows, SetEntry},
    };

    /// Test if the dimensions are taken over correctly.
    #[test]
    fn dimensions() {
        let matz = MatZ::new(15, 17);
        let modulus = Modulus::from(17);

        let matzq_1 = MatZq::from((&matz, &modulus));

        assert_eq!(15, matzq_1.get_num_rows());
        assert_eq!(17, matzq_1.get_num_columns());
    }

    /// Test if entries are taken over correctly.
    #[test]
    fn entries_taken_over_correctly() {
        let mut matz = MatZ::new(2, 2);
        let modulus = Modulus::from(u64::MAX);

        matz.set_entry(0, 0, u64::MAX - 58).unwrap();
        matz.set_entry(0, 1, -1).unwrap();

        let matzq_1 = MatZq::from((&matz, &modulus));

        let entry_1: Z = matzq_1.get_entry(0, 1).unwrap();
        let entry_2: Z = matzq_1.get_entry(0, 0).unwrap();

        assert_eq!(u64::MAX - 1, entry_1);
        assert_eq!(u64::MAX - 58, entry_2);
    }

    /// Ensures that the function is still available for all values implementing
    /// `Into<Modulus>`.
    #[test]
    fn availability() {
        let matz = MatZ::new(2, 2);

        let _ = MatZq::from((&matz, 2u8));
        let _ = MatZq::from((&matz, 2u16));
        let _ = MatZq::from((&matz, 2u32));
        let _ = MatZq::from((&matz, 2u64));
        let _ = MatZq::from((&matz, 2i8));
        let _ = MatZq::from((&matz, 2i16));
        let _ = MatZq::from((&matz, 2i32));
        let _ = MatZq::from((&matz, 2i64));
        let _ = MatZq::from((&matz, Z::from(2)));
        let _ = MatZq::from((&matz, Modulus::from(2)));

        let _ = MatZq::from((&matz, &2u8));
        let _ = MatZq::from((&matz, &2u16));
        let _ = MatZq::from((&matz, &2u32));
        let _ = MatZq::from((&matz, &2u64));
        let _ = MatZq::from((&matz, &2i8));
        let _ = MatZq::from((&matz, &2i16));
        let _ = MatZq::from((&matz, &2i32));
        let _ = MatZq::from((&matz, &2i64));
        let _ = MatZq::from((&matz, &Z::from(2)));
        let _ = MatZq::from((&matz, &Modulus::from(2)));

        let _ = MatZq::from((matz, Modulus::from(2)));
    }
}

#[cfg(test)]
mod test_from_str {
    use crate::{integer::Z, integer_mod_q::MatZq, traits::GetEntry};
    use std::str::FromStr;

    /// Ensure that initialization works.
    #[test]
    fn init_works() {
        let matrix_str_1 = &MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 6").unwrap();

        let entry: Z = matrix_str_1.get_entry(0, 0).unwrap();

        assert_eq!(1, entry);
    }

    /// Ensure that entries are correctly reduced.
    #[test]
    fn reduce_works() {
        let matrix_str_1 = &MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 3").unwrap();

        let entry: Z = matrix_str_1.get_entry(1, 1).unwrap();

        assert_eq!(1, entry);
    }

    /// Ensure that initialization with positive numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_large_numbers() {
        let matrix_string = &MatZq::from_str(&format!(
            "[[{}, 2, 3],[3, 4, 5]] mod {}",
            u64::MAX - 1,
            u64::MAX
        ))
        .unwrap();

        let entry: Z = matrix_string.get_entry(0, 0).unwrap();

        assert_eq!(u64::MAX - 1, entry);
    }

    /// Ensure that initialization with negative numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_small_numbers() {
        let matrix_string = &MatZq::from_str(&format!(
            "[[-{}, 2, 3],[3, 4, 5]] mod {}",
            u64::MAX - 1,
            u64::MAX
        ))
        .unwrap();

        let entry: Z = matrix_string.get_entry(0, 0).unwrap();

        assert_eq!(1, entry);
    }

    /// Ensure that initialization with moduli that are larger than [`i64`] works.
    #[test]
    fn init_works_large_modulus() {
        let matrix_string =
            &MatZq::from_str(&format!("[[1, 2, 3],[3, 4, 5]] mod {}", u64::MAX)).unwrap();

        let entry: Z = matrix_string.get_entry(0, 0).unwrap();

        assert_eq!(1, entry);
    }

    /// Ensure that entries can have leading and trailing whitespaces.
    #[test]
    fn whitespaces_in_entries_works() {
        let matrix_str_1 = &MatZq::from_str("[[  1, 2 ,  3  ],[3 , 4, 5 ]]  mod  6 ").unwrap();

        let entry: Z = matrix_str_1.get_entry(0, 0).unwrap();

        assert_eq!(1, entry);
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_str_1 = "[1, 2, 3],[3, 4, 5]] mod 6";
        let matrix_str_2 = "[[1, 2, 3][3, 4, 5]] mod 6";
        let matrix_str_3 = "[[1, 2, 3], 3, 4, 5] mod 6";
        let matrix_str_4 = "[1, 2, 3, 4, 5] mod 6";
        let matrix_str_5 = "[ [1, 2, 3],[3, 4, 5]] mod 6";
        let matrix_str_6 = "[[1, 2, 3],[3, 4, 5]8] mod 6";
        let matrix_str_7 = "[[1, 2, 3],[3, 4, 5]] md 6";
        let matrix_str_8 = " mod 6";
        let matrix_str_9 = "";
        let matrix_str_10 = "[] mod 6";
        let matrix_str_11 = "[[]] mod 6";

        assert!(MatZq::from_str(matrix_str_1).is_err());
        assert!(MatZq::from_str(matrix_str_2).is_err());
        assert!(MatZq::from_str(matrix_str_3).is_err());
        assert!(MatZq::from_str(matrix_str_4).is_err());
        assert!(MatZq::from_str(matrix_str_5).is_err());
        assert!(MatZq::from_str(matrix_str_6).is_err());
        assert!(MatZq::from_str(matrix_str_7).is_err());
        assert!(MatZq::from_str(matrix_str_8).is_err());
        assert!(MatZq::from_str(matrix_str_9).is_err());
        assert!(MatZq::from_str(matrix_str_10).is_err());
        assert!(MatZq::from_str(matrix_str_11).is_err());
    }
}

#[cfg(test)]
/// Test the implementation of [`MatZq::from_utf8`] briefly.
/// This module omits tests that were already provided for [`Z::from_bytes`]
/// and [`crate::utils::parse::matrix_from_utf8_fill_bytes`].
mod test_from_utf8 {
    use super::{MatZq, Z};
    use crate::traits::GetEntry;
    use std::str::FromStr;

    /// Ensure that the empty string results in a zero value.
    #[test]
    fn empty_string() {
        let message = "";

        let matrix = MatZq::from_utf8(message, 1, 1, 5).unwrap();
        let value: Z = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::ZERO, value);
    }

    /// Ensures correct conversion of bytes and their order.
    #[test]
    fn conversion_and_order() {
        let message = "{10_chars}";
        let cmp_matrix =
            MatZq::from_str("[[12667, 24368],[26723, 29281],[32115, 12336]] mod 65536").unwrap();

        let matrix = MatZq::from_utf8(message, 3, 2, 65536).unwrap();

        assert_eq!(cmp_matrix, matrix);
    }

    /// Ensures that if the modulus was chosen too small, that the function returns an error.
    #[test]
    fn modulus_too_small() {
        let message = "1";

        let matrix = MatZq::from_utf8(message, 1, 1, 3);

        assert!(matrix.is_err());
    }
}
