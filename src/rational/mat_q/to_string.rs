// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a matrix of type
//! [`MatQ`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::MatQ;
use crate::{
    macros::for_others::implement_for_owned,
    traits::{GetEntry, GetNumColumns, GetNumRows},
    utils::parse::matrix_to_string,
};
use core::fmt;

impl From<&MatQ> for String {
    /// Converts a [`MatQ`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[[row_0],[row_1],...[row_n]]"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    /// let matrix = MatQ::from_str("[[6/7, 1],[5, 2/3]]").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &MatQ) -> Self {
        value.to_string()
    }
}

implement_for_owned!(MatQ, String, From);

impl fmt::Display for MatQ {
    /// Allows to convert a matrix of type [`MatQ`] into a [`String`].
    ///
    /// Returns the Matrix in form of a [`String`]. For matrix `[[1/2, 2, 3/4],[4, 5/3, 6/2]]`
    /// the String looks like this `[[1/2, 2, 3/4],[4, 5/3, 3]]`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[1/2, 2, 3/4],[4, 5/3, 6]]").unwrap();
    /// println!("{matrix}");
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[1/2, 2, 3/4],[4, 5/3, 6]]").unwrap();
    /// let matrix_string = matrix.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", matrix_to_string(self))
    }
}

impl MatQ {
    /// Outputs a representation of [`MatQ`] with the decimal representation of each entry
    /// with the specified number of decimal digits.
    /// If an entry can't be represented exactly, it provides the
    /// closest value representable with `nr_decimal_digits` rounded towards zero.
    ///
    /// **WARNING:** This function converts every entry into an [`f64`] before
    /// outputting the decimal representation. Thus, values that can't be represented exactly
    /// by a [`f64`] will lose some precision. For large values, e.g. of size `2^64`
    /// the deviation to the original value might be within the size of `1_000`.
    ///
    /// Parameters:
    /// - `nr_decimal_digits`: specifies the number of decimal digits
    ///     that will be a part of the output [`String`]
    ///
    /// Returns the matrix in form of a [`String`]. For matrix `[[1/2],[5/3]]`
    /// the [`String`] looks like this `[[0.50],[1.66]]` if `nr_decimal_digits = 2`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    /// let matrix = MatQ::from_str("[[5/2, 2],[-2/3, 4/3]]").unwrap();
    ///
    /// let decimal_repr = matrix.to_string_decimal(3);
    /// ```
    ///
    /// # Panics ...
    /// - if any entry of the matrix can't be represented as an [`f64`].
    pub fn to_string_decimal(&self, nr_decimal_digits: usize) -> String {
        let mut matrix_string = String::from("[");
        let nr_rows = self.get_num_rows() - 1;
        let nr_cols = self.get_num_columns() - 1;

        for row in 0..nr_rows {
            matrix_string.push('[');
            for column in 0..nr_cols {
                self.get_entry_and_push_str(&mut matrix_string, row, column, nr_decimal_digits);
                matrix_string.push_str(", ");
            }
            self.get_entry_and_push_str(&mut matrix_string, row, nr_cols, nr_decimal_digits);
            matrix_string.push_str("],\n");
        }
        matrix_string.push('[');
        for column in 0..nr_cols {
            self.get_entry_and_push_str(&mut matrix_string, nr_rows, column, nr_decimal_digits);
            matrix_string.push_str(", ");
        }
        self.get_entry_and_push_str(&mut matrix_string, nr_rows, nr_cols, nr_decimal_digits);
        matrix_string.push_str("]]");

        matrix_string
    }

    /// Helper function to assemble a [`String`] for a matrix easily.
    ///
    /// Parameters:
    /// - `matrix_string`: [`String`] to append the decimal representation of the matrices entry
    /// - `row`: specifies the row, in which the desired entry is located
    /// - `column`: specifies the column, in which the desired entry is located
    /// - `nr_decimal_digits`: specifies how many digits the decimal representation of the entry should have
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    /// let matrix = MatQ::from_str("[[5/2, 2],[-2/3, 4/3]]").unwrap();
    /// let mut matrix_string = String::from("[[");
    ///
    /// matrix.get_entry_and_push_str(&mut matrix_string, 0, 0, 2);
    ///
    /// assert_eq!("[[2.50", matrix_string);
    /// ```
    fn get_entry_and_push_str(
        &self,
        matrix_string: &mut String,
        row: i64,
        column: i64,
        nr_decimal_digits: usize,
    ) {
        // exchange with `get_entry_unchecked` once changes are on dev
        let entry = self.get_entry(row, column).unwrap();
        let entry_string = entry.to_string_decimal(nr_decimal_digits);
        matrix_string.push_str(&entry_string);
    }
}

/// This module avoids tests already performed for [`crate::rational::Q::to_string_decimal`].
#[cfg(test)]
mod test_to_string_decimal {
    use super::MatQ;
    use std::str::FromStr;

    /// Ensures that [`MatQ::to_string_decimal`] works for matrices of different dimensions.
    #[test]
    fn dimensions() {
        let a = MatQ::from_str("[[3/2, 1/2],[-1, -7/3]]").unwrap();
        let b = MatQ::from_str("[[3/2],[-7/3]]").unwrap();
        let c = MatQ::from_str("[[3/2, 1/2, -7/3]]").unwrap();

        let a_0 = a.to_string_decimal(0);
        let a_1 = a.to_string_decimal(1);
        let b_0 = b.to_string_decimal(0);
        let b_2 = b.to_string_decimal(2);
        let c_0 = c.to_string_decimal(0);
        let c_1 = c.to_string_decimal(1);

        assert_eq!("[[1, 0],\n[-1, -2]]", a_0);
        assert_eq!("[[1.5, 0.5],\n[-1.0, -2.3]]", a_1);
        assert_eq!("[[1],\n[-2]]", b_0);
        assert_eq!("[[1.50],\n[-2.33]]", b_2);
        assert_eq!("[[1, 0, -2]]", c_0);
        assert_eq!("[[1.5, 0.5, -2.3]]", c_1);
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::rational::MatQ;
    use std::str::FromStr;

    /// Tests whether a matrix with large nominators and denominators works in a
    /// roundtrip
    #[test]
    fn working_large_positive() {
        let cmp =
            MatQ::from_str(&format!("[[{}, 1/{}, 3],[5, 6, 7]]", u64::MAX, u64::MAX)).unwrap();

        assert_eq!(
            format!("[[{}, 1/{}, 3],[5, 6, 7]]", u64::MAX, u64::MAX),
            cmp.to_string()
        )
    }

    /// Tests whether a matrix with large negative nominators and denominators
    /// works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp =
            MatQ::from_str(&format!("[[-{}, 1/-{}, 3],[5, 6, 7]]", u64::MAX, u64::MAX)).unwrap();

        assert_eq!(
            format!("[[-{}, -1/{}, 3],[5, 6, 7]]", u64::MAX, u64::MAX),
            cmp.to_string()
        )
    }

    /// Tests whether a matrix with positive nominators and denominators works
    /// in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = MatQ::from_str("[[2, 1, 2/3],[5, 6, 14/7]]").unwrap();

        assert_eq!("[[2, 1, 2/3],[5, 6, 2]]", cmp.to_string());
    }

    /// Tests whether a matrix with negative nominators and denominators works
    /// in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = MatQ::from_str("[[-2, 1, -3/8],[5, 1/-6, -14/7]]").unwrap();

        assert_eq!("[[-2, 1, -3/8],[5, -1/6, -2]]", cmp.to_string());
    }

    /// Tests whether a large matrix works in a roundtrip
    #[test]
    fn working_large_dimensions() {
        let cmp_1 = MatQ::from_str(&format!("[{}[5, 6, 7]]", "[1/2, 2, 3/8],".repeat(99))).unwrap();
        let cmp_2 = MatQ::from_str(&format!("[[{}1]]", "1/4, ".repeat(99))).unwrap();

        assert_eq!(
            format!("[{}[5, 6, 7]]", "[1/2, 2, 3/8],".repeat(99)),
            cmp_1.to_string()
        );
        assert_eq!(format!("[[{}1]]", "1/4, ".repeat(99)), cmp_2.to_string());
    }

    /// Tests whether a matrix that is created using a string, returns a
    /// string that can be used to create a [`MatQ`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = MatQ::from_str("[[-2/5, 1, 3],[5, 1/-6, 14/7]]").unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(MatQ::from_str(&cmp_str_2).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "[[6/7, 1, 3],[5, 2/3, 7]]";
        let matrix = MatQ::from_str(cmp).unwrap();

        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}
