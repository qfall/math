// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a matrix of type
//! [`MatZ`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::MatZ;
use crate::{
    macros::for_others::implement_for_owned,
    traits::{GetEntry, GetNumColumns, GetNumRows},
    utils::parse::matrix_to_string,
};
use core::fmt;
use std::string::FromUtf8Error;

impl From<&MatZ> for String {
    /// Converts a [`MatZ`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[[row_0],[row_1],...[row_n]]"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    /// let matrix = MatZ::from_str("[[6, 1],[5, 2]]").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &MatZ) -> Self {
        value.to_string()
    }
}

implement_for_owned!(MatZ, String, From);

impl fmt::Display for MatZ {
    /// Allows to convert a matrix of type [`MatZ`] into a [`String`].
    ///
    /// Returns the Matrix in form of a [`String`]. For matrix `[[1, 2, 3],[4, 5, 6]]`
    /// the String looks like this `[[1, 2, 3],[4, 5, 6]]`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZ::from_str("[[1, 2, 3],[4, 5, 6]]").unwrap();
    /// println!("{matrix}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZ::from_str("[[1, 2, 3],[4, 5, 6]]").unwrap();
    /// let matrix_string = matrix.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", matrix_to_string(self))
    }
}

impl MatZ {
    /// Enables conversion to a UTF8-Encoded [`String`] for [`MatZ`] values.
    /// The inverse to this function is [`MatZ::from_utf8`] for valid UTF8-Encodings.
    ///
    /// **Warning**: Not every byte-sequence forms a valid UTF8-Encoding.
    /// In these cases, an error is returned. Please check the format of your message again.
    /// The matrix entries are evaluated row by row, i.e. in the order of the output of [`MatZ::to_string`].
    ///
    /// Returns the corresponding UTF8-encoded [`String`] or a
    /// [`FromUtf8Error`] if the byte sequence contains an invalid UTF8-character.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    /// let matrix = MatZ::from_str("[[104, 101, 108],[108, 111, 33]]").unwrap();
    ///
    /// let message = matrix.to_utf8().unwrap();
    ///
    /// assert_eq!("hello!", message);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`FromUtf8Error`] if the integer's byte sequence contains
    ///     invalid UTF8-characters.
    pub fn to_utf8(&self) -> Result<String, FromUtf8Error> {
        let mut byte_vector: Vec<u8> = vec![];

        // Fill byte vector
        for row in 0..self.get_num_rows() as usize {
            for col in 0..self.get_num_columns() as usize {
                let entry_value = self.get_entry(row, col).unwrap();
                let mut entry_bytes = entry_value.to_bytes();
                byte_vector.append(&mut entry_bytes);
            }
        }

        String::from_utf8(byte_vector)
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Tests whether a matrix with a large entry works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = MatZ::from_str(&format!("[[{}, 1, 3],[5, 6, 7]]", u64::MAX)).unwrap();

        assert_eq!(format!("[[{}, 1, 3],[5, 6, 7]]", u64::MAX), cmp.to_string());
    }

    /// Tests whether a matrix with a large negative entry works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = MatZ::from_str(&format!("[[-{}, 1, 3],[5, 6, 7]]", u64::MAX)).unwrap();

        assert_eq!(
            format!("[[-{}, 1, 3],[5, 6, 7]]", u64::MAX),
            cmp.to_string()
        )
    }

    /// Tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = MatZ::from_str("[[2, 1, 3],[5, 6, 7]]").unwrap();

        assert_eq!("[[2, 1, 3],[5, 6, 7]]", cmp.to_string());
    }

    /// Tests whether a matrix with negative entries works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = MatZ::from_str("[[-2, 1, 3],[5, -6, 7]]").unwrap();

        assert_eq!("[[-2, 1, 3],[5, -6, 7]]", cmp.to_string());
    }

    /// Tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_large_dimensions() {
        let cmp_1 = MatZ::from_str(&format!("[{}[5, 6, 7]]", "[1, 2, 3],".repeat(99))).unwrap();
        let cmp_2 = MatZ::from_str(&format!("[[{}1]]", "1, ".repeat(99))).unwrap();

        assert_eq!(
            format!("[{}[5, 6, 7]]", "[1, 2, 3],".repeat(99)),
            cmp_1.to_string()
        );
        assert_eq!(format!("[[{}1]]", "1, ".repeat(99)), cmp_2.to_string());
    }

    /// Tests whether a matrix that is created using a string, returns a
    /// string that can be used to create a [`MatZ`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = MatZ::from_str("[[-2, 1, 3],[5, -6, 7]]").unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(MatZ::from_str(&cmp_str_2).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "[[6, 1, 3],[5, 2, 7]]";
        let matrix = MatZ::from_str(cmp).unwrap();

        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}

#[cfg(test)]
mod test_to_utf8 {
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensures that [`MatZ::to_utf8`] is inverse to [`MatZ::from_utf8`].
    #[test]
    fn inverse_to_from_utf8() {
        let message = "some_random_string_1-9A-Z!?-_;:#";

        let matrix = MatZ::from_utf8(message, 4, 4);

        let string = matrix.to_utf8().unwrap();

        assert_eq!(message, string);
    }

    /// Ensures that [`MatZ::to_utf8`] is inverse to [`MatZ::from_utf8`]
    /// and padding is applied if necessary.
    #[test]
    fn inverse_incl_padding() {
        let message = "some_random_string_1-9A-Z!?-_;";
        let cmp_text = "some_random_string_1-9A-Z!?-_;00";

        let matrix = MatZ::from_utf8(message, 4, 8);

        let string = matrix.to_utf8().unwrap();

        assert_eq!(cmp_text, string);
    }

    /// Ensures that [`MatZ::to_utf8`] outputs an error
    /// if the integer contains an invalid UTF8-Encoding.
    #[test]
    fn invalid_encoding() {
        // 128 is an invalid UTF8-character (at least at the end and on its own)
        let matrix = MatZ::from_str("[[1,2],[3,128]]").unwrap();
        let string = matrix.to_utf8();

        assert!(string.is_err());
    }
}
