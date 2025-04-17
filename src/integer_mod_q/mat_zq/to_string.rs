// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a matrix of type
//! [`MatZq`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::MatZq;
use crate::{
    integer::Z,
    macros::for_others::implement_for_owned,
    traits::{MatrixDimensions, MatrixGetEntry},
    utils::parse::matrix_to_string,
};
use core::fmt;
use std::string::FromUtf8Error;

impl From<&MatZq> for String {
    /// Converts a [`MatZq`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[[row_0],[row_1],...[row_n]] mod q"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    /// let matrix = MatZq::from_str("[[6, 1],[5, 2]] mod 4").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &MatZq) -> Self {
        value.to_string()
    }
}

implement_for_owned!(MatZq, String, From);

impl fmt::Display for MatZq {
    /// Allows to convert a matrix of type [`MatZq`] into a [`String`].
    ///
    /// Returns the Matrix in form of a [`String`]. For matrix `[[1, 2, 3],[4, 5, 6]] mod 4`
    /// the String looks like this `[[1, 2, 3],[0, 1, 2]] mod 4`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 4").unwrap();
    /// println!("{matrix}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use core::fmt;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 4").unwrap();
    /// let matrix_string = matrix.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let matrix = matrix_to_string::<Z, MatZq>(self);
        write!(f, "{matrix} mod {}", self.get_mod())
    }
}

impl MatZq {
    /// Enables conversion to a UTF8-Encoded [`String`] for [`MatZq`] values.
    /// Every entry is padded with `00`s s.t. all entries contain the same number of bytes.
    /// Afterwards, they are appended row-by-row and converted.
    /// The inverse to this function is [`MatZq::from_utf8`] for valid UTF8-Encodings.
    ///
    /// **Warning**: Not every byte-sequence forms a valid UTF8-Encoding.
    /// In these cases, an error is returned. Please check the format of your message again.
    /// The matrix entries are evaluated row by row, i.e. in the order of the output of `mat_zq.to_string()`.
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
    ///   invalid UTF8-characters.
    pub fn to_utf8(&self) -> Result<String, FromUtf8Error> {
        let mut byte_vectors: Vec<Vec<u8>> = vec![];
        let mut max_length = 0;

        // Fill byte vector
        for row in 0..self.get_num_rows() as usize {
            for col in 0..self.get_num_columns() as usize {
                let entry_value: Z = unsafe { self.get_entry_unchecked(row as i64, col as i64) };
                let entry_bytes = entry_value.to_bytes();

                // Find maximum length of bytes in one entry of the matrix
                if max_length < entry_bytes.len() {
                    max_length = entry_bytes.len();
                }

                byte_vectors.push(entry_bytes);
            }
        }

        // Pad every entry to the same length with `0`s
        // to ensure any matrix given a string provides the same matrix
        // and append them in the same iteration
        let mut bytes = vec![];
        for mut byte_vector in byte_vectors {
            // 0 encodes a control character �, which can be followed by anything
            // Hence, this might change the encoding of any trailing sequences
            byte_vector.resize(max_length, 0u8);

            bytes.append(&mut byte_vector);
        }

        String::from_utf8(bytes)
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Tests whether a matrix with a large entry works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = MatZq::from_str(&format!(
            "[[{}, 1, 3],[5, 6, 7]] mod {}",
            u64::MAX - 1,
            u64::MAX
        ))
        .unwrap();

        assert_eq!(
            format!("[[{}, 1, 3],[5, 6, 7]] mod {}", u64::MAX - 1, u64::MAX),
            cmp.to_string()
        )
    }

    /// Tests whether a matrix with a large negative entry works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = MatZq::from_str(&format!(
            "[[-{}, 1, 3],[5, 6, 7]] mod {}",
            u64::MAX - 1,
            u64::MAX
        ))
        .unwrap();

        assert_eq!(
            format!("[[1, 1, 3],[5, 6, 7]] mod {}", u64::MAX),
            cmp.to_string()
        )
    }

    /// Tests whether a matrix with positive entries works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = MatZq::from_str("[[2, 1, 3],[5, 6, 7]] mod 4").unwrap();

        assert_eq!("[[2, 1, 3],[1, 2, 3]] mod 4", cmp.to_string());
    }

    /// Tests whether a matrix with negative entries works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = MatZq::from_str("[[-2, 1, 3],[5, -6, 7]] mod 4").unwrap();

        assert_eq!("[[2, 1, 3],[1, 2, 3]] mod 4", cmp.to_string());
    }

    /// Tests whether a matrix with a large modulus works in a roundtrip
    #[test]
    fn working_large_modulus() {
        let cmp = MatZq::from_str(&format!("[[1, 1, 3],[5, 6, 7]] mod {}", u64::MAX)).unwrap();

        assert_eq!(
            format!("[[1, 1, 3],[5, 6, 7]] mod {}", u64::MAX),
            cmp.to_string()
        )
    }

    /// Tests whether a large matrix works in a roundtrip
    #[test]
    fn working_large_dimensions() {
        let cmp_1 =
            MatZq::from_str(&format!("[{}[5, 6, 7]] mod 4", "[1, 2, 3],".repeat(99))).unwrap();
        let cmp_2 = MatZq::from_str(&format!("[[{}1]] mod 4", "1, ".repeat(99))).unwrap();

        assert_eq!(
            format!("[{}[1, 2, 3]] mod 4", "[1, 2, 3],".repeat(99)),
            cmp_1.to_string()
        );
        assert_eq!(
            format!("[[{}1]] mod 4", "1, ".repeat(99)),
            cmp_2.to_string()
        );
    }

    /// Tests whether a matrix that is created using a string, returns a
    /// string that can be used to create a [`MatZq`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = MatZq::from_str("[[-2, 1, 3],[5, -6, 7]] mod 4").unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(MatZq::from_str(&cmp_str_2).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "[[6, 1, 3],[5, 2, 7]] mod 8";
        let matrix = MatZq::from_str(cmp).unwrap();

        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}

#[cfg(test)]
mod test_to_utf8 {
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Ensures that [`MatZq::to_utf8`] is inverse to [`MatZq::from_utf8`].
    #[test]
    fn inverse_of_from_utf8() {
        let message = "some_random_string_1-9A-Z!?-_;:#";

        let matrix = MatZq::from_utf8(message, 8, 4, 256).unwrap();

        let string = matrix.to_utf8().unwrap();

        assert_eq!(message, string);
    }

    /// Ensures that [`MatZq::from_utf8`] is inverse to [`MatZq::to_utf8`].
    #[test]
    fn inverse_to_from_utf8() {
        let matrix_cmp_w_padding =
            MatZq::from_str("[[104, 101, 108],[28524, 48, 48]] mod 256").unwrap();
        let matrix_cmp_wo_padding =
            MatZq::from_str("[[104, 101],[108, 108],[111, 33]] mod 256").unwrap();

        let string_w_padding = matrix_cmp_w_padding.to_utf8().unwrap();
        let string_wo_padding = matrix_cmp_wo_padding.to_utf8().unwrap();

        let matrix_w_padding = MatZq::from_utf8(&string_w_padding, 2, 3, 256).unwrap();
        let matrix_wo_padding = MatZq::from_utf8(&string_wo_padding, 3, 2, 256).unwrap();

        assert_eq!(matrix_cmp_w_padding, matrix_w_padding);
        assert_eq!(matrix_cmp_wo_padding, matrix_wo_padding);
    }

    /// Ensures that [`MatZq::to_utf8`] is inverse to [`MatZq::from_utf8`]
    /// and padding is applied if necessary.
    #[test]
    fn inverse_incl_padding() {
        let message = "some_random_string_1-9A-Z!?-_;";
        let cmp_text = "some_random_string_1-9A-Z!?-_;00";

        let matrix = MatZq::from_utf8(message, 4, 8, 256).unwrap();

        let string = matrix.to_utf8().unwrap();

        assert_eq!(cmp_text, string);
    }

    /// Ensures that [`MatZq::to_utf8`] outputs an error
    /// if the integer contains an invalid UTF8-Encoding.
    #[test]
    fn invalid_encoding() {
        // 128 is an invalid UTF8-character (at least at the end and on its own)
        let matrix = MatZq::from_str("[[1,2],[3,128]] mod 256").unwrap();
        let string = matrix.to_utf8();

        assert!(string.is_err());
    }
}
