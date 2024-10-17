// Copyright © 2023 Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert an integer of type
//! [`Zq`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::Zq;
use crate::macros::for_others::implement_for_owned;
use core::fmt;
use std::string::FromUtf8Error;

impl From<&Zq> for String {
    /// Converts a [`Zq`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"x mod q"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use std::str::FromStr;
    /// let matrix = Zq::from_str("3 mod 5").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &Zq) -> Self {
        value.to_string()
    }
}

implement_for_owned!(Zq, String, From);

impl fmt::Display for Zq {
    /// Allows to convert an integer of type [`Zq`] into a [`String`].
    ///
    /// Returns the integer in form of a [`String`]. For integer `2 mod 4`
    /// the String looks like this `2 mod 4`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let integer_mod_q = Zq::from((42, 3));
    /// println!("{integer_mod_q}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let integer_mod_q = Zq::from((42, 3));
    /// let integer_string = integer_mod_q.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} mod {}", self.value, self.modulus)
    }
}

impl Zq {
    /// Enables conversion to a UTF8-Encoded [`String`] for [`Zq`] values.
    /// The inverse to this function is [`Zq::from_utf8`] for valid UTF8-Encodings.
    ///
    /// **Warning**: Not every byte-sequence forms a valid UTF8-character.
    /// If this is the case, a [`FromUtf8Error`] will be returned.
    ///
    /// Returns the corresponding UTF8-encoded [`String`] or a
    /// [`FromUtf8Error`] if the byte sequence contains an invalid UTF8-character.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// let value = Zq::from((10, 63));
    ///
    /// let text: String = value.to_utf8().unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`FromUtf8Error`] if the integer's byte sequence contains
    ///     invalid UTF8-characters.
    pub fn to_utf8(&self) -> Result<String, FromUtf8Error> {
        String::from_utf8(self.get_value().to_bytes())
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::integer_mod_q::Zq;
    use std::str::FromStr;

    /// Tests whether a large integer works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = Zq::from_str(&format!("{} mod {}", u64::MAX, u128::MAX)).unwrap();

        assert_eq!(format!("{} mod {}", u64::MAX, u128::MAX), cmp.to_string());
    }

    /// Tests whether a large integer works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = Zq::from_str(&format!("-{} mod {}", u64::MAX, u128::MAX)).unwrap();
        let diff = u128::MAX - u64::MAX as u128;

        assert_eq!(format!("{diff} mod {}", u128::MAX), cmp.to_string());
    }

    /// Tests whether a positive integer works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = Zq::from_str("42 mod 60").unwrap();

        assert_eq!("42 mod 60", cmp.to_string());
    }

    /// Tests whether a negative integer works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = Zq::from_str("-40 mod 3").unwrap();

        assert_eq!("2 mod 3", cmp.to_string());
    }

    /// Tests whether a integer that is created using a string, returns a
    /// string that can be used to create a [`Zq`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = Zq::from((42, 10));

        let cmp_str = cmp.to_string();

        assert!(Zq::from_str(&cmp_str).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "6 mod 11";
        let matrix = Zq::from_str(cmp).unwrap();

        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}

#[cfg(test)]
/// This module omits tests performed in [`crate::integer::Z::to_utf8`].
mod test_to_utf8 {
    use super::Zq;

    /// Ensures that [`Zq::to_utf8`] is inverse to [`Zq::from_utf8`] for valid UTF8-Encodings.
    #[test]
    fn inverse_to_from_utf8() {
        let cmp_text = "Test!";

        let value = Zq::from_utf8(cmp_text, u64::MAX).unwrap();
        let text = value.to_utf8().unwrap();

        assert_eq!(cmp_text, text);
    }
}
