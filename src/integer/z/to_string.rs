// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert an integer of type
//! [`Z`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::Z;
use crate::{error::MathError, macros::for_others::implement_for_owned};
use core::fmt;
use flint_sys::fmpz::{fmpz_bits, fmpz_get_str, fmpz_tstbit};
use std::{ffi::CStr, ptr::null_mut, string::FromUtf8Error};

impl From<&Z> for String {
    /// Converts a [`Z`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    /// let matrix = Z::from_str("6").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &Z) -> Self {
        value.to_string()
    }
}

implement_for_owned!(Z, String, From);

impl fmt::Display for Z {
    /// Allows to convert an integer of type [`Z`] into a [`String`].
    ///
    /// Returns the integer in form of a [`String`]. For integer `1`
    /// the String looks like this `1`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use core::fmt;
    ///
    /// let integer = Z::from(42);
    /// println!("{integer}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer::Z;
    /// use core::fmt;
    ///
    /// let integer = Z::from(42);
    /// let integer_string = integer.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_b(10).unwrap())
    }
}

impl Z {
    /// Allows to convert an integer of type [`Z`] into a [`String`]
    /// with a configurable base `b` between `2` and `62`.
    ///
    /// Parameters:
    /// - `b`: specifies any base between `2` and `62` which specifies
    ///     the base of the returned [`String`].
    ///
    /// Returns the integer in form of a [`String`] with regards to the base `b`
    /// or an error, if the base is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use core::fmt;
    ///
    /// let integer = Z::from(42);
    /// println!("{integer}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer::Z;
    /// use core::fmt;
    ///
    /// let integer = Z::from(42);
    /// let integer_string = integer.to_string();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if the
    ///     base is not between `2` and `62`.
    pub fn to_string_b(&self, base: i32) -> Result<String, MathError> {
        if !(2..=62).contains(&base) {
            return Err(MathError::OutOfBounds(
                "between 2 and 62".to_owned(),
                base.to_string(),
            ));
        }

        let c_str_ptr = unsafe { fmpz_get_str(null_mut(), base, &self.value) };

        // we expect c_str_ptr to be reference a real value, hence get_str returns an
        // actual value, hence a simple unwrap should be sufficient and we do not have
        // to consider an exception
        //
        // c_string should not be null either, since we call this method on an
        // instantiated object
        let msg = "We expect the pointer to point to a real value and the c_string 
        not to be null. This error occurs if the provided string does not have UTF-8 format.";
        let return_str = unsafe { CStr::from_ptr(c_str_ptr).to_str().expect(msg).to_owned() };

        unsafe { libc::free(c_str_ptr as *mut libc::c_void) };

        Ok(return_str)
    }

    /// Outputs the integer as a [`Vec`] of bytes.
    /// The inverse function to [`Z::to_bytes`] is [`Z::from_bytes`] for positive numbers including `0`.
    ///
    /// **Warning**: The bits are returned as they are stored in the memory. For negative numbers,
    /// this means that `-1` is output as `[255]`.
    /// For these values, [`Z::from_bytes`] is not inverse to [`Z::to_bytes`],
    /// as this function can only instantiate positive values.
    ///
    /// Returns a [`Vec<u8>`] of bytes representing the integer as it is stored in memory.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let integer = Z::from(257);
    ///
    /// let byte_string = integer.to_bytes();
    ///
    /// assert_eq!(vec![1, 1], byte_string);
    /// ```
    pub fn to_bytes(&self) -> Vec<u8> {
        let num_bits = unsafe { fmpz_bits(&self.value) } as usize;
        let num_bytes = num_bits.div_ceil(8);
        let mut bytes = vec![0u8; num_bytes];

        for (byte, item) in bytes.iter_mut().enumerate() {
            for bit_of_byte in (0..8usize).rev() {
                let bit_index = (byte * u8::BITS as usize + bit_of_byte) as u64;
                let bit_at_index = unsafe { fmpz_tstbit(&self.value, bit_index) };

                *item *= 2;
                if bit_at_index == 1 {
                    *item += 1;
                }
            }
        }

        bytes
    }

    /// Enables conversion to a UTF8-Encoded [`String`] for [`Z`] values.
    /// The inverse to this function is [`Z::from_utf8`] for valid UTF8-Encodings.
    ///
    /// **Warning**: Not every byte-sequence forms a valid UTF8-character.
    /// If this is the case, a [`FromUtf8Error`] will be returned.
    ///
    /// Returns the corresponding UTF8-encoded [`String`] or a
    /// [`FromUtf8Error`] if the byte sequence contains an invalid UTF8-character.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let integer = Z::from(10);
    ///
    /// let text: String = integer.to_utf8().unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`FromUtf8Error`] if the integer's byte sequence contains
    ///     invalid UTF8-characters.
    pub fn to_utf8(&self) -> Result<String, FromUtf8Error> {
        String::from_utf8(self.to_bytes())
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::integer::Z;
    use std::str::FromStr;

    /// Tests whether a large positive integer works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = Z::from(u64::MAX);

        assert_eq!(u64::MAX.to_string(), cmp.to_string());
    }

    /// Tests whether a large negative integer works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = Z::from_str(&format!("-{}", u64::MAX)).unwrap();

        assert_eq!(format!("-{}", u64::MAX), cmp.to_string());
    }

    /// Tests whether a positive integer works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = Z::from(42);

        assert_eq!("42", cmp.to_string());
    }

    /// Tests whether a negative integer works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = Z::from(-42);

        assert_eq!("-42", cmp.to_string());
    }

    /// Tests whether an integer that is created using a string, returns a
    /// string that can be used to create a [`Z`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = Z::from(42);

        let cmp_str_2 = cmp.to_string();

        assert!(Z::from_str(&cmp_str_2).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "6";
        let matrix = Z::from_str(cmp).unwrap();

        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}

#[cfg(test)]
mod test_to_string_b {
    use crate::integer::Z;

    /// Ensure that an error is returned, if an invalid base is provided
    #[test]
    fn out_of_bounds() {
        let value = Z::from(42);

        assert!(value.to_string_b(-1).is_err());
        assert!(value.to_string_b(1).is_err());
        assert!(value.to_string_b(63).is_err());
    }

    /// Ensure that binary representation works correctly
    #[test]
    fn binary() {
        let value_1 = Z::from(u64::MAX);
        let cmp_str_1 = "1".repeat(64);

        let value_2 = Z::from(i64::MIN);
        let cmp_str_2 = format!("-1{}", "0".repeat(63));

        assert_eq!(cmp_str_1, value_1.to_string_b(2).unwrap());
        assert_eq!(cmp_str_2, value_2.to_string_b(2).unwrap());
    }
}

#[cfg(test)]
mod test_to_bytes {
    use super::Z;

    /// Ensures that [`Z::to_bytes`] is inverse to [`Z::from_bytes`] for positive values.
    #[test]
    fn inverse_to_from_bytes() {
        let bytes: Vec<u8> = vec![0, 255, 128, 77, 31, 52];

        let integer = Z::from_bytes(&bytes);
        let cmp_bytes = integer.to_bytes();

        assert_eq!(bytes, cmp_bytes);
    }

    /// Ensures that [`Z::ZERO`] results in an empty vector of bytes.
    #[test]
    fn zero() {
        let integer = Z::ZERO;
        let cmp_bytes: Vec<u8> = vec![];

        let bytes = integer.to_bytes();

        assert_eq!(cmp_bytes, bytes);
    }

    /// Ensure that negative values are represented as they are stored in memory.
    #[test]
    fn negative() {
        let integer = Z::MINUS_ONE;
        let cmp_bytes: Vec<u8> = vec![255];

        let bytes = integer.to_bytes();
        let integer = Z::from_bytes(&bytes);

        println!("{}", integer);
        assert_eq!(cmp_bytes, bytes);
    }
}

#[cfg(test)]
mod test_to_utf8 {
    use super::Z;

    /// Ensures that [`Z::to_utf8`] is inverse to [`Z::from_utf8`] for valid UTF8-Encodings.
    #[test]
    fn inverse_to_from_utf8() {
        let cmp_text = "Some valid string formatted in UTF8!";

        let integer = Z::from_utf8(cmp_text);
        let text = integer.to_utf8().unwrap();

        assert_eq!(cmp_text, text);
    }

    /// Ensures that [`Z::to_utf8`] outputs an error
    /// if the integer contains an invalid UTF8-Encoding.
    #[test]
    fn invalid_encoding() {
        let invalid_sequence = [128];

        let integer = Z::from_bytes(&invalid_sequence);
        let text = integer.to_utf8();

        assert!(text.is_err());
    }
}
