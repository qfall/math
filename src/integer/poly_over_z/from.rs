// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`PolyOverZ`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::PolyOverZ;
use crate::error::MathError;
use flint_sys::fmpz_poly::fmpz_poly_set_str;
use std::{ffi::CString, str::FromStr};

impl FromStr for PolyOverZ {
    type Err = MathError;

    // TODO: the second whitespace is not shown in the Rust-documentation
    /// Create a new polynomial with arbitrarily many coefficients of type
    /// [`Z`](crate::integer::Z).
    ///
    /// Parameters:
    /// - `s`: the polynomial of form: `"[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴..."`.
    ///  Note that the `[#number of coefficients]` and `[0th coefficient]`
    ///  are divided by two spaces.
    ///
    /// Returns a [`PolyOverZ`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::InvalidStringToPolyInput`]
    /// if the provided string was not formatted correctly or the number of
    /// coefficients was smaller than the number provided at the start of the
    /// provided string.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToPolyMissingWhitespace`](MathError::InvalidStringToPolyMissingWhitespace)
    /// if the provided value did not contain two whitespaces.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if the provided string contains a Null Byte.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut res = Self::default();

        let c_string = CString::new(s)?;

        // 0 is returned if the string is a valid input
        // additionally if it was not successfully, test if the provided value 's' actually
        // contains two whitespaces, since this might be a common error
        match unsafe { fmpz_poly_set_str(&mut res.poly, c_string.as_ptr()) } {
            0 => Ok(res),
            _ if !s.contains("  ") => Err(MathError::InvalidStringToPolyMissingWhitespace(
                s.to_owned(),
            )),
            _ => Err(MathError::InvalidStringToPolyInput(s.to_owned())),
        }
    }
}

#[cfg(test)]
mod test_from_str {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that zero-coefficients are reduced
    #[test]
    fn reduce_zero_coeff() {
        let one_1 = PolyOverZ::from_str("2  24 1").unwrap();
        let one_2 = PolyOverZ::from_str("3  24 1 0").unwrap();

        assert_eq!(one_1, one_2)
    }

    /// tests whether the same string yields the same polynomial
    #[test]
    fn same_string() {
        let str = format!("3  1 {} {}", u64::MAX, i64::MIN);

        let poly_1 = PolyOverZ::from_str(&str).unwrap();
        let poly_2 = PolyOverZ::from_str(&str).unwrap();

        assert_eq!(poly_1, poly_2)
    }

    /// tests whether a correctly formatted string outputs an instantiation of a
    /// polynomial, i.e. does not return an error
    #[test]
    fn working_example() {
        assert!(PolyOverZ::from_str("3  1 2 -3").is_ok());
    }

    /// tests whether a falsely formatted string (missing double-space) returns
    /// an error
    #[test]
    fn missing_whitespace() {
        assert!(PolyOverZ::from_str("3 1 2 -3").is_err());
    }

    /// tests whether a falsely formatted string (too many whitespaces) returns
    /// an error
    #[test]
    fn too_many_whitespaces() {
        assert!(PolyOverZ::from_str("3  1  2  -3").is_err());
    }

    /// tests whether a falsely formatted string (wrong number of total
    /// coefficients) returns an error
    #[test]
    fn false_number_of_coefficient() {
        assert!(PolyOverZ::from_str("4  1 2 -3").is_err());
    }
}
