// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a polynomial of type
//! [`PolyOverZ`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::PolyOverZ;
use crate::macros::for_others::implement_for_owned;
use core::fmt;
use flint_sys::fmpz_poly::fmpz_poly_get_str;
use std::ffi::CStr;

impl From<&PolyOverZ> for String {
    /// Converts a [`PolyOverZ`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴..."`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    /// let matrix = PolyOverZ::from_str("2  6 1").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &PolyOverZ) -> Self {
        value.to_string()
    }
}

implement_for_owned!(PolyOverZ, String, From);

impl fmt::Display for PolyOverZ {
    /// Allows to convert a polynomial of type [`PolyOverZ`] into a [`String`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    /// println!("{poly}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    /// let poly_string = poly.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c_str_ptr = unsafe { fmpz_poly_get_str(&self.poly) };
        let return_str = unsafe { CStr::from_ptr(c_str_ptr).to_str().unwrap().to_owned() };
        // free the space allocated by the pointer
        unsafe { libc::free(c_str_ptr as *mut libc::c_void) };
        write!(f, "{}", return_str)
    }
}

#[cfg(test)]
mod test_to_string {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Tests whether a polynomial that is created using a string, returns the
    /// same string, when it is converted back to a string
    #[test]
    fn working_keeps_same_string() {
        let cmp_str = "3  1 2 -3";
        let cmp = PolyOverZ::from_str(cmp_str).unwrap();

        assert_eq!(cmp_str, cmp.to_string());
    }

    /// Tests whether a polynomial that is created using a string, returns a
    /// string that can be used to create a polynomial
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp_str = "3  1 2 -3";
        let cmp = PolyOverZ::from_str(cmp_str).unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(PolyOverZ::from_str(&cmp_str_2).is_ok());
    }

    /// Tests whether large entries are correctly converted using to_string
    #[test]
    fn large_entries() {
        let cmp_str = format!("3  1 {} -{}", u64::MAX, u64::MAX);
        let cmp = PolyOverZ::from_str(&cmp_str).unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(PolyOverZ::from_str(&cmp_str_2).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "2  6 1";
        let matrix = PolyOverZ::from_str(cmp).unwrap();

        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}
