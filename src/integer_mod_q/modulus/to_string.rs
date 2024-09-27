// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a modulus of type
//! [`Modulus`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::Modulus;
use crate::macros::for_others::implement_for_owned;
use core::fmt;
use flint_sys::fmpz::fmpz_get_str;
use std::{ffi::CStr, ptr::null_mut};

impl From<&Modulus> for String {
    /// Converts a [`Modulus`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the matrix that will be represented as a [`String`]
    ///
    /// Returns a [`String`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    /// let matrix = Modulus::from_str("6").unwrap();
    ///
    /// let string: String = matrix.into();
    /// ```
    fn from(value: &Modulus) -> Self {
        value.to_string()
    }
}

implement_for_owned!(Modulus, String, From);

impl fmt::Display for Modulus {
    /// Allows to convert a modulus of type [`Modulus`] into a [`String`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let modulus = Modulus::from(42);
    /// println!("{modulus}");
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let modulus = Modulus::from(42);
    /// let modulus_string = modulus.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // we have to access modulus.n[0] manually because there is no dedicated
        // method in FLINT
        let c_str_ptr = unsafe { fmpz_get_str(null_mut(), 10, &self.modulus.n[0]) };

        // we expect c_str_ptr to be reference a real value, hence get_str returns an
        // actual value, hence a simple unwrap should be sufficient and we do not have
        // to consider an exception
        //
        // c_string should not be null either, since we call this method on an
        // instantiated object
        let msg = "We expect the pointer to point to a real value and the c_string 
        not to be null.  This error occurs if the provided string does not have UTF-8 format.";
        let return_str = unsafe { CStr::from_ptr(c_str_ptr).to_str().expect(msg).to_owned() };

        unsafe { libc::free(c_str_ptr as *mut libc::c_void) };

        write!(f, "{return_str}")
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::integer_mod_q::Modulus;
    use std::str::FromStr;

    /// Tests whether a large modulus works in a roundtrip
    #[test]
    fn working_large() {
        let cmp_str = "1".repeat(65);
        let cmp = Modulus::from_str(&cmp_str).unwrap();

        assert_eq!(cmp_str, cmp.to_string());
    }

    /// Tests whether a positive modulus works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp_str = "42";
        let cmp = Modulus::from_str(cmp_str).unwrap();

        assert_eq!(cmp_str, cmp.to_string());
    }

    /// Tests whether a modulus that is created using a string, returns a
    /// string that can be used to create a [`Modulus`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp_str = "42";
        let cmp = Modulus::from_str(cmp_str).unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(Modulus::from_str(&cmp_str_2).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "6";
        let matrix = Modulus::from_str(cmp).unwrap();

        let string: String = matrix.clone().into();
        let borrowed_string: String = (&matrix).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}
