// Copyright © 2023 Marvin Beckmann
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
use core::fmt;
use flint_sys::fmpz::fmpz_get_str;
use std::{ffi::CStr, ptr::null_mut};

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
    /// println!("{}", integer);
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
        let c_str_ptr = unsafe { fmpz_get_str(null_mut(), 10, &self.value) };

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

        write!(f, "{}", return_str)
    }
}

#[cfg(test)]
mod test_to_string {

    use crate::integer::Z;
    use std::str::FromStr;

    /// tests whether a large positive integer works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = Z::from(u64::MAX);

        assert_eq!(u64::MAX.to_string(), cmp.to_string())
    }

    /// tests whether a large negative integer works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = Z::from_str(&format!("-{}", u64::MAX)).unwrap();

        assert_eq!(format!("-{}", u64::MAX), cmp.to_string())
    }

    /// tests whether a positive integer works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = Z::from(42);

        assert_eq!("42", cmp.to_string())
    }

    /// tests whether a negative integer works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = Z::from(-42);

        assert_eq!("-42", cmp.to_string())
    }

    /// tests whether an integer that is created using a string, returns a
    /// string that can be used to create a [`Z`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = Z::from(42);

        let cmp_string2 = cmp.to_string();

        assert!(Z::from_str(&cmp_string2).is_ok())
    }
}
