// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a rational of type
//! [`Q`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::Q;
use core::fmt;
use flint_sys::fmpq::fmpq_get_str;
use std::{ffi::CStr, ptr::null_mut};

impl fmt::Display for Q {
    /// Allows to convert a rational of type [`Q`] into a [`String`].
    ///
    /// Returns the rational in form of a [`String`]. For rational `1/2`
    /// the String looks like this `1/2`.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::rational::Q;
    /// use core::fmt;
    ///
    /// let rational = Q::from((-1, 235));
    /// println!("{}", rational);
    /// ```
    ///
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::rational::Q;
    /// use core::fmt;
    ///
    /// let rational = Q::from((-1, 235));
    /// let integer_string = rational.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c_str_ptr = unsafe { fmpq_get_str(null_mut(), 10, &self.value) };

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
    use crate::rational::Q;
    use std::str::FromStr;

    /// Tests whether a large positive rational works in a roundtrip
    #[test]
    fn working_large_positive_nom() {
        let cmp = Q::from(u64::MAX);

        assert_eq!(u64::MAX.to_string(), cmp.to_string())
    }

    /// Tests whether a large negative rational works in a roundtrip
    #[test]
    fn working_large_negative_nom() {
        let cmp = Q::from_str(&format!("-{}", u64::MAX)).unwrap();

        assert_eq!(format!("-{}", u64::MAX), cmp.to_string())
    }

    /// Tests whether a large denominator works in a roundtrip
    #[test]
    fn working_large_positive_den() {
        let cmp = Q::from_str(&format!("1/{}", u64::MAX)).unwrap();

        assert_eq!(format!("1/{}", u64::MAX), cmp.to_string())
    }

    /// Tests whether a large negative denominator works in a roundtrip
    #[test]
    fn working_large_negative_den() {
        let cmp = Q::from_str(&format!("1/-{}", u64::MAX)).unwrap();

        assert_eq!(format!("-1/{}", u64::MAX), cmp.to_string())
    }

    /// Tests whether a positive rational works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = Q::from((42, 235));

        assert_eq!("42/235", cmp.to_string())
    }

    /// Tests whether a negative rational works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = Q::from((-42, 235));

        assert_eq!("-42/235", cmp.to_string())
    }

    /// Tests whether a rational that is created using a string, returns a
    /// string that can be used to create a [`Q`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = Q::from((42, 235));

        let cmp_string2 = cmp.to_string();

        assert!(Q::from_str(&cmp_string2).is_ok())
    }
}
