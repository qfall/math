// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a polynomial of type
//! [`PolyOverQ`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::PolyOverQ;
use core::fmt;
use flint_sys::fmpq_poly::fmpq_poly_get_str;
use std::ffi::CStr;

impl fmt::Display for PolyOverQ {
    /// Allows to convert a polynomial of type [`PolyOverQ`] into a [`String`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let poly = PolyOverQ::from_str("5  0 1 2/5 -3/2 1").unwrap();
    /// println!("{poly}");
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverQ::from_str("5  0 1 2/5 -3/2 1").unwrap();
    /// let poly_string = poly.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c_str_ptr = unsafe { fmpq_poly_get_str(&self.poly) };
        let return_str = unsafe { CStr::from_ptr(c_str_ptr).to_str().unwrap().to_owned() };
        // free the space allocated by the pointer
        unsafe { libc::free(c_str_ptr as *mut libc::c_void) };
        write!(f, "{return_str}")
    }
}

#[cfg(test)]
mod test_to_string {
    use super::PolyOverQ;
    use std::str::FromStr;

    /// Tests whether a polynomial that is created using a string, returns the
    /// same string, when it is converted back to a string
    #[test]
    fn working_keeps_same_string() {
        let cmp_string = "5  0 1 2/5 -3/2 1";
        let cmp = PolyOverQ::from_str(cmp_string).unwrap();

        assert_eq!(cmp_string, cmp.to_string())
    }

    /// Tests whether a polynomial that is created using a string, returns a
    /// string that can be used to create a polynomial
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp_string = "5  0 1 2/5 -3/2 1";
        let cmp = PolyOverQ::from_str(cmp_string).unwrap();

        let cmp_string2 = cmp.to_string();

        assert!(PolyOverQ::from_str(&cmp_string2).is_ok())
    }
}
