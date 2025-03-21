// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
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
use crate::macros::for_others::implement_for_owned;
use core::fmt;
use flint_sys::fmpq::fmpq_get_str;
use std::{ffi::CStr, ptr::null_mut};

impl From<&Q> for String {
    /// Converts a [`Q`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the rational that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"x/y"`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    /// let rational = Q::from_str("6/7").unwrap();
    ///
    /// let string: String = rational.into();
    /// ```
    fn from(value: &Q) -> Self {
        value.to_string()
    }
}

implement_for_owned!(Q, String, From);

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
    /// println!("{rational}");
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

        write!(f, "{return_str}")
    }
}

impl Q {
    /// Outputs the decimal representation of a [`Q`] with
    /// the specified number of decimal digits.
    /// If `self` can't be represented exactly, it provides the
    /// closest value representable with `nr_decimal_digits` rounded
    /// towards the next representable number.
    ///
    /// Notice that, e.g., `0.5` is represented as `0.499...` as [`f64`].
    /// Therefore, rounding with `nr_decimal_digits = 0` will output `0`.
    ///
    /// **WARNING:** This function converts the [`Q`] value into an [`f64`] before
    /// outputting the decimal representation. Thus, values that can't be represented exactly
    /// by an [`f64`] will lose some precision. For large values, e.g. of size `2^64`
    /// the deviation to the original value might be within the size of `1_000`.
    ///
    /// Parameters:
    /// - `nr_decimal_digits`: specifies the number of decimal digits
    ///     that will be a part of the output [`String`]
    ///
    /// Returns a [`String`] of the form `"10.25"` if `nr_decimal_digits = 2`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    /// let rational = Q::from_str("6/7").unwrap();
    ///
    /// let decimal_repr = rational.to_string_decimal(3);
    /// ```
    ///
    /// # Panics ...
    /// - if `self` can't be represented as an [`f64`].
    pub fn to_string_decimal(&self, nr_decimal_digits: usize) -> String {
        let value = f64::from(self);
        format!("{:.1$}", value, nr_decimal_digits)
    }
}

#[cfg(test)]
mod test_to_string_decimal {
    use super::Q;

    /// Ensures that [`Q::to_string_decimal`] works for integer values as intended.
    #[test]
    fn integer() {
        let a = Q::from((5, 1));
        let b = Q::from((256, 8));
        let c = Q::from((-1, 1));

        let a_0 = a.to_string_decimal(0);
        let a_1 = a.to_string_decimal(1);
        let a_2 = a.to_string_decimal(2);
        let b_0 = b.to_string_decimal(0);
        let b_1 = b.to_string_decimal(1);
        let b_5 = b.to_string_decimal(5);
        let c_0 = c.to_string_decimal(0);
        let c_1 = c.to_string_decimal(1);
        let c_2 = c.to_string_decimal(2);

        assert_eq!("5", a_0);
        assert_eq!("5.0", a_1);
        assert_eq!("5.00", a_2);
        assert_eq!("32", b_0);
        assert_eq!("32.0", b_1);
        assert_eq!("32.00000", b_5);
        assert_eq!("-1", c_0);
        assert_eq!("-1.0", c_1);
        assert_eq!("-1.00", c_2);
    }

    /// Ensures that [`Q::to_string_decimal`] works for rational / non-integer values as intended.
    #[test]
    fn non_integer() {
        let a = Q::from((2, 3));
        let b = Q::from((21, 2));
        let c = Q::from((-1, 3));

        let a_0 = a.to_string_decimal(0);
        let a_1 = a.to_string_decimal(1);
        let a_2 = a.to_string_decimal(2);
        let b_0 = b.to_string_decimal(0);
        let b_1 = b.to_string_decimal(1);
        let b_2 = b.to_string_decimal(2);
        let c_0 = c.to_string_decimal(0);
        let c_1 = c.to_string_decimal(1);
        let c_2 = c.to_string_decimal(2);

        assert_eq!("1", a_0);
        assert_eq!("0.7", a_1);
        assert_eq!("0.67", a_2);
        assert_eq!("10", b_0);
        assert_eq!("10.5", b_1);
        assert_eq!("10.50", b_2);
        assert_eq!("-0", c_0);
        assert_eq!("-0.3", c_1);
        assert_eq!("-0.33", c_2);
    }

    /// Ensures that [`Q::to_string_decimal`] works for large numbers.
    #[test]
    fn large_number() {
        let a = Q::from((i64::MAX, 1));

        let a_0 = a.to_string_decimal(0);
        let a_1 = a.to_string_decimal(1);

        assert_eq!("9223372036854774784", a_0); // deviation of 1023 from original value
        assert_eq!("9223372036854774784.0", a_1);
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

        assert_eq!(u64::MAX.to_string(), cmp.to_string());
    }

    /// Tests whether a large negative rational works in a roundtrip
    #[test]
    fn working_large_negative_nom() {
        let cmp = Q::from_str(&format!("-{}", u64::MAX)).unwrap();

        assert_eq!(format!("-{}", u64::MAX), cmp.to_string());
    }

    /// Tests whether a large denominator works in a roundtrip
    #[test]
    fn working_large_positive_den() {
        let cmp = Q::from_str(&format!("1/{}", u64::MAX)).unwrap();

        assert_eq!(format!("1/{}", u64::MAX), cmp.to_string());
    }

    /// Tests whether a large negative denominator works in a roundtrip
    #[test]
    fn working_large_negative_den() {
        let cmp = Q::from_str(&format!("1/-{}", u64::MAX)).unwrap();

        assert_eq!(format!("-1/{}", u64::MAX), cmp.to_string());
    }

    /// Tests whether a positive rational works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = Q::from((42, 235));

        assert_eq!("42/235", cmp.to_string());
    }

    /// Tests whether a negative rational works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = Q::from((-42, 235));

        assert_eq!("-42/235", cmp.to_string());
    }

    /// Tests whether a rational that is created using a string, returns a
    /// string that can be used to create a [`Q`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = Q::from((42, 235));

        let cmp_str_2 = cmp.to_string();

        assert!(Q::from_str(&cmp_str_2).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "6/7";
        let rational = Q::from_str(cmp).unwrap();

        let string: String = rational.clone().into();
        let borrowed_string: String = (&rational).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}
