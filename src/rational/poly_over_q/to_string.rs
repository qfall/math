// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
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
use crate::{macros::for_others::implement_for_owned, traits::GetCoefficient};
use core::fmt;
use flint_sys::fmpq_poly::fmpq_poly_get_str;
use std::ffi::CStr;

impl From<&PolyOverQ> for String {
    /// Converts a [`PolyOverQ`] into its [`String`] representation.
    ///
    /// Parameters:
    /// - `value`: specifies the polynomial that will be represented as a [`String`]
    ///
    /// Returns a [`String`] of the form `"[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴..."`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    /// let poly = PolyOverQ::from_str("2  6/7 1").unwrap();
    ///
    /// let string: String = poly.into();
    /// ```
    fn from(value: &PolyOverQ) -> Self {
        value.to_string()
    }
}

implement_for_owned!(PolyOverQ, String, From);

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

impl PolyOverQ {
    /// Outputs a representation of [`PolyOverQ`] with the decimal representation
    /// of each coefficient with the specified number of decimal digits.
    /// If a coefficient can't be represented exactly, it provides the
    /// closest value representable with `nr_decimal_digits` rounded towards zero.
    ///
    /// **WARNING:** This function converts every coefficient into an [`f64`] before
    /// outputting the decimal representation. Thus, values that can't be represented exactly
    /// by a [`f64`] will lose some precision. For large values, e.g. of size `2^64`
    /// the deviation to the original value might be within the size of `1_000`.
    ///
    /// Parameters:
    /// - `nr_decimal_digits`: specifies the number of decimal digits
    ///     that will be a part of the output [`String`]
    ///
    /// Returns the polynomial in form of a [`String`]. For polynomial `2  1/2 5/3`
    /// the [`String`] looks like this `2  0.50 1.66` if `nr_decimal_digits = 2`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    /// let poly = PolyOverQ::from_str("4  5/2 2 -2/3 4/3").unwrap();
    ///
    /// let decimal_repr = poly.to_string_decimal(3);
    /// ```
    ///
    /// # Panics ...
    /// - if any entry of the polynomial can't be represented as a [`f64`].
    pub fn to_string_decimal(&self, nr_decimal_digits: usize) -> String {
        let degree = self.get_degree() + 1;
        let mut poly_string = format!("{degree}  ");

        for i in 0..degree {
            // swap with get_coeff_unchecked once available
            let entry = self.get_coeff(i).unwrap();
            let entry_string = entry.to_string_decimal(nr_decimal_digits);

            poly_string.push_str(&entry_string);
            poly_string.push(' ');
        }
        poly_string = poly_string.trim().to_string();

        poly_string
    }
}

/// This module avoids tests already performed for [`crate::rational::Q::to_string_decimal`].
#[cfg(test)]
mod test_to_string_decimal {
    use super::PolyOverQ;
    use std::str::FromStr;

    /// Ensures that [`PolyOverQ::to_string_decimal`] works for different degrees
    /// and different `nr_decimal_digits`.
    #[test]
    fn different_degrees() {
        let a = PolyOverQ::from_str("0").unwrap();
        let b = PolyOverQ::from_str("1  1/3").unwrap();
        let c = PolyOverQ::from_str("3  1/3 0 -5/3").unwrap();

        let a_0 = a.to_string_decimal(0);
        let a_1 = a.to_string_decimal(1);
        let b_0 = b.to_string_decimal(0);
        let b_2 = b.to_string_decimal(2);
        let c_0 = c.to_string_decimal(0);
        let c_1 = c.to_string_decimal(1);

        assert_eq!("0", a_0);
        assert_eq!("0", a_1);
        assert_eq!("1  0", b_0);
        assert_eq!("1  0.33", b_2);
        assert_eq!("3  0 0 -1", c_0);
        assert_eq!("3  0.3 0.0 -1.6", c_1);
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
        let cmp_str = "5  0 1 2/5 -3/2 1";
        let cmp = PolyOverQ::from_str(cmp_str).unwrap();

        assert_eq!(cmp_str, cmp.to_string());
    }

    /// Tests whether a polynomial that is created using a string, returns a
    /// string that can be used to create a polynomial
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp_str = "5  0 1 2/5 -3/2 1";
        let cmp = PolyOverQ::from_str(cmp_str).unwrap();

        let cmp_str_2 = cmp.to_string();

        assert!(PolyOverQ::from_str(&cmp_str_2).is_ok());
    }

    /// Ensures that the `Into<String>` trait works properly
    #[test]
    fn into_works_properly() {
        let cmp = "2  6/7 2";
        let poly = PolyOverQ::from_str(cmp).unwrap();

        let string: String = poly.clone().into();
        let borrowed_string: String = (&poly).into();

        assert_eq!(cmp, string);
        assert_eq!(cmp, borrowed_string);
    }
}
