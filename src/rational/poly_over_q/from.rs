// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`PolyOverQ`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::PolyOverQ;
use crate::{
    error::{MathError, StringConversionError},
    integer::PolyOverZ,
    rational::Q,
};
use flint_sys::fmpq_poly::{
    fmpq_poly_canonicalise, fmpq_poly_set_fmpq, fmpq_poly_set_fmpz_poly, fmpq_poly_set_str,
};
use std::{ffi::CString, str::FromStr};

impl FromStr for PolyOverQ {
    type Err = MathError;

    /// Create a new polynomial with arbitrarily many coefficients of type
    /// [`Q`](crate::rational::Q).
    ///
    /// Parameters:
    /// - `s`: the polynomial of form: "`[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴...`"
    ///
    /// Note that the `[#number of coefficients]` and `[0th coefficient]`
    /// are divided by two spaces and the input string is trimmed, i.e. all whitespaces
    /// before and after are removed.
    ///
    /// Returns a [`PolyOverQ`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverQ::from_str("5  0 1/3 2/10 -3/2 1").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`StringConversionError`](MathError::StringConversionError)
    ///     - if the provided string contains a `Null` Byte,
    ///     - if the provided value did not contain two whitespaces, or
    ///     - if the provided string was not formatted correctly or the number of
    ///         coefficients was smaller than the number provided at the start of the
    ///         provided string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut res = Self::default();

        let c_string = CString::new(s.trim())?;

        // `0` is returned if the string is a valid input
        // additionally if it was not successfully, test if the provided value 's' actually
        // contains two whitespaces, since this might be a common error
        match unsafe { fmpq_poly_set_str(&mut res.poly, c_string.as_ptr()) } {
            0 => unsafe {
                // set_str assumes that all coefficients are reduced as far as possible,
                // hence we have to reduce manually
                fmpq_poly_canonicalise(&mut res.poly);
                Ok(res)
            },
            _ if !s.contains("  ") => Err(
                StringConversionError::InvalidStringToPolyMissingWhitespace(s.to_owned()),
            )?,
            _ => Err(StringConversionError::InvalidStringToPolyInput(
                s.to_owned(),
            ))?,
        }
    }
}

impl PolyOverQ {
    /// Create a [`PolyOverQ`] from a [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `poly`: the polynomial from which the coefficients are copied
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 102 3").unwrap();
    ///
    /// let poly_q = PolyOverQ::from_poly_over_z(&poly);
    ///
    /// # let cmp_poly = PolyOverQ::from_str("4  0 1 102 3").unwrap();
    /// # assert_eq!(cmp_poly, poly_q);
    /// ```
    pub fn from_poly_over_z(poly: &PolyOverZ) -> Self {
        let mut out = Self::default();
        unsafe { fmpq_poly_set_fmpz_poly(&mut out.poly, &poly.poly) };
        out
    }
}

impl From<&PolyOverZ> for PolyOverQ {
    /// Converts a polynomial of type [`PolyOverZ`] to a [`PolyOverQ`] using
    /// [`PolyOverQ::from_poly_over_z`].
    fn from(poly: &PolyOverZ) -> Self {
        Self::from_poly_over_z(poly)
    }
}

impl<Rational: Into<Q>> From<Rational> for PolyOverQ {
    /// Create a constant [`PolyOverQ`] with a specified rational constant.
    ///
    /// # Parameters:
    /// - `value`: the constant value the polynomial will have. It has to be a rational
    ///   number like [`Q`], an integer or a tuple of integers `(numerator, denominator)`.
    ///
    /// Returns a new constant polynomial with the specified value.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::{rational::*, traits::GetCoefficient};
    ///
    /// let one = PolyOverQ::from(1);
    /// let three_quarter = PolyOverQ::from(Q::from((3, 4)));
    /// let one_half = PolyOverQ::from((1, 2));
    ///
    /// assert_eq!(one_half.get_coeff(0).unwrap(), Q::from((1, 2)));
    /// assert_eq!(one_half.get_degree(), 0);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided value can not be converted into a [`Q`].
    ///   For example, because of a division by zero.
    fn from(value: Rational) -> Self {
        let mut out = PolyOverQ::default();
        let value: Q = value.into();

        unsafe {
            fmpq_poly_set_fmpq(&mut out.poly, &value.value);
        }
        out
    }
}

#[cfg(test)]
mod test_from_str {
    use super::PolyOverQ;
    use std::str::FromStr;

    /// Ensure that zero-coefficients are reduced
    #[test]
    fn reduce_zero_coeff() {
        let one_1 = PolyOverQ::from_str("2  24/42 1").unwrap();
        let one_2 = PolyOverQ::from_str("3  24/42 1 0").unwrap();

        assert_eq!(one_1, one_2);
    }

    /// Ensure that coefficients in the string are reduced
    #[test]
    fn reduce_coeff() {
        assert_eq!(
            PolyOverQ::from_str("3  4/77 4/14 -28/21").unwrap(),
            PolyOverQ::from_str("3  4/77 2/7 -28/21").unwrap()
        );
    }

    /// Tests whether the same string yields the same polynomial
    #[test]
    fn same_string() {
        let str_1 = format!("3  1 2/3 {}/{}", u64::MAX, i64::MIN);

        let poly_1 = PolyOverQ::from_str(&str_1).unwrap();
        let poly_2 = PolyOverQ::from_str(&str_1).unwrap();

        assert_eq!(poly_1, poly_2);
    }

    /// Tests whether a correctly formatted string outputs an instantiation of a
    /// polynomial, i.e. does not return an error
    #[test]
    fn working_example() {
        assert!(PolyOverQ::from_str("3  1 2/5 -3/2").is_ok());
    }

    /// Tests whether a falsely formatted string (missing double-space) returns
    /// an error
    #[test]
    fn missing_whitespace() {
        assert!(PolyOverQ::from_str("3 1 2/5 -3/2").is_err());
        assert!(PolyOverQ::from_str("3 12/5 2 -3").is_err());
        assert!(PolyOverQ::from_str("2 17 42/4").is_err());
        assert!(PolyOverQ::from_str("2 17 42").is_err());
        assert!(PolyOverQ::from_str("2 17/1 42").is_err());
        assert!(PolyOverQ::from_str("2 17/13 42  ").is_err());
        assert!(PolyOverQ::from_str("  2 17/5 42").is_err());
    }

    /// Tests whether a falsely formatted string (too many whitespaces) returns
    /// an error
    #[test]
    fn too_many_whitespaces() {
        assert!(PolyOverQ::from_str("3  1  2/5  -3/2").is_err());
    }

    /// Tests whether a falsely formatted string (wrong number of total
    /// coefficients) returns an error
    #[test]
    fn false_number_of_coefficient() {
        assert!(PolyOverQ::from_str("4  1 2/5 -3/2").is_err());
    }

    /// Tests whether a falsely formatted string (too many divisors) returns
    /// an error
    #[test]
    fn too_many_divisors() {
        assert!(PolyOverQ::from_str("3  1 2/5 -3/2/3").is_err());
    }

    /// Ensure that the input works with strings that have to be trimmed
    #[test]
    fn trim_input() {
        let poly = PolyOverQ::from_str("                   4  1/2 2/3 3/4 -4                  ");
        assert!(poly.is_ok());
        assert_eq!(
            PolyOverQ::from_str("4  1/2 2/3 3/4 -4").unwrap(),
            poly.unwrap()
        );
    }
}

#[cfg(test)]
mod test_from_poly_over_z {
    use crate::{integer::PolyOverZ, rational::PolyOverQ};
    use std::str::FromStr;

    /// Ensure that the conversion works with negative entries
    #[test]
    fn small_negative() {
        let poly = PolyOverZ::from_str("4  0 1 -102 -3").unwrap();

        let poly_q = PolyOverQ::from(&poly);

        let cmp_poly = PolyOverQ::from_str("4  0 1 -102 -3").unwrap();
        assert_eq!(cmp_poly, poly_q);
    }

    /// Ensure that the conversion works with negative large entries
    #[test]
    fn large_negative() {
        let poly = PolyOverZ::from_str(&format!("4  0 1 -102 -{}", u64::MAX)).unwrap();

        let poly_q = PolyOverQ::from(&poly);

        let cmp_poly = PolyOverQ::from_str(&format!("4  0 1 -102 -{}", u64::MAX)).unwrap();
        assert_eq!(cmp_poly, poly_q);
    }

    /// Ensure that the conversion works with positive large entries
    #[test]
    fn large_positive() {
        let poly = PolyOverZ::from_str(&format!("4  0 1 102 {}", u64::MAX)).unwrap();

        let poly_q = PolyOverQ::from(&poly);

        let cmp_poly = PolyOverQ::from_str(&format!("4  0 1 102 {}", u64::MAX)).unwrap();
        assert_eq!(cmp_poly, poly_q);
    }
}

#[cfg(test)]
mod test_from_rational {
    use super::*;
    use crate::{integer::Z, traits::GetCoefficient};

    /// Ensure that the [`From`] trait works for large
    /// borrowed and owned [`Q`],[`Z`] and [`u64`] instances.
    #[test]
    fn large() {
        let value = Q::from(u64::MAX);

        let poly = PolyOverQ::from(&value);
        let poly_2 = PolyOverQ::from(value.clone());
        let poly_3 = PolyOverQ::from(u64::MAX);
        let poly_4 = PolyOverQ::from(&u64::MAX);
        let poly_5 = PolyOverQ::from(Z::from(u64::MAX));
        let poly_6 = PolyOverQ::from(&Z::from(u64::MAX));

        assert_eq!(poly.get_coeff(0).unwrap(), value);
        assert_eq!(poly.get_degree(), 0);
        assert_eq!(poly, poly_2);
        assert_eq!(poly, poly_3);
        assert_eq!(poly, poly_4);
        assert_eq!(poly, poly_5);
        assert_eq!(poly, poly_6);
    }

    /// Ensure that the [`From`] trait works for small
    /// borrowed and owned [`Q`] and integer tuples instances.
    #[test]
    fn small() {
        let value = Q::from((1, 2));

        let poly = PolyOverQ::from(&value);
        let poly_2 = PolyOverQ::from(value.clone());
        let poly_3 = PolyOverQ::from((1, 2));
        let poly_4 = PolyOverQ::from((&1, &2));

        assert_eq!(poly.get_coeff(0).unwrap(), value);
        assert_eq!(poly.get_degree(), 0);
        assert_eq!(poly, poly_2);
        assert_eq!(poly, poly_3);
        assert_eq!(poly, poly_4);
    }

    /// Ensure that a division by zero panics.
    #[test]
    #[should_panic]
    fn divide_by_zero() {
        let _ = PolyOverQ::from((1, 0));
    }
}
