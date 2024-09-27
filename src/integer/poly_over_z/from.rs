// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`PolyOverZ`] value from other types.
//!
//! The explicit functions contain the documentation.

use super::PolyOverZ;
use crate::integer_mod_q::PolyOverZq;
use crate::macros::for_others::implement_for_owned;
use crate::{
    error::{MathError, StringConversionError},
    integer::Z,
    traits::AsInteger,
};
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_get_fmpz_poly;
use flint_sys::fmpz_poly::{fmpz_poly_set_fmpz, fmpz_poly_set_str};
use std::{ffi::CString, str::FromStr};

impl FromStr for PolyOverZ {
    type Err = MathError;

    /// Creates a polynomial with arbitrarily many coefficients of type [`Z`]
    /// from a [`String`].
    ///
    /// **Warning**: If the input string starts with a correctly formatted [`PolyOverZ`] object,
    /// the rest of the string is ignored. This means that the input string
    /// `"4  0 1 2 3"` is the same as `"4  0 1 2 3 4 5 6 7"`.
    ///
    /// Parameters:
    /// - `s`: the polynomial of form: `"[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴..."`.
    ///
    /// Note that the `[#number of coefficients]` and `[0th coefficient]`
    /// are divided by two spaces and the input string is trimmed, i.e. all whitespaces
    /// before and after are removed.
    ///
    /// Returns a [`PolyOverZ`] or an error if the provided string was not formatted
    /// correctly, the number of coefficients was smaller than the number provided
    /// at the start of the provided string, or the provided string contains a `Null` Byte.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::StringConversionError`]
    ///     - if the provided string was not formatted correctly,
    ///     - if the number of coefficients was smaller than the number provided
    ///         at the start of the provided string,
    ///     - if the provided value did not contain two whitespaces, or
    ///     - if the provided string contains a `Null` Byte.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // remove whitespaces at the start and at the end
        let s_trimmed = s.trim();

        if s_trimmed == "0" {
            return Ok(Self::default());
        }

        // fmpz_poly_set_str just skips the two symbols after the first space
        // behind the number of coefficients (even if not a space), hence
        // it has to be checked here to Ensure that no number is lost.
        // We only have to check it once, because for every other position it checks
        // whether there is only one space.
        if !s_trimmed.contains("  ") {
            return Err(StringConversionError::InvalidStringToPolyMissingWhitespace(
                s.to_owned(),
            ))?;
        };

        let mut res = Self::default();

        let c_string = CString::new(s_trimmed)?;

        match unsafe { fmpz_poly_set_str(&mut res.poly, c_string.as_ptr()) } {
            0 => Ok(res),
            _ => Err(StringConversionError::InvalidStringToPolyInput(
                s.to_owned(),
            ))?,
        }
    }
}

impl<Integer: AsInteger + Into<Z>> From<Integer> for PolyOverZ {
    /// Creates a constant [`PolyOverZ`] with a specified integer constant.
    ///
    /// # Parameters:
    /// `value`: an integer like [`Z`], rust Integers or a reference to these values.
    ///
    /// Returns a new constant polynomial with the specified value.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::{integer::*, traits::*};
    ///
    /// let one = PolyOverZ::from(1);
    ///
    /// assert_eq!(one.get_coeff(0).unwrap(), Z::ONE);
    /// assert_eq!(one.get_degree(), 0);
    /// ```
    fn from(value: Integer) -> Self {
        let mut ret = PolyOverZ::default();
        unsafe {
            match value.get_fmpz_ref() {
                Some(fmpz_ref) => fmpz_poly_set_fmpz(&mut ret.poly, fmpz_ref),
                None => {
                    // Does not include a fmpz in the original data Type.
                    // We convert the value into Z to also handle the memory management.
                    let z_value: Z = value.into();
                    fmpz_poly_set_fmpz(&mut ret.poly, &z_value.value)
                }
            }
        }

        ret
    }
}

impl From<&PolyOverZ> for PolyOverZ {
    /// Alias for [`PolyOverZ::clone`].
    fn from(value: &PolyOverZ) -> Self {
        value.clone()
    }
}

impl From<&PolyOverZq> for PolyOverZ {
    /// Creates a [`PolyOverZ`] from a [`PolyOverZq`].
    ///
    /// Parameters:
    /// - `poly`: the polynomial from which the coefficients are copied.
    ///
    /// Returns the representative polynomial (all reduced coefficients)
    /// of the [`PolyOverZq`] as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("4  0 1 5 3 mod 4").unwrap();
    ///
    /// let poly_z = PolyOverZ::from(&poly);
    ///
    /// # let cmp_poly = PolyOverZ::from_str("4  0 1 1 3").unwrap();
    /// # assert_eq!(cmp_poly, poly_z);
    /// ```
    fn from(poly: &PolyOverZq) -> Self {
        let mut out = Self::default();
        unsafe {
            fmpz_mod_poly_get_fmpz_poly(
                &mut out.poly,
                &poly.poly,
                poly.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
        out
    }
}

implement_for_owned!(PolyOverZq, PolyOverZ, From);

#[cfg(test)]
mod test_from_str {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that zero-coefficients are reduced
    #[test]
    fn reduce_zero_coeff() {
        let one_1 = PolyOverZ::from_str("2  24 1").unwrap();
        let one_2 = PolyOverZ::from_str("3  24 1 0").unwrap();

        assert_eq!(one_1, one_2);
    }

    /// Tests whether the same string yields the same polynomial
    #[test]
    fn same_string() {
        let str_1 = format!("3  1 {} {}", u64::MAX, i64::MIN);

        let poly_1 = PolyOverZ::from_str(&str_1).unwrap();
        let poly_2 = PolyOverZ::from_str(&str_1).unwrap();

        assert_eq!(poly_1, poly_2);
    }

    /// Tests whether a correctly formatted string outputs an instantiation of a
    /// polynomial, i.e. does not return an error
    #[test]
    fn working_example() {
        assert!(PolyOverZ::from_str("3  1 2 -3").is_ok());
    }

    /// Tests whether a falsely formatted string (missing double-space) returns
    /// an error
    #[test]
    fn missing_whitespace() {
        assert!(PolyOverZ::from_str("3 12 2 -3").is_err());
        assert!(PolyOverZ::from_str("2 17 42").is_err());
        assert!(PolyOverZ::from_str("2 17  42").is_err());
        assert!(PolyOverZ::from_str("2 17 42  ").is_err());
        assert!(PolyOverZ::from_str("  2 17 42").is_err());
    }

    /// Tests whether a falsely formatted string (too many whitespaces) returns
    /// an error
    #[test]
    fn too_many_whitespaces() {
        assert!(PolyOverZ::from_str("3  1  2  -3").is_err());
    }

    /// Tests whether a falsely formatted string (wrong number of total
    /// coefficients) returns an error
    #[test]
    fn false_number_of_coefficient() {
        assert!(PolyOverZ::from_str("4  1 2 -3").is_err());
    }

    /// Ensure that the input works with strings that have to be trimmed
    #[test]
    fn trim_input() {
        let poly = PolyOverZ::from_str("                   4  1 2 3 -4                  ");
        assert!(poly.is_ok());
        assert_eq!(PolyOverZ::from_str("4  1 2 3 -4").unwrap(), poly.unwrap());
    }
}

#[cfg(test)]
mod test_from_poly_over_zq {
    use crate::{integer::PolyOverZ, integer_mod_q::PolyOverZq};
    use std::str::FromStr;

    /// Ensure that the conversion works with positive large entries
    #[test]
    fn large_positive() {
        let poly = PolyOverZq::from_str(&format!("4  0 1 102 {} mod {}", u64::MAX - 58, u64::MAX))
            .unwrap();

        let poly_z = PolyOverZ::from(&poly);

        let cmp_poly = PolyOverZ::from_str(&format!("4  0 1 102 {}", u64::MAX - 58)).unwrap();
        assert_eq!(cmp_poly, poly_z);
    }

    /// Ensure that the conversion works for owned values
    #[test]
    fn availability() {
        let poly = PolyOverZq::from_str(&format!("4  0 1 102 {} mod {}", u64::MAX - 58, u64::MAX))
            .unwrap();

        let _ = PolyOverZ::from(poly);
    }
}

#[cfg(test)]
mod test_from_integer {
    use super::*;
    use crate::traits::GetCoefficient;

    /// Ensure that the [`From`] trait works for large
    /// borrowed and owned [`Z`] and [`u64`] instances.
    #[test]
    fn large() {
        let value = Z::from(u64::MAX);

        let poly = PolyOverZ::from(&value);
        let poly_2 = PolyOverZ::from(value.clone());
        let poly_3 = PolyOverZ::from(u64::MAX);
        let poly_4 = PolyOverZ::from(&u64::MAX);

        assert_eq!(value, poly.get_coeff(0).unwrap());
        assert_eq!(poly.get_degree(), 0);
        assert_eq!(poly, poly_2);
        assert_eq!(poly, poly_3);
        assert_eq!(poly, poly_4);
    }

    /// Ensure that the [`From`] trait works for small
    /// borrowed and owned [`Z`] and rust integer instances.
    #[test]
    fn small() {
        let value = Z::ONE;

        let poly = PolyOverZ::from(&value);
        let poly_2 = PolyOverZ::from(value.clone());

        let poly_3 = PolyOverZ::from(1u64);
        let poly_4 = PolyOverZ::from(&1u64);
        let poly_5 = PolyOverZ::from(1i64);
        let poly_6 = PolyOverZ::from(&1i64);
        // Assume that it also works for the other rust integers.

        assert_eq!(value, poly.get_coeff(0).unwrap());
        assert_eq!(poly.get_degree(), 0);
        assert_eq!(poly, poly_2);
        assert_eq!(poly, poly_3);
        assert_eq!(poly, poly_4);
        assert_eq!(poly, poly_5);
        assert_eq!(poly, poly_6);
    }

    /// Ensure that the [`From`] trait works for large negative
    /// borrowed and owned [`Z`] and rust integer instances.
    #[test]
    fn negative() {
        let value = Z::from(i64::MIN);

        let poly = PolyOverZ::from(&value);
        let poly_2 = PolyOverZ::from(value.clone());

        let poly_3 = PolyOverZ::from(i64::MIN);
        let poly_4 = PolyOverZ::from(&i64::MIN);
        // Assume that it also works for the other rust integers.

        assert_eq!(value, poly.get_coeff(0).unwrap());
        assert_eq!(poly.get_degree(), 0);
        assert_eq!(poly, poly_2);
        assert_eq!(poly, poly_3);
        assert_eq!(poly, poly_4);
    }
}
