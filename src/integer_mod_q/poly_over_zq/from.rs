// Copyright © 2023 Marvin Beckmann and Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`PolyOverZq`] value from other types.
//!
//! The explicit functions contain the documentation.

use crate::{
    error::{MathError, StringConversionError},
    integer::PolyOverZ,
    integer_mod_q::{modulus::Modulus, ModulusPolynomialRingZq, PolyOverZq, Zq},
};
use flint_sys::fmpz_mod_poly::{
    fmpz_mod_poly_init, fmpz_mod_poly_set, fmpz_mod_poly_set_fmpz_poly,
};
use std::{mem::MaybeUninit, str::FromStr};

impl From<&Modulus> for PolyOverZq {
    /// Create a zero polynomial with a given [`Modulus`].
    ///
    /// Parameters:
    /// - `modulus` of the new [`PolyOverZq`]
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::integer_mod_q::{PolyOverZq, Modulus};
    /// use std::str::FromStr;
    ///
    /// let modulus = Modulus::from(100);
    /// let poly = PolyOverZq::from(&modulus);
    ///
    /// let poly_cmp = PolyOverZq::from_str("0 mod 100").unwrap();
    /// assert_eq!(poly, poly_cmp);
    /// ```
    fn from(modulus: &Modulus) -> Self {
        let modulus = modulus.clone();
        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpz_mod_poly_init(poly.as_mut_ptr(), modulus.get_fmpz_mod_ctx_struct());
            let poly = poly.assume_init();
            PolyOverZq { poly, modulus }
        }
    }
}

impl<Mod: Into<Modulus>> From<(&PolyOverZ, Mod)> for PolyOverZq {
    /// Create a [`PolyOverZq`] from a [`PolyOverZ`] and [`Modulus`].
    ///
    /// Parameters:
    /// - `poly`: The coefficients of the polynomial.
    /// - `modulus`: The modulus by which each entry is reduced.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::integer_mod_q::{PolyOverZq, Modulus};
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 102 3").unwrap();
    /// let modulus = Modulus::from(100);
    ///
    /// let mod_poly = PolyOverZq::from((&poly, &modulus));
    ///
    /// # let cmp_poly = PolyOverZq::from_str("4  0 1 2 3 mod 100").unwrap();
    /// # assert_eq!(cmp_poly, mod_poly);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    fn from((poly, modulus): (&PolyOverZ, Mod)) -> Self {
        let mut res = PolyOverZq::from(&modulus.into());
        unsafe {
            fmpz_mod_poly_set_fmpz_poly(
                &mut res.poly,
                &poly.poly,
                res.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        res
    }
}

impl From<&ModulusPolynomialRingZq> for PolyOverZq {
    /// Create a [`PolyOverZ`] from a [`ModulusPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `modulus`: the context polynomial from which the coefficients are copied
    ///
    /// # Examples
    ///
    /// Returns the context [`PolyOverZq`] representing the modulus object.
    ///
    /// ```
    /// use qfall_math::integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    ///
    /// let poly_zq = PolyOverZq::from(&modulus);
    ///
    /// let cmp_poly = PolyOverZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// assert_eq!(cmp_poly, poly_zq);
    /// ```
    fn from(modulus: &ModulusPolynomialRingZq) -> Self {
        let modulus_q = Modulus::from(&modulus.get_q());
        let mut out = PolyOverZq::from(&modulus_q);
        unsafe {
            fmpz_mod_poly_set(
                &mut out.poly,
                &modulus.get_fq_ctx_struct().modulus[0],
                out.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
        out
    }
}

impl FromStr for PolyOverZq {
    type Err = MathError;

    /// Creating a polynomial with arbitrarily many coefficients of type [`Zq`].
    ///
    /// Parameters:
    /// - `s`: the polynomial of form:
    ///     "`[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴...⌴mod⌴[modulus]`".
    ///     Note that the `[#number of coefficients]` and `[0th coefficient]`
    ///     are divided by two spaces and the string for the polynomial is trimmed,
    ///     i.e. all whitespaces before around the polynomial and the modulus are removed.
    ///
    /// Returns a [`PolyOverZq`] or an error, if the provided string was not
    /// formatted correctly.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("4  0 1 -2 3 mod 42").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`StringConversionError`](MathError::StringConversionError)
    ///     - if the provided first half of the string was not formatted correctly to
    ///         create a [`PolyOverZ`],
    ///     - if the provided second half of the
    ///         string was not formatted correctly to create a [`Modulus`],
    ///     - if the number of coefficients was smaller than the number provided
    ///         at the start of the provided string, or
    ///     - if the provided value did not contain two whitespaces.
    /// - Returns a [`MathError`] of type
    ///     [`InvalidModulus`](MathError::InvalidModulus)
    ///     if `modulus` is smaller than `2`.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (poly_s, modulus) = match s.split_once("mod") {
            Some((poly_s, modulus)) => (poly_s, modulus.trim()),
            None => {
                return Err(StringConversionError::InvalidStringToPolyModulusInput(
                    s.to_owned(),
                ))?
            }
        };

        let poly_over_z = PolyOverZ::from_str(poly_s)?;
        let modulus = Modulus::from_str(modulus)?;

        Ok(Self::from((&poly_over_z, &modulus)))
    }
}

impl<IntegerModQ: Into<Zq>> From<IntegerModQ> for PolyOverZq {
    /// Create a constant [`PolyOverZq`] with a specified constant.
    ///
    /// # Parameters:
    /// - `value`: the constant value the polynomial will have.
    ///   It has to be a [`Zq`], or a value that can be converted into [`Zq`].
    ///   
    /// Returns a new constant polynomial with the specified value and modulus.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::{integer_mod_q::*, traits::*};
    ///
    /// let poly = PolyOverZq::from((1, 10));
    /// let poly_2 = PolyOverZq::from(Zq::from((1, 10)));
    ///
    /// let value_cmp: Zq = poly.get_coeff(0).unwrap();
    /// assert_eq!(value_cmp, Zq::from((1, 10)));
    /// assert_eq!(poly.get_degree(), 0);
    /// assert_eq!(poly, poly_2);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided value can not be converted into a [`Zq`].
    ///   For example, if the modulus is not larger than one.
    fn from(value: IntegerModQ) -> Self {
        let value: Zq = value.into();
        let poly_z = PolyOverZ::from(value.value);

        PolyOverZq::from((&poly_z, &value.modulus))
    }
}

#[cfg(test)]
mod test_from_zq {
    use super::*;
    use crate::{integer::Z, traits::GetCoefficient};

    /// Ensure that the [`From`] trait works for small
    /// borrowed and owned [`Zq`], and tuples of value and modulus instances
    #[test]
    fn small() {
        let value: Zq = Zq::from((1, 2));

        let poly = PolyOverZq::from(&value);
        let poly_2 = PolyOverZq::from(value.clone());
        let poly_3 = PolyOverZq::from((1, 2));
        let poly_4 = PolyOverZq::from((&1, &2));

        let value_set: Zq = poly.get_coeff(0).unwrap();
        assert_eq!(value_set, value);
        assert_eq!(poly.get_degree(), 0);
        assert_eq!(poly, poly_2);
        assert_eq!(poly, poly_3);
        assert_eq!(poly, poly_4);
    }

    /// Ensure that the [`From`] trait works for large
    /// borrowed and owned [`Zq`], and tuples of value and modulus instances.
    #[test]
    fn large() {
        let value = Zq::from((u64::MAX - 1, u64::MAX));
        let modulus = Modulus::from(u64::MAX);

        let poly = PolyOverZq::from(&value);
        let poly_2 = PolyOverZq::from(value.clone());
        let poly_3 = PolyOverZq::from((u64::MAX - 1, &modulus));
        let poly_4 = PolyOverZq::from((&(u64::MAX - 1), &modulus));
        let poly_5 = PolyOverZq::from((Z::from(u64::MAX - 1), &u64::MAX));
        let poly_6 = PolyOverZq::from((&Z::from(u64::MAX - 1), u64::MAX));

        let value_set: Zq = poly.get_coeff(0).unwrap();
        assert_eq!(value_set, value);
        assert_eq!(poly.get_degree(), 0);
        assert_eq!(poly, poly_2);
        assert_eq!(poly, poly_3);
        assert_eq!(poly, poly_4);
        assert_eq!(poly, poly_5);
        assert_eq!(poly, poly_6);
    }

    /// Ensure that the modulus is applied when creating a [`PolyOverZq`]
    /// from a constant [`Zq`].
    #[test]
    fn modulus_reduction() {
        let poly = PolyOverZq::from((42, 5));

        let value_set: Zq = poly.get_coeff(0).unwrap();
        assert_eq!(value_set, Zq::from((2, 5)));
    }

    /// Ensure that the polynomial can not be created with an invalid modulus.
    #[test]
    #[should_panic]
    fn invalid_modulus() {
        let _ = PolyOverZq::from((10, 1));
    }
}

#[cfg(test)]
mod test_from_poly_z_modulus {
    use super::PolyOverZq;
    use crate::{integer::PolyOverZ, integer_mod_q::Modulus};
    use std::str::FromStr;

    /// Test conversion of a [`PolyOverZ`] with small coefficients and small
    /// [`Modulus`] into a [`PolyOverZq`].
    #[test]
    fn working_small() {
        let poly = PolyOverZ::from_str("4  0 1 -2 3").unwrap();
        let modulus = Modulus::from(100);

        let mod_poly = PolyOverZq::from((&poly, &modulus));

        let cmp_poly = PolyOverZq::from_str("4  0 1 -2 3 mod 100").unwrap();
        assert_eq!(cmp_poly, mod_poly);
    }

    /// Test conversion of a [`PolyOverZ`] with large coefficients and large
    /// [`Modulus`] into a [`PolyOverZq`].
    #[test]
    fn working_large() {
        let poly = PolyOverZ::from_str(&format!("4  {} {} -2 3", u64::MAX - 1, u64::MAX)).unwrap();
        let modulus = Modulus::from(u64::MAX);

        let mod_poly = PolyOverZq::from((&poly, &modulus));

        let cmp_poly = PolyOverZq::from_str(&format!("4  -1 0 -2 3 mod {}", u64::MAX)).unwrap();
        assert_eq!(cmp_poly, mod_poly);
    }

    /// Test that the coefficients are reduced properly after the conversion.
    #[test]
    fn reduce() {
        let poly = PolyOverZ::from_str("4  100 101 -102 103").unwrap();
        let modulus = Modulus::from(100);

        let mod_poly = PolyOverZq::from((&poly, &modulus));

        let cmp_poly = PolyOverZq::from_str("4  0 1 -2 3 mod 100").unwrap();
        assert_eq!(cmp_poly, mod_poly);
    }
}

#[cfg(test)]
mod test_from_str {
    use super::PolyOverZq;
    use std::str::FromStr;

    /// tests whether a falsely formatted string (modulus is 0) returns an
    /// error
    #[test]
    fn modulus_zero_throws_error() {
        assert!(PolyOverZq::from_str("4  0 1 -2 3 mod 0").is_err());
    }

    /// tests whether a falsely formatted string (several modulus) returns
    /// an error
    #[test]
    fn several_mod() {
        assert!(PolyOverZq::from_str("4  0 1 -2 3 mod 42 mod 13").is_err());
    }

    /// tests whether a falsely formatted string (wrong whitespaces) returns an
    /// error
    #[test]
    fn whitespaces_in_modulus() {
        assert!(PolyOverZq::from_str("4  0 1 -2 3 mod 4 2").is_err());
    }

    /// tests whether a falsely formatted string (wrong symbols) returns an error
    #[test]
    fn false_format_symbols_modulus() {
        assert!(PolyOverZq::from_str("1  1 mod ba").is_err());
    }

    /// tests whether a falsely formatted string (wrong symbols) returns an error
    #[test]
    fn false_format_symbols_polynomial() {
        assert!(PolyOverZq::from_str("1  ba mod 42").is_err());
    }

    /// tests whether a false string (negative modulus) returns an error
    #[test]
    fn false_sign() {
        assert!(PolyOverZq::from_str("4  0 1 -2 3 mod -42").is_err());
    }

    /// tests whether a falsely formatted string (missing double-space) returns
    /// an error
    #[test]
    fn false_format() {
        assert!(PolyOverZq::from_str("4 0 1 -2 3 mod 42").is_err());
    }

    /// tests whether a falsely formatted string (wrong number of total
    /// coefficients) returns an error
    #[test]
    fn false_number_of_coefficient() {
        assert!(PolyOverZq::from_str("5  0 1 -2 3 mod 42").is_err());
    }

    /// tests whether a falsely formatted string (missing double-space) returns
    /// an error
    #[test]
    fn missing_whitespace() {
        assert!(PolyOverZq::from_str("3 12 2 -3 mod 42").is_err());
        assert!(PolyOverZq::from_str("2 17 42 mod 42").is_err());
        assert!(PolyOverZq::from_str("2 17  42 mod 42").is_err());
        assert!(PolyOverZq::from_str("2 17 42   mod 42").is_err());
        assert!(PolyOverZq::from_str("  2 17 42 mod 42").is_err());
        assert!(PolyOverZq::from_str("2 17 42 mod 42  ").is_err());
    }

    /// tests whether a falsely formatted string (too many whitespaces) returns
    /// an error
    #[test]
    fn too_many_whitespaces() {
        assert!(PolyOverZq::from_str("4  0  1  -2  3 mod 42").is_err());
    }

    /// Ensure that the input works with strings that have to be trimmed
    #[test]
    fn trim_input() {
        let poly = PolyOverZq::from_str("                   4  1 2 3 -4                  mod              17                     ");
        assert!(poly.is_ok());
        assert_eq!(
            PolyOverZq::from_str("4  1 2 3 -4 mod 17").unwrap(),
            poly.unwrap()
        );
    }
}

#[cfg(test)]
mod test_from_modulus_polynomial_ring_zq {
    use crate::integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq};
    use std::str::FromStr;

    /// ensure that the conversion works with positive large entries
    #[test]
    fn large_positive() {
        let modulus_ring =
            ModulusPolynomialRingZq::from_str(&format!("4  -1 0 0 1 mod {}", u64::MAX - 58))
                .unwrap();

        let modulus = PolyOverZq::from(&modulus_ring);

        let cmp_poly =
            PolyOverZq::from_str(&format!("4  {} 0 0 1 mod {}", u64::MAX - 59, u64::MAX - 58))
                .unwrap();
        assert_eq!(cmp_poly, modulus);
    }
}
