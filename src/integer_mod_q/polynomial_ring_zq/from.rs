// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`PolynomialRingZq`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::PolynomialRingZq;
use crate::{
    error::{MathError, StringConversionError},
    integer::PolyOverZ,
    integer_mod_q::ModulusPolynomialRingZq,
};
use std::str::FromStr;

impl<Poly: Into<PolyOverZ>, Mod: Into<ModulusPolynomialRingZq>> From<(Poly, Mod)>
    for PolynomialRingZq
{
    /// Creates a new polynomial ring element of type [`PolynomialRingZq`].
    ///
    /// Parameters:
    /// - `poly`: the coefficients of the polynomial.
    /// - `modulus`: the modulus that is applied to the polynomial ring element.
    ///
    /// Returns a new element inside the polynomial ring.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let poly_ring = PolynomialRingZq::from((&poly, &modulus));
    /// ```
    fn from((poly, modulus): (Poly, Mod)) -> Self {
        let mut out = Self {
            poly: poly.into(),
            modulus: modulus.into(),
        };
        out.reduce();
        out
    }
}

impl FromStr for PolynomialRingZq {
    type Err = MathError;

    /// Creates a polynomial ring element of type [`PolynomialRingZq`].
    ///
    /// **Warning**: If the polynomials start with a correctly formatted
    /// [`PolyOverZ`] object, the rest of the string
    /// until the `"/"` (for the first polynomial)  or `"mod"` (for the second polynomial)
    /// is ignored. This means that the input string `"4  0 1 2 3 / 2  1 1 mod 13"`
    /// is the same as `"4  0 1 2 3 4 5 6 7 / 2  1 1 mod 13"`.
    ///
    /// Parameters:
    /// - `s`: the polynomial ring element of form:
    ///     "`[#number of coefficients of element]⌴⌴[0th coefficient]⌴
    ///     [1st coefficient]⌴...⌴/⌴[#number of coefficients of polynomial modulus]⌴⌴
    ///     [0th coefficient]⌴[1st coefficient]⌴...⌴mod⌴[q]`".
    ///     Note that the `[#number of coefficients]` and `[0th coefficient]`
    ///     are divided by two spaces and the strings for the polynomials are trimmed,
    ///     i.e. all whitespaces around the polynomials and the modulus are removed.
    ///
    /// Returns a [`PolynomialRingZq`] or an error if the provided string was not
    /// formatted correctly, the numbers of coefficients were smaller than the numbers
    /// provided at the start of the provided string, or the modulus was smaller than `2`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolynomialRingZq::from_str("4  -1 0 1 1 / 4  0 1 -2 3 mod 42").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`StringConversionError`](MathError::StringConversionError)
    ///     - if the provided first half of the string was not formatted correctly to
    ///         create a [`PolyOverZ`],
    ///     - if the provided second half of the
    ///         string was not formatted correctly to create a [`ModulusPolynomialRingZq`],
    ///     - if the numbers of coefficients were smaller than the numbers provided
    ///         at the start of the provided string, or
    ///     - if the provided values did not contain two whitespaces.
    /// - Returns a [`MathError`] of type
    ///     [`InvalidModulus`](MathError::InvalidModulus)
    ///     if the integer modulus `q` is smaller than `2`.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (poly_s, modulus) = match s.split_once("/") {
            Some((poly_s, modulus)) => (poly_s, modulus),
            None => {
                return Err(StringConversionError::InvalidStringToPolyRingZqInput(
                    s.to_owned(),
                ))?
            }
        };
        println!("polynom: {}", poly_s);
        print!("polymod: {}", modulus);

        let poly_over_z = PolyOverZ::from_str(poly_s)?;
        let modulus = ModulusPolynomialRingZq::from_str(modulus)?;

        Ok(Self::from((&poly_over_z, &modulus)))
    }
}

#[cfg(test)]
mod test_from_poly_over_z_modulus_polynomial_ring_zq {
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq},
    };
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Ensure that the modulus is applied with a large prime and large coefficients
    #[test]
    fn is_reduced_large() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();

        let poly =
            PolyOverZ::from_str(&format!("4  {} {} 1 1", LARGE_PRIME + 2, u64::MAX)).unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let cmp_poly = PolyOverZ::from_str("3  1 58 1").unwrap();
        let cmp_poly_ring = PolynomialRingZq::from((&cmp_poly, &modulus));

        assert_eq!(poly_ring, cmp_poly_ring);
    }

    /// Ensure that two ring elements that are instantiated the same way are equal
    #[test]
    fn same_instantiation() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly =
            PolyOverZ::from_str(&format!("4  {} {} 1 1", LARGE_PRIME + 2, u64::MAX)).unwrap();

        let poly_ring_1 = PolynomialRingZq::from((&poly, &modulus));
        let poly_ring_2 = PolynomialRingZq::from((&poly, &modulus));

        assert_eq!(poly_ring_1, poly_ring_2);
    }

    /// Ensures that the function is still available for all values implementing
    /// `Into<ModulusPolynomialRingZq>`.
    #[test]
    fn availability() {
        let poly = PolyOverZ::from(2);
        let poly_mod = PolyOverZq::from_str("2  1 1 mod 17").unwrap();
        let modulus = ModulusPolynomialRingZq::from(&poly_mod);

        let _ = PolynomialRingZq::from((&poly, &poly_mod));
        let _ = PolynomialRingZq::from((&poly, poly_mod.clone()));
        let _ = PolynomialRingZq::from((poly.clone(), &poly_mod));
        let _ = PolynomialRingZq::from((poly.clone(), poly_mod));

        let _ = PolynomialRingZq::from((0_i8, &modulus));
        let _ = PolynomialRingZq::from((0_i16, &modulus));
        let _ = PolynomialRingZq::from((0_i32, &modulus));
        let _ = PolynomialRingZq::from((0_i64, &modulus));
        let _ = PolynomialRingZq::from((0_u8, &modulus));
        let _ = PolynomialRingZq::from((0_u16, &modulus));
        let _ = PolynomialRingZq::from((0_u32, &modulus));
        let _ = PolynomialRingZq::from((0_u64, &modulus));

        let _ = PolynomialRingZq::from((poly.clone(), &modulus));
        let _ = PolynomialRingZq::from((poly, modulus));
    }
}

#[cfg(test)]
mod test_from_str {
    use super::PolynomialRingZq;
    use std::str::FromStr;

    /// tests whether a falsely formatted string (integer modulus is 0) returns an
    /// error
    #[test]
    fn modulus_zero_throws_error() {
        assert!(PolynomialRingZq::from_str("4  -1 0 1 1 / 4  0 1 -2 3 mod 0").is_err());
    }

    /// tests whether a false string (negative modulus) returns an error
    #[test]
    fn false_sign() {
        assert!(PolynomialRingZq::from_str("4  0 1 -2 3 mod -42").is_err());
    }

    /// tests whether a falsely formatted string (wrong whitespaces) returns an
    /// error
    #[test]
    fn whitespaces_in_modulus() {
        assert!(PolynomialRingZq::from_str("4  -1 0 1 1 / 4  0 1 -2 3 mod 4 2").is_err());
    }

    /// tests whether a falsely formatted string (wrong symbols) returns an error
    #[test]
    fn false_format_symbols() {
        assert!(PolynomialRingZq::from_str("4  -1 0 1 1 / 1  1 mod ba").is_err());
        assert!(PolynomialRingZq::from_str("4  -1 0 1a 1 / 1  1 mod 42").is_err());
        assert!(PolynomialRingZq::from_str("4  -1 0 1 1 / b  1 mod 42").is_err());
    }

    /// tests whether a falsely formatted string (missing double-space) returns
    /// an error
    #[test]
    fn false_format() {
        assert!(PolynomialRingZq::from_str("4  -1 0 1 1 / 4 0 1 -2 3 mod 42").is_err());
        assert!(PolynomialRingZq::from_str("4 -1 0 1 1 / 4  0 1 -2 3 mod 42").is_err());
    }

    /// tests whether a falsely formatted string (wrong number of total
    /// coefficients) returns an error
    #[test]
    fn false_number_of_coefficient() {
        assert!(PolynomialRingZq::from_str("4  -1 0 1 1 / 5  0 1 -2 3 mod 42").is_err());
        assert!(PolynomialRingZq::from_str("5  -1 0 1 1 / 4  0 1 -2 3 mod 42").is_err());
    }

    /// tests whether a falsely formatted string (too many whitespaces) returns
    /// an error
    #[test]
    fn too_many_whitespaces() {
        assert!(PolynomialRingZq::from_str("4  -1  0  1  1 / 4  0  1  -2  3 mod 42").is_err());
    }

    /// Ensure that the input works with strings that have to be trimmed
    #[test]
    fn trim_input() {
        let poly = PolynomialRingZq::from_str("        4  -1 0 1 1     /            4  1 2 3 -4                  mod              17                     ");
        assert!(poly.is_ok());
        assert_eq!(
            PolynomialRingZq::from_str("4  -1 0 1 1 / 4  1 2 3 -4 mod 17").unwrap(),
            poly.unwrap()
        );
    }
}
