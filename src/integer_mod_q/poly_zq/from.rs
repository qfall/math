//! Implementations to create a [`PolyZq`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::PolyZq;
use crate::{error::MathError, integer::PolyZ, integer_mod_q::modulus::Modulus};
use flint_sys::fmpz_mod_poly::{fmpz_mod_poly_init, fmpz_mod_poly_set_fmpz_poly};
use std::{mem::MaybeUninit, str::FromStr};

impl FromStr for PolyZq {
    type Err = MathError;

    /// Creating a polynomial with arbitrarily many coefficients of type
    /// [`Zq`](crate::integer_mod_q::z_q::Zq).
    ///
    /// Parameters:
    /// - `s`: the polynomial of form:
    /// "`[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴...⌴mod⌴[modulus]`".
    /// Note that the `[#number of coefficients]` and `[0th coefficient]`
    /// are divided by two spaces.
    ///
    /// Returns a [`PolyZq`] or an error, if the provided string was not
    /// formatted correctly.
    ///
    /// # Example
    /// ```rust
    /// use math::integer_mod_q::PolyZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyZq::from_str("4  0 1 -2 3 mod 42").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToPolyModulusInput`](MathError::InvalidStringToPolyModulusInput)
    /// if the provided string was not formatted correctly to create a [`Modulus`].
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToPolyMissingWhitespace`](`MathError::InvalidStringToPolyMissingWhitespace`)
    /// if the provided value did not contain two whitespaces.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToPolyInput`](MathError::InvalidStringToPolyInput)
    /// if the provided half of the string was not formatted correctly to
    /// create a polynomial.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToModulusInput`](MathError::InvalidStringToModulusInput)
    /// if the provided half of the
    /// string was not formatted correctly to create a [`Modulus`].
    /// - Returns a [`MathError`] of type
    /// [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the provided modulus is not greater than zero.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (poly_s, modulus) = match s.split_once(" mod ") {
            Some((poly_s, modulus)) => (poly_s, modulus),
            None => return Err(MathError::InvalidStringToPolyModulusInput(s.to_owned())),
        };

        let poly_z = PolyZ::from_str(poly_s)?;
        let modulus = Modulus::from_str(modulus)?;

        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpz_mod_poly_init(poly.as_mut_ptr(), &modulus.modulus);
            let mut poly = poly.assume_init();
            fmpz_mod_poly_set_fmpz_poly(&mut poly, &poly_z.poly, &modulus.modulus);
            Ok(Self { poly, modulus })
        }
    }
}

#[cfg(test)]
mod test_from_str {

    use super::PolyZq;
    use std::str::FromStr;

    /// tests whether a falsely formatted string (modulus is 0) returns an
    /// error
    #[test]
    fn modulus_zero_throws_error() {
        assert!(PolyZq::from_str("4  0 1 -2 3 mod 0").is_err())
    }

    /// tests whether a falsely formatted string (several modulus) returns
    /// an error
    #[test]
    fn several_mod() {
        assert!(PolyZq::from_str("4  0 1 -2 3 mod 42 mod 13").is_err());
    }

    /// tests whether a falsely formatted string (wrong whitespaces) returns an
    /// error
    #[test]
    fn whitespaces_in_modulus() {
        assert!(PolyZq::from_str("4  0 1 -2 3 mod 4 2").is_err());
    }

    /// tests whether a falsely formatted string (wrong symbols) returns an error
    #[test]
    fn false_format_symbols_modulus() {
        assert!(PolyZq::from_str("1  1 mod ba").is_err());
    }

    /// tests whether a falsely formatted string (wrong symbols) returns an error
    #[test]
    fn false_format_symbols_polynomial() {
        assert!(PolyZq::from_str("1  ba mod 42").is_err());
    }

    /// tests whether a false string (negative modulus) returns an error
    #[test]
    fn false_sign() {
        assert!(PolyZq::from_str("4  0 1 -2 3 mod -42").is_err());
    }

    /// tests whether a falsely formatted string (missing double-space) returns
    /// an error
    #[test]
    fn false_format() {
        assert!(PolyZq::from_str("4 0 1 -2 3 mod 42").is_err());
    }

    /// tests whether a falsely formatted string (wrong number of total
    /// coefficients) returns an error
    #[test]
    fn false_number_of_coefficient() {
        assert!(PolyZq::from_str("5  0 1 -2 3 mod 42").is_err());
    }

    /// tests whether a falsely formatted string (missing double-space) returns
    /// an error
    #[test]
    fn missing_whitespace() {
        assert!(PolyZq::from_str("4 0 1 -2 3 mod 42").is_err());
    }

    /// tests whether a falsely formatted string (too many whitespaces) returns
    /// an error
    #[test]
    fn too_many_whitespaces() {
        assert!(PolyZq::from_str("4  0  1  -2  3 mod 42").is_err());
    }
}