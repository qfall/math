//! Implementations of the 'From' trait for [PolyZq].
//!
//! This module contains all options to create a polynomial of type [PolyZq].

use std::{mem::MaybeUninit, str::FromStr};

use flint_sys::fmpz_mod_poly::{fmpz_mod_poly_init, fmpz_mod_poly_set_fmpz_poly};

use crate::{error::MathError, integer::poly_z::PolyZ, integer_mod_q::modulus::Modulus};

use super::PolyZq;

impl FromStr for PolyZq {
    type Err = MathError;

    /// Creating a polynomial with integer coefficients modulo q of arbitrary length using a string as input.
    ///
    /// Parameters:
    /// - `s`: the polynomial of form: "[#number of coefficients]  [0th coefficient] [1st coefficient] ... mod [modulus]"
    /// Returns a [PolyZq] or an error, if the provided string was not formatted correctly.
    ///
    /// # Example
    /// ```rust
    /// use math::integer_mod_q::PolyZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyZq::from_str("4  0 1 -2 3 mod 42").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [MathError::InvalidStringToPolyModulusInput] if the provided string was not formatted correctly.
    /// - Returns a [`MathError`] of type [MathError::InvalidStringToPolyInput] if the provided half of the string was not formatted correctly to create a polynomial.
    /// - Returns a [`MathError`] of type [MathError::InvalidStringToModulusInput] if the provided half of the string was not formatted correctly to create a modulus.
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
mod test {
    use std::str::FromStr;

    use crate::integer_mod_q::poly_zq::PolyZq;

    // tests whether a correctly formatted string outputs an instantiation of a polynomial mod q, i.e. does not return an error
    #[test]
    fn from_str_working_example() {
        assert!(PolyZq::from_str("4  0 1 -2 3 mod 42").is_ok())
    }

    // tests whether a falsely formatted string (wrong whitespaces) returns an error
    #[test]
    fn from_str_false_format_whitespaces() {
        assert!(PolyZq::from_str("4  0 1 -2 3 mod 4 2").is_err());
    }

    // tests whether a falsely formatted string (wrong symbols) returns an error
    #[test]
    fn from_str_false_format_symbols() {
        assert!(PolyZq::from_str("1  ba mod 42").is_err());
        assert!(PolyZq::from_str("1  1 mod ba").is_err());
    }

    // tests whether a false string (negative modulus) returns an error
    #[test]
    fn from_str_false_sign() {
        assert!(PolyZq::from_str("4  0 1 -2 3 mod -42").is_err());
    }

    // tests whether a falsely formatted string (missing double-space) returns an error
    #[test]
    fn from_str_false_format() {
        assert!(PolyZq::from_str("4 0 1 -2 3 mod 42").is_err());
    }

    // tests whether a falsely formatted string (wrong number of total coefficients) returns an error
    #[test]
    fn from_str_false_number_of_coefficient() {
        assert!(PolyZq::from_str("5  0 1 -2 3 mod 42").is_err());
    }
}
