//! This module contains all options to convert a polynomial of type
//! [`ModulusPolynomialRingZq] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::ModulusPolynomialRingZq;
use crate::integer::{PolyOverZ, Z};
use flint_sys::{fmpz::fmpz_set, fmpz_mod_poly::fmpz_mod_poly_get_fmpz_poly};
use std::fmt::Display;

impl Display for ModulusPolynomialRingZq {
    /// Allows to convert a [`ModulusPolynomialRingZq`] into a [`String`].
    ///
    /// # Examples
    /// ```
    /// use math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// println!("{}", poly);
    /// ```
    ///
    /// ```
    /// use math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let poly_string = poly.to_string();
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // get the value of the modulus
        let mut modulus = Z::default();
        unsafe { fmpz_set(&mut modulus.value, &self.get_fq_ctx_struct().ctxp[0].n[0]) };

        // get the value of the polynomial
        let mut poly = PolyOverZ::default();
        unsafe {
            fmpz_mod_poly_get_fmpz_poly(
                &mut poly.poly,
                &self.get_fq_ctx_struct().modulus[0],
                &self.get_fq_ctx_struct().ctxp[0],
            )
        };

        write!(f, "{} mod {}", poly, modulus)
    }
}

/// most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_to_string {
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// test whether a roundtrip works
    #[test]
    fn working_keeps_same_string() {
        let cmp_string = "3  1 2 2 mod 5";
        let cmp = ModulusPolynomialRingZq::from_str(cmp_string).unwrap();

        assert_eq!(cmp_string, cmp.to_string())
    }

    /// test whether a string returned from to_string can be used to construct a [`ModulusPolynomialRingZq`]
    #[test]
    fn working_use_result_of_to_string() {
        let cmp_string = "3  1 2 2 mod 5";
        let cmp = ModulusPolynomialRingZq::from_str(cmp_string).unwrap();
        let str = cmp.to_string();

        assert!(ModulusPolynomialRingZq::from_str(&str).is_ok())
    }
}
