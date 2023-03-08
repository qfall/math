//! This module contains all options to convert a polynomial of type
//! [`ModulusPolynomialRingZq] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::ModulusPolynomialRingZq;
use crate::integer_mod_q::PolyOverZq;
use flint_sys::{fmpz_mod::fmpz_mod_ctx_init, fmpz_mod_poly::fmpz_mod_poly_set};
use std::{fmt::Display, str::FromStr};

impl Display for ModulusPolynomialRingZq {
    /// Allows to convert a [`ModulusPolynomialRingZq`] into a [`String`].
    ///
    /// # Examples
    /// ```rust
    /// use math::finite_fields::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// println!("{}", poly);
    /// ```
    ///
    /// ```rust
    /// use math::finite_fields::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let poly_string = poly.to_string();
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // initialize
        // unwrap is ok, since we now, that this should always work
        let mut out = PolyOverZq::from_str("0 mod 1").unwrap();
        unsafe {
            // set context
            fmpz_mod_ctx_init(&mut out.modulus.modulus, &self.modulus.ctxp[0].n[0]);
            // set coefficients
            fmpz_mod_poly_set(
                &mut out.poly,
                &self.modulus.modulus[0],
                &self.modulus.ctxp[0],
            );
            // use fmt of [`PolyOverZq`]
            out.fmt(f)
        }
    }
}

/// most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_to_string {
    use crate::finite_fields::ModulusPolynomialRingZq;
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
