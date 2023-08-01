// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to manipulate a [`PolyOverZq`] polynomial.

use super::PolyOverZq;
use crate::{
    error::MathError, integer::Z, integer_mod_q::Zq, macros::for_others::implement_for_owned,
    traits::SetCoefficient, utils::index::evaluate_index,
};
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_set_coeff_fmpz;
use std::fmt::Display;

impl<Integer: Into<Z>> SetCoefficient<Integer> for PolyOverZq {
    /// Sets the coefficient of a polynomial [`PolyOverZq`].
    /// We advise to use small coefficients, since already 2^32 coefficients take space
    /// of roughly 34 GB. If not careful, be prepared that memory problems can occur, if
    /// the index is very high.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to set (has to be positive)
    /// - `value`: the new value the coefficient will be set to.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if either the index is negative
    /// or it does not fit into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use qfall_math::integer::Z;
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let mut poly = PolyOverZq::from_str("4  0 1 2 3 mod 17").unwrap();
    ///
    /// assert!(poly.set_coeff(4, 1000).is_ok());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the index is negative or it does not fit into an [`i64`].
    fn set_coeff(
        &mut self,
        index: impl TryInto<i64> + Display,
        value: Integer,
    ) -> Result<(), MathError> {
        let value: Z = value.into();
        let index = evaluate_index(index)?;

        unsafe {
            fmpz_mod_poly_set_coeff_fmpz(
                &mut self.poly,
                index,
                &value.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );
        };
        Ok(())
    }
}

impl SetCoefficient<&Zq> for PolyOverZq {
    /// Sets the coefficient of a polynomial [`PolyOverZq`].
    /// We advise to use small coefficients, since already 2^32 coefficients take space
    /// of roughly 34 GB. If not careful, be prepared that memory problems can occur, if
    /// the index is very high.
    ///
    /// All entries which are not directly addressed are automatically treated as zero.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to set (has to be positive)
    /// - `value`: the new value the index should have from a borrowed [`Zq`].
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if either the index is negative
    /// or it does not fit into an [`i64`], or the moduli of
    /// the polynomial and the input mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let mut poly = PolyOverZq::from_str("4  0 1 2 3 mod 17").unwrap();
    /// let value = Zq::from((1000, 17));
    ///
    /// assert!(poly.set_coeff(4, &value).is_ok());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the index is negative or it does not fit into an [`i64`].
    /// - Returns a [`MathError`] of type
    ///  [`MismatchingModulus`](MathError::MismatchingModulus) the moduli of
    /// the polynomial and the input mismatch
    fn set_coeff(
        &mut self,
        index: impl TryInto<i64> + Display,
        value: &Zq,
    ) -> Result<(), MathError> {
        if self.modulus != value.modulus {
            return Err(MathError::MismatchingModulus(value.to_string()));
        }
        self.set_coeff(index, &value.value)
    }
}

implement_for_owned!(Zq, PolyOverZq, SetCoefficient);

#[cfg(test)]
mod test_set_coeff_z {
    use crate::{integer::Z, integer_mod_q::PolyOverZq, traits::SetCoefficient};
    use std::str::FromStr;

    /// Ensure that the negative indices return an error.
    #[test]
    fn set_min_negative_coeff() {
        let mut poly = PolyOverZq::from_str("2  1 1 mod 11").unwrap();

        assert!(poly.set_coeff(i64::MIN, 2).is_err());
        assert!(poly.set_coeff(i32::MIN, 2).is_err());
        assert!(poly.set_coeff(i16::MIN, 2).is_err());
        assert!(poly.set_coeff(i8::MIN, 2).is_err());
    }

    /// Ensure that large coefficients work.
    #[test]
    fn set_coeff_big() {
        let mut poly = PolyOverZq::from_str("2  1 1 mod 11").unwrap();

        assert!(poly.set_coeff(2, i32::MAX,).is_ok());
        assert!(poly.set_coeff(2, i64::MAX).is_ok());
    }

    /// Ensure that the max of [`u8`] and [`u16`] works as an index.
    #[test]
    fn set_index_big() {
        let mut poly = PolyOverZq::from_str("2  1 1 mod 11").unwrap();

        assert!(poly.set_coeff(u8::MAX, 2).is_ok());
        assert!(poly.set_coeff(u16::MAX, 2).is_ok());
    }

    /// Ensure that a general case is working.
    #[test]
    fn set_coeff_working() {
        let mut poly = PolyOverZq::from_str("4  0 1 2 3 mod 11").unwrap();
        let value = 10000;

        poly.set_coeff(0, value).unwrap();
        poly.set_coeff(5, value).unwrap();
        assert_eq!(
            PolyOverZq::from_str("6  1 1 2 3 0 1  mod 11").unwrap(),
            poly
        );
    }

    /// Ensure that the correct coefficient is set and all others are set to `0`.
    #[test]
    fn set_coeff_rest_zero() {
        let mut poly = PolyOverZq::from_str("0 mod 11").unwrap();

        poly.set_coeff(4, -10).unwrap();
        assert_eq!(PolyOverZq::from_str("5  0 0 0 0 1 mod 11").unwrap(), poly);
    }

    /// Ensure that setting with a z works.
    #[test]
    fn set_coeff_z() {
        let mut poly = PolyOverZq::from_str("0 mod 11").unwrap();

        poly.set_coeff(4, Z::from(123)).unwrap();
        assert_eq!(PolyOverZq::from_str("5  0 0 0 0 2 mod 11").unwrap(), poly);
    }
}

/// we omit most of the tests for the correct values, since
/// the values itself are set with set_coeff taking in a [`Z`] value
#[cfg(test)]
mod test_set_coeff_zq {
    use crate::{
        integer_mod_q::{PolyOverZq, Zq},
        traits::SetCoefficient,
    };
    use std::str::FromStr;

    /// Ensure that an error is returned if the moduli do not match
    #[test]
    fn mismatching_moduli() {
        let mut poly = PolyOverZq::from_str(&format!("4  0 1 2 3 mod {}", u64::MAX - 58)).unwrap();
        let value = Zq::from((u64::MAX, u64::MAX - 57));

        assert!(poly.set_coeff(4, &value).is_err());
        assert_eq!(
            PolyOverZq::from_str(&format!("4  0 1 2 3 mod {}", u64::MAX - 58)).unwrap(),
            poly
        )
    }

    /// Ensure that an ok is returned if the moduli not match
    #[test]
    fn matching_moduli() {
        let mut poly = PolyOverZq::from_str(&format!("4  0 1 2 3 mod {}", u64::MAX - 58)).unwrap();
        let value = Zq::from((u64::MAX, u64::MAX - 58));

        assert!(poly.set_coeff(4, &value).is_ok());
        assert_eq!(
            PolyOverZq::from_str(&format!("5  0 1 2 3 58 mod {}", u64::MAX - 58)).unwrap(),
            poly
        )
    }
}
