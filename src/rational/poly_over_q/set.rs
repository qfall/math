// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to manipulate a [`PolyOverQ`] polynomial.

use super::PolyOverQ;
use crate::{error::MathError, rational::Q, traits::SetCoefficient, utils::index::evaluate_index};
use flint_sys::fmpq_poly::fmpq_poly_set_coeff_fmpq;
use std::fmt::Display;

impl<Rational: Into<Q>> SetCoefficient<Rational> for PolyOverQ {
    /// Sets the coefficient of a polynomial [`PolyOverQ`].
    /// We advise to use small coefficients, since already 2^32 coefficients take space
    /// of roughly 34 GB. If not careful, be prepared that memory problems can occur, if
    /// the index is very high.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to set (has to be positive)
    /// - `value`: the new value the index should have
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if either the index is negative
    /// or it does not fit into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use qfall_math::rational::Q;
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let mut poly = PolyOverQ::from_str("4  0 1 2/3 3/17").unwrap();
    /// let value = Q::from((3, 17));
    ///
    /// assert!(poly.set_coeff(4, &value).is_ok());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    ///     either the index is negative or it does not fit into an [`i64`].
    fn set_coeff(
        &mut self,
        index: impl TryInto<i64> + Display,
        value: Rational,
    ) -> Result<(), MathError> {
        let value = value.into();
        let index = evaluate_index(index)?;

        unsafe {
            fmpq_poly_set_coeff_fmpq(&mut self.poly, index, &value.value);
        };
        Ok(())
    }
}

#[cfg(test)]
mod test_set_coeff_z {
    use crate::{integer::Z, rational::PolyOverQ, traits::SetCoefficient};
    use std::str::FromStr;

    /// Ensure that the negative indices return an error.
    #[test]
    fn set_min_negative_coeff() {
        let mut poly = PolyOverQ::from_str("2  -1 3/17").unwrap();

        assert!(poly.set_coeff(i64::MIN, 2).is_err());
        assert!(poly.set_coeff(i32::MIN, 2).is_err());
        assert!(poly.set_coeff(i16::MIN, 2).is_err());
        assert!(poly.set_coeff(i8::MIN, 2).is_err());
    }

    /// Ensure that large coefficients work.
    #[test]
    fn set_coeff_large() {
        let mut poly = PolyOverQ::from_str("2  -1 3/17").unwrap();

        assert!(poly.set_coeff(2, i32::MAX).is_ok());
        assert!(poly.set_coeff(2, i64::MAX).is_ok());
    }

    /// Ensure that the max of [`u8`] and [`u16`] works as an index.
    #[test]
    fn set_index_large() {
        let mut poly = PolyOverQ::from_str("2  -1 3/17").unwrap();

        assert!(poly.set_coeff(u8::MAX, 2).is_ok());
        assert!(poly.set_coeff(u16::MAX, 2).is_ok());
    }

    /// Ensure that a general case is working.
    #[test]
    fn set_coeff_working() {
        let mut poly = PolyOverQ::from_str("4  0 -1 2 3/17").unwrap();
        let value = 10000;

        poly.set_coeff(0, value).unwrap();
        poly.set_coeff(5, value).unwrap();
        assert_eq!(
            PolyOverQ::from_str("6  10000 -1 2 3/17 0 10000").unwrap(),
            poly
        );
    }

    /// Ensure that the correct coefficient is set and all others are set to `0`.
    #[test]
    fn set_coeff_rest_zero() {
        let mut poly = PolyOverQ::default();

        poly.set_coeff(4, -10).unwrap();
        assert_eq!(PolyOverQ::from_str("5  0 0 0 0 -10").unwrap(), poly);
    }

    /// Ensure that setting with a [`Z`] works.
    #[test]
    fn set_coeff_z() {
        let mut poly = PolyOverQ::default();

        poly.set_coeff(4, Z::from(123)).unwrap();
        poly.set_coeff(5, &Z::from(321)).unwrap();
        assert_eq!(PolyOverQ::from_str("6  0 0 0 0 123 321").unwrap(), poly);
    }

    /// Ensure that setting large coefficients works.
    #[test]
    fn large_coeff_z() {
        let mut poly = PolyOverQ::default();

        poly.set_coeff(4, u64::MAX).unwrap();
        assert_eq!(
            PolyOverQ::from_str(&format!("5  0 0 0 0 {}", u64::MAX)).unwrap(),
            poly
        );
    }
}

#[cfg(test)]
mod test_set_coeff_q {
    use crate::{
        rational::{PolyOverQ, Q},
        traits::{GetCoefficient, SetCoefficient},
    };
    use std::str::FromStr;

    /// Ensure that setting with a large [`Q`] works
    #[test]
    fn large_coeff() {
        let mut poly = PolyOverQ::from_str("1  1").unwrap();
        let q = Q::from((u64::MAX - 1, u64::MAX));

        poly.set_coeff(2, &q).unwrap();

        assert_eq!(q, poly.get_coeff(2).unwrap());
        assert_eq!(
            PolyOverQ::from_str(&format!("3  1 0 {}/{}", u64::MAX - 1, u64::MAX)).unwrap(),
            poly
        )
    }
}
