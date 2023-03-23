// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to set coefficients for a [`PolyOverQ`] value from other types.
//! Each reasonable type should be used to set a coefficient.

use super::PolyOverQ;
use crate::{
    error::MathError,
    integer::Z,
    macros::for_others::{implement_for_others, implement_for_owned},
    rational::Q,
    traits::SetCoefficient,
    utils::coordinate::evaluate_coordinate,
};
use flint_sys::fmpq_poly::{fmpq_poly_set_coeff_fmpq, fmpq_poly_set_coeff_fmpz};
use std::fmt::Display;

impl SetCoefficient<&Z> for PolyOverQ {
    /// Sets the coefficient of a polynomial [`PolyOverQ`].
    /// We advise to use small coefficients, since already 2^32 coefficients take space
    /// of roughly 34 GB. If not careful, be prepared that memory problems can occur, if
    /// the coordinate is very high.
    ///
    /// All entries which are not directly addressed are automatically treated as zero.
    ///
    /// Parameters:
    /// - `coordinate`: the coordinate of the coefficient to set (has to be positive)
    /// - `value`: the new value the coordinate should have from a borrowed [`Z`].
    ///
    /// # Example
    /// ```
    /// use math::rational::PolyOverQ;
    /// use math::integer::Z;
    /// use math::traits::SetCoefficient;
    /// use std::str::FromStr;
    ///
    /// let mut poly = PolyOverQ::from_str("4  0 1 2/3 3/17").unwrap();
    /// let value = Z::from(1000);
    ///
    /// assert!(poly.set_coeff(4, &value).is_ok());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the coordinate is negative or it does not fit into an [`i64`].
    fn set_coeff(
        &mut self,
        coordinate: impl TryInto<i64> + Display + Copy,
        value: &Z,
    ) -> Result<(), MathError> {
        let coordinate = evaluate_coordinate(coordinate)?;

        unsafe {
            fmpq_poly_set_coeff_fmpz(&mut self.poly, coordinate, &value.value);
        };
        Ok(())
    }
}

impl SetCoefficient<&Q> for PolyOverQ {
    /// Sets the coefficient of a polynomial [`PolyOverQ`].
    /// We advise to use small coefficients, since already 2^32 coefficients take space
    /// of roughly 34 GB. If not careful, be prepared that memory problems can occur, if
    /// the coordinate is very high.
    ///
    /// All entries which are not directly addressed are automatically treated as zero.
    ///
    /// Parameters:
    /// - `coordinate`: the coordinate of the coefficient to set (has to be positive)
    /// - `value`: the new value the coordinate should have from a borrowed [`Q`].
    ///
    /// # Example
    /// ```
    /// use math::rational::PolyOverQ;
    /// use math::rational::Q;
    /// use math::traits::SetCoefficient;
    /// use std::str::FromStr;
    ///
    /// let mut poly = PolyOverQ::from_str("4  0 1 2/3 3/17").unwrap();
    /// let value = Q::from_str("3/17").unwrap();
    ///
    /// assert!(poly.set_coeff(4, &value).is_ok());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the coordinate is negative or it does not fit into an [`i64`].
    fn set_coeff(
        &mut self,
        coordinate: impl TryInto<i64> + Display + Copy,
        value: &Q,
    ) -> Result<(), MathError> {
        let coordinate = evaluate_coordinate(coordinate)?;

        unsafe {
            fmpq_poly_set_coeff_fmpq(&mut self.poly, coordinate, &value.value);
        };
        Ok(())
    }
}

implement_for_others!(Z, PolyOverQ, SetCoefficient for i8 i16 i32 i64 u8 u16 u32 u64);
implement_for_owned!(Z, PolyOverQ, SetCoefficient);
implement_for_owned!(Q, PolyOverQ, SetCoefficient);

#[cfg(test)]
mod test_set_coeff_z {

    use crate::{integer::Z, rational::PolyOverQ, traits::SetCoefficient};
    use std::str::FromStr;

    /// ensure that the negative coordinates return an error
    #[test]
    fn set_min_negative_coeff() {
        let mut poly = PolyOverQ::from_str("2  -1 3/17").unwrap();

        assert!(poly.set_coeff(i64::MIN, 2).is_err());
        assert!(poly.set_coeff(i32::MIN, 2).is_err());
        assert!(poly.set_coeff(i16::MIN, 2).is_err());
        assert!(poly.set_coeff(i8::MIN, 2).is_err());
    }

    /// ensure that coefficients up to 2^15 -1 work
    #[test]
    fn set_max_coeff() {
        let mut poly = PolyOverQ::from_str("2  -1 3/17").unwrap();

        assert!(poly.set_coeff(i8::MAX, 2).is_ok());
        assert!(poly.set_coeff(i16::MAX, 2).is_ok());
    }

    /// ensure that the max of [`u8`] and [`u16`] works as a coefficient
    #[test]
    fn set_unsigned_coeff() {
        let mut poly = PolyOverQ::from_str("2  -1 3/17").unwrap();

        assert!(poly.set_coeff(u8::MAX, 2).is_ok());
        assert!(poly.set_coeff(u16::MAX, 2).is_ok());
    }

    /// ensure that a general case is working
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

    /// ensure that the correct coefficient is set and all others are set to `0`
    #[test]
    fn set_coeff_rest_zero() {
        let mut poly = PolyOverQ::from_str("0").unwrap();

        poly.set_coeff(4, -10).unwrap();
        assert_eq!(PolyOverQ::from_str("5  0 0 0 0 -10").unwrap(), poly);
    }

    /// ensure that setting with a [`Z`] works
    #[test]
    fn set_coeff_z() {
        let mut poly = PolyOverQ::from_str("0").unwrap();

        poly.set_coeff(4, Z::from(123)).unwrap();
        poly.set_coeff(5, &Z::from(321)).unwrap();
        assert_eq!(PolyOverQ::from_str("6  0 0 0 0 123 321").unwrap(), poly);
    }

    /// ensure that setting large coefficients works
    #[test]
    fn large_coeff_z() {
        let mut poly = PolyOverQ::from_str("0").unwrap();

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

    /// ensure that setting with a large [`Q`] works
    #[test]
    fn large_coeff() {
        let mut poly = PolyOverQ::from_str("1  1").unwrap();
        let q = Q::from_str(&format!("{}/{}", u64::MAX - 1, u64::MAX)).unwrap();

        poly.set_coeff(2, &q).unwrap();

        assert_eq!(q, poly.get_coeff(2).unwrap());
        assert_eq!(
            PolyOverQ::from_str(&format!("3  1 0 {}/{}", u64::MAX - 1, u64::MAX)).unwrap(),
            poly
        )
    }
}
