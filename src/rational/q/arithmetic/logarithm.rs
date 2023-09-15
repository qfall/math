// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to call the logarithm on a [`Q`] integer.

use crate::{error::MathError, integer::Z, rational::Q};
use flint_sys::fmpz::fmpz_dlog;

impl Q {
    /// Computes the natural logarithm of a positive rational number
    /// approximated as an [`f64`] and returned as a [`Q`].
    ///
    /// **Warning**: It assumes that the return value does not overflow an [`f64`].
    ///
    /// Returns the double precision approximation of the natural logarithm of `self`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let value = Q::from(1);
    /// let log = value.ln().unwrap();
    ///
    /// assert_eq!(Q::ZERO, log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`NonPositive`](MathError::NonPositive) if `self` is not
    ///  greater than `0`.
    pub fn ln(&self) -> Result<Self, MathError> {
        if self <= &Q::ZERO {
            Err(MathError::NonPositive(self.to_string()))
        } else {
            Ok(Q::from(
                unsafe { fmpz_dlog(&self.value.num) } - unsafe { fmpz_dlog(&self.value.den) },
            ))
        }
    }

    /// Computes the logarithm of a positive rational number
    /// with an integer base greater than `1` approximated as an [`f64`]
    /// and returned as a [`Q`].
    ///
    /// **Warning**: It assumes that the return value does not overflow an [`f64`].
    ///
    /// Parameters:
    /// - `base`: the base of the logarithm
    ///
    /// Returns `log_base(self)` as a [`Q`] instance or a [`MathError`],
    /// if at least one of the conditions `base > 1` and `self > 0` isn't met.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let value = Q::from(2);
    /// let log = value.log(2).unwrap();
    ///
    /// assert_eq!(Q::ONE, log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if the `base` is not greater than `1`.
    /// - Returns a [`MathError`] of type
    /// [`NonPositive`](MathError::NonPositive) if `self` is not
    ///  greater than `0`.
    pub fn log(&self, base: impl Into<Z>) -> Result<Q, MathError> {
        let base: Z = base.into();
        if base <= Z::ONE {
            return Err(MathError::InvalidIntegerInput(format!(
                "The base must be greater than 1, but the provided is {base}"
            )));
        }

        let ln_value = self.ln()?;
        let ln_base = base.ln()?;
        let log_b = ln_value / ln_base;

        Ok(log_b)
    }
}

#[cfg(test)]
mod test_natural_ln {
    use crate::rational::Q;
    use std::f64::consts::{LN_10, LN_2};

    /// Ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        assert!(Q::ZERO.ln().is_err());
        assert!(Q::MINUS_ONE.ln().is_err());
        assert!(Q::from(i64::MIN).ln().is_err());
    }

    /// Ensure that the output of the function corresponds to the known
    /// approximated value in [`f64`]
    #[test]
    fn static_known_values() {
        assert_eq!(Q::ZERO, Q::ONE.ln().unwrap());
        assert_eq!(Q::from(LN_2), Q::from(2).ln().unwrap());
        assert_eq!(Q::from(LN_10), Q::from(10).ln().unwrap());
        assert_eq!(Q::ONE, Q::E.ln().unwrap());
    }
}

#[cfg(test)]
mod test_log {
    use crate::{integer::Z, rational::Q, traits::Distance};

    /// Ensure that an error is returned if the base is too small
    #[test]
    fn base_too_small() {
        let value = Q::from(17);

        assert!(value.log(Z::ZERO).is_err());
        assert!(value.log(Z::ONE).is_err());
        assert!(value.log(Z::MINUS_ONE).is_err());
        assert!(value.log(Z::from(i64::MIN)).is_err());
    }

    /// Ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        let base = Z::from(2);

        assert!(Q::ZERO.log(&base).is_err());
        assert!(Q::MINUS_ONE.log(&base).is_err());
        assert!(Q::from(i64::MIN).log(&base).is_err());
    }

    /// Checks whether the logarithm computation works correctly for small values
    #[test]
    fn small_values() {
        let z_0 = Q::from(1);
        let z_1 = Q::from(2);
        let z_2 = Q::from(1.25f64);
        let z_3 = Q::from(20.75f64);
        let cmp_0 = Q::from(1.25_f64.log2());
        let cmp_1 = Q::from(20.75f64.log(3f64));
        let max_distance = Q::from((1, 1_000_000_000));

        let res_0 = z_0.log(2).unwrap();
        let res_1 = z_1.log(2).unwrap();
        let res_2 = z_2.log(2).unwrap();
        let res_3 = z_3.log(3).unwrap();

        assert_eq!(Q::ZERO, res_0);
        assert_eq!(Q::ONE, res_1);
        assert!(cmp_0.distance(res_2) < max_distance);
        assert!(cmp_1.distance(res_3) < max_distance);
    }

    /// Checks whether the logarithm computation works correctly for large values
    #[test]
    fn large_values() {
        let z_0 = Q::from(i64::MAX as u64 + 1);
        let z_1 = Q::from(f64::MAX);
        let z_2 = Q::from(i32::MAX);
        let cmp_0 = Q::try_from((&63, &1)).unwrap();
        let cmp_1 = Q::from(f64::MAX.log2());
        let max_distance = Q::try_from((&1, &1_000_000_000)).unwrap();

        let res_0 = z_0.log(2).unwrap();
        let res_1 = z_1.log(2).unwrap();
        let res_2 = z_2.log(i32::MAX).unwrap();

        assert!(cmp_0.distance(res_0) < max_distance);
        assert!(cmp_1.distance(res_1) < max_distance);
        assert_eq!(Q::ONE, res_2);
    }

    /// Ensures that the logarithm function is available for types
    /// that can be casted to a [`Z`] instance like u8, u16, i32, i64, ...
    #[test]
    fn availability() {
        let value = Z::from(5);

        let _ = value.log(2u8).unwrap();
        let _ = value.log(2u16).unwrap();
        let _ = value.log(2u32).unwrap();
        let _ = value.log(2u64).unwrap();
        let _ = value.log(2i8).unwrap();
        let _ = value.log(2i16).unwrap();
        let _ = value.log(2i32).unwrap();
        let _ = value.log(2i64).unwrap();
        let _ = value.log(&value).unwrap();
    }
}
