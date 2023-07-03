// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to call the logarithm on a [`Z`] integer.

use crate::{error::MathError, integer::Z, rational::Q};
use flint_sys::fmpz::{fmpz_clog, fmpz_dlog, fmpz_flog};

impl Z {
    /// Computes the logarithm of a natural number (i.e. an integer greater than `0`)
    /// with a base greater than `1` rounded up.
    ///
    /// **Warning**: It assumes that the return value fits in an [`i64`].
    ///
    /// Parameters:
    /// - `base`: the base of the logarithm
    ///
    /// Returns $\lceil log_base(self) \rceil$ as a [`Z`] instance or a [`MathError`],
    /// if at least one of the conditions
    /// `base > 1` and `self > 0` isn't met.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(15);
    /// let log = value.log_ceil(4).unwrap();
    ///
    /// assert_eq!(Z::from(2), log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidBase`](MathError::InvalidBase) if the `base` is not greater than `1`.
    /// - Returns a [`MathError`] of type
    /// [`NotPositiveNumber`](MathError::NotPositiveNumber) if `self` is not
    ///  greater than `0`.
    pub fn log_ceil(&self, base: impl Into<Z>) -> Result<Z, MathError> {
        let base: Z = base.into();
        if base <= Z::ONE {
            Err(MathError::InvalidBase(format!(
                "The base must be greater than 1, but the provided is {}",
                base
            )))
        } else if self <= &Z::ZERO {
            Err(MathError::NotPositiveNumber(self.to_string()))
        } else {
            Ok(Z::from(unsafe { fmpz_clog(&self.value, &base.value) }))
        }
    }

    /// Computes the logarithm of a natural number (i.e. an integer greater than `0`)
    /// with a base greater than `1` rounded down.
    ///
    /// **Warning**: It assumes that the return value fits in an [`i64`].
    ///
    /// Parameters:
    /// - `base`: the base of the logarithm
    ///
    /// Returns $\lfloor log_base(self) \rfloor$ as a [`Z`] instance or a [`MathError`],
    /// if at least one of the conditions
    /// `base > 1` and `self > 0` isn't met.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(15);
    /// let log = value.log_floor(4).unwrap();
    ///
    /// assert_eq!(Z::from(1), log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidBase`](MathError::InvalidBase) if the `base` is not greater than `1`.
    /// - Returns a [`MathError`] of type
    /// [`NotPositiveNumber`](MathError::NotPositiveNumber) if `self` is not
    ///  greater than `0`.
    pub fn log_floor(&self, base: impl Into<Z>) -> Result<Z, MathError> {
        let base: Z = base.into();
        if base <= Z::ONE {
            Err(MathError::InvalidBase(format!(
                "The base must be greater than 1, but the provided is {}",
                base
            )))
        } else if self <= &Z::ZERO {
            Err(MathError::NotPositiveNumber(self.to_string()))
        } else {
            Ok(Z::from(unsafe { fmpz_flog(&self.value, &base.value) }))
        }
    }

    /// Computes the natural logarithm of a natural number
    /// (i.e. an integer greater than `0`)
    /// approximated as an [`f64`] and returned as a [`Q`].
    ///
    /// **Warning**: It assumes that the return value does not overflow an [`f64`].
    ///
    /// Returns the double precision approximation of the natural logarithm of `self`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::rational::Q;
    ///
    /// let value = Z::from(1);
    /// let log = value.ln().unwrap();
    ///
    /// assert_eq!(Q::ZERO, log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`NotPositiveNumber`](MathError::NotPositiveNumber) if `self` is not
    ///  greater than `0`.
    pub fn ln(&self) -> Result<Q, MathError> {
        if self <= &Z::ZERO {
            Err(MathError::NotPositiveNumber(self.to_string()))
        } else {
            Ok(Q::from(unsafe { fmpz_dlog(&self.value) }))
        }
    }

    /// Computes the logarithm of a natural number (i.e. an integer greater than `0`)
    /// with an integer base greater than `1` approximated as an [`f64`]
    /// and returned as a [`Q`].
    ///
    /// **Warning**: It assumes that the return value does not overflow an [`f64`].
    ///
    /// Parameters:
    /// - `base`: the base of the logarithm
    ///
    /// Returns $log_base(self)$ as a [`Q`] instance or a [`MathError`],
    /// if at least one of the conditions `base > 1` and `self > 0` isn't met.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::rational::Q;
    ///
    /// let value = Z::from(2);
    /// let log = value.log(2).unwrap();
    ///
    /// assert_eq!(Q::ONE, log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidBase`](MathError::InvalidBase)
    /// if the `base` is not greater than `1`.
    /// - Returns a [`MathError`] of type
    /// [`NotPositiveNumber`](MathError::NotPositiveNumber) if `self` is not
    ///  greater than `0`.
    pub fn log(&self, base: impl Into<Z>) -> Result<Q, MathError> {
        let base: Z = base.into();
        if base <= Z::ONE {
            return Err(MathError::InvalidBase(format!(
                "The base must be greater than 1, but the provided is {}",
                base
            )));
        }

        let ln_value = self.ln()?;
        let ln_base = base.ln()?;
        let log_b = ln_value / ln_base;

        Ok(log_b)
    }
}

#[cfg(test)]
mod test_log_ceil {
    use crate::integer::Z;

    /// Ensure that an error is returned if the base is too small
    #[test]
    fn base_too_small() {
        let value = Z::from(17);

        assert!(value.log_ceil(&Z::ZERO).is_err());
        assert!(value.log_ceil(&Z::ONE).is_err());
        assert!(value.log_ceil(&Z::MINUS_ONE).is_err());
        assert!(value.log_ceil(&Z::from(i64::MIN)).is_err());
    }

    /// Ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        let base = Z::from(2);

        assert!(Z::ZERO.log_ceil(&base).is_err());
        assert!(Z::MINUS_ONE.log_ceil(&base).is_err());
        assert!(Z::from(i64::MIN).log_ceil(&base).is_err());
    }

    /// Ensure that the value is rounded up
    #[test]
    fn rounded_up() {
        let base = Z::from(2);

        assert_eq!(Z::ZERO, Z::from(1).log_ceil(&base).unwrap());
        assert_eq!(Z::ONE, Z::from(2).log_ceil(&base).unwrap());
        assert_eq!(Z::from(2), Z::from(3).log_ceil(&base).unwrap());
        assert_eq!(Z::from(2), Z::from(4).log_ceil(&base).unwrap());
        assert_eq!(Z::from(64), Z::from(u64::MAX).log_ceil(&base).unwrap());
        assert_eq!(
            Z::from(32),
            Z::from(u64::MAX).log_ceil(&Z::from(4)).unwrap()
        );
    }

    /// Ensures that `log_ceil` is available for all important types
    /// that can be casted to a [`Z`] instance like u8, u16, i32, i64, ...
    #[test]
    fn availability() {
        let value = Z::from(5);

        let _ = value.log_ceil(&2_u8).unwrap();
        let _ = value.log_ceil(&2_u16).unwrap();
        let _ = value.log_ceil(&2_u32).unwrap();
        let _ = value.log_ceil(&2_u64).unwrap();
        let _ = value.log_ceil(&2_i8).unwrap();
        let _ = value.log_ceil(&2_i16).unwrap();
        let _ = value.log_ceil(&2_i32).unwrap();
        let _ = value.log_ceil(&2_i64).unwrap();
        let _ = value.log_ceil(&value).unwrap();
    }
}

#[cfg(test)]
mod test_log_floor {
    use crate::integer::Z;

    /// Ensure that an error is returned if the base is too small
    #[test]
    fn base_too_small() {
        let value = Z::from(17);

        assert!(value.log_floor(&Z::ZERO).is_err());
        assert!(value.log_floor(&Z::ONE).is_err());
        assert!(value.log_floor(&Z::MINUS_ONE).is_err());
        assert!(value.log_floor(&Z::from(i64::MIN)).is_err());
    }

    /// Ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        let base = Z::from(2);

        assert!(Z::ZERO.log_floor(&base).is_err());
        assert!(Z::MINUS_ONE.log_floor(&base).is_err());
        assert!(Z::from(i64::MIN).log_floor(&base).is_err());
    }

    /// Ensure that the value is rounded down
    #[test]
    fn rounded_down() {
        let base = Z::from(2);

        assert_eq!(Z::ZERO, Z::from(1).log_floor(&base).unwrap());
        assert_eq!(Z::ONE, Z::from(2).log_floor(&base).unwrap());
        assert_eq!(Z::ONE, Z::from(3).log_floor(&base).unwrap());
        assert_eq!(Z::from(2), Z::from(4).log_floor(&base).unwrap());
        assert_eq!(Z::from(63), Z::from(u64::MAX).log_floor(&base).unwrap());
        assert_eq!(
            Z::from(31),
            Z::from(u64::MAX).log_floor(&Z::from(4)).unwrap()
        );
    }

    /// Ensures that `log_floor` is available for types
    /// that can be casted to a [`Z`] instance like u8, u16, i32, i64, ...
    #[test]
    fn availability() {
        let value = Z::from(5);

        let _ = value.log_floor(&2_u8).unwrap();
        let _ = value.log_floor(&2_u16).unwrap();
        let _ = value.log_floor(&2_u32).unwrap();
        let _ = value.log_floor(&2_u64).unwrap();
        let _ = value.log_floor(&2_i8).unwrap();
        let _ = value.log_floor(&2_i16).unwrap();
        let _ = value.log_floor(&2_i32).unwrap();
        let _ = value.log_floor(&2_i64).unwrap();
        let _ = value.log_floor(&value).unwrap();
    }
}

#[cfg(test)]
mod test_natural_ln {
    use crate::{integer::Z, rational::Q};
    use std::f64::consts::{LN_10, LN_2};

    /// Ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        assert!(Z::ZERO.ln().is_err());
        assert!(Z::MINUS_ONE.ln().is_err());
        assert!(Z::from(i64::MIN).ln().is_err());
    }

    /// Ensure that the output of the function corresponds to the known
    /// approximated value in [`f64`]
    #[test]
    fn static_known_values() {
        assert_eq!(Q::ZERO, Z::ONE.ln().unwrap());
        assert_eq!(Q::from(LN_2), Z::from(2).ln().unwrap());
        assert_eq!(Q::from(LN_10), Z::from(10).ln().unwrap());
    }
}

#[cfg(test)]
mod test_log {
    use crate::{integer::Z, rational::Q, traits::Distance};

    /// Ensure that an error is returned if the base is too small
    #[test]
    fn base_too_small() {
        let value = Z::from(17);

        assert!(value.log(&Z::ZERO).is_err());
        assert!(value.log(&Z::ONE).is_err());
        assert!(value.log(&Z::MINUS_ONE).is_err());
        assert!(value.log(&Z::from(i64::MIN)).is_err());
    }

    /// Ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        let base = Z::from(2);

        assert!(Z::ZERO.log(&base).is_err());
        assert!(Z::MINUS_ONE.log(&base).is_err());
        assert!(Z::from(i64::MIN).log(&base).is_err());
    }

    /// Checks whether the logarithm computation works correctly for small values
    #[test]
    fn small_values() {
        let z_0 = Z::from(1);
        let z_1 = Z::from(2);
        let z_2 = Z::from(6);
        let z_3 = Z::from(9);
        let cmp_0 = Q::from(6_f64.log2());
        let cmp_1 = Q::from(2);
        let max_distance = Q::from((1, 1_000_000_000));

        let res_0 = z_0.log(&2).unwrap();
        let res_1 = z_1.log(&2).unwrap();
        let res_2 = z_2.log(&2).unwrap();
        let res_3 = z_3.log(&3).unwrap();

        assert_eq!(Q::ZERO, res_0);
        assert_eq!(Q::ONE, res_1);
        assert!(cmp_0.distance(res_2) < max_distance);
        assert!(cmp_1.distance(res_3) < max_distance);
    }

    /// Checks whether the logarithm computation works correctly for large values
    #[test]
    fn large_values() {
        let z_0 = Z::from(i64::MAX as u64 + 1);
        let z_1 = Z::from(i64::MAX);
        let z_2 = Z::from(i32::MAX);
        let cmp_0 = Q::from(63);
        let cmp_1 = Q::from((i64::MAX as f64).log2());
        let max_distance = Q::from((1, 1_000_000_000));

        let res_0 = z_0.log(&2).unwrap();
        let res_1 = z_1.log(&2).unwrap();
        let res_2 = z_2.log(&i32::MAX).unwrap();

        assert!(cmp_0.distance(res_0) < max_distance);
        assert!(cmp_1.distance(res_1) < max_distance);
        assert_eq!(Q::ONE, res_2);
    }

    /// Ensures that the logarithm function is available for all important types
    /// that can be casted to a [`Z`] instance like u8, u16, i32, i64, ...
    #[test]
    fn availability() {
        let value = Z::from(5);

        let _ = value.log(&2_u8).unwrap();
        let _ = value.log(&2_u16).unwrap();
        let _ = value.log(&2_u32).unwrap();
        let _ = value.log(&2_u64).unwrap();
        let _ = value.log(&2_i8).unwrap();
        let _ = value.log(&2_i16).unwrap();
        let _ = value.log(&2_i32).unwrap();
        let _ = value.log(&2_i64).unwrap();
        let _ = value.log(&value).unwrap();
    }
}
