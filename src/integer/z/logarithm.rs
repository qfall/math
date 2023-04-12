// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to call the logarithm on a [`Z`] integer.

use super::Z;
use crate::{error::MathError, rational::Q};
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
    /// # Example
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(15);
    /// let log = value.log_ceil(&Z::from(4)).unwrap();
    ///
    /// assert_eq!(Z::from(2), log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidBase`](MathError::InvalidBase) if the `base` is not greater than `1`.
    /// - Returns a [`MathError`] of type
    /// [`NotNaturalNumber`](MathError::NotNaturalNumber) if the `self` is not
    ///  greater than `0`.
    pub fn log_ceil(&self, base: &Z) -> Result<Z, MathError> {
        if base <= &Z::ONE {
            Err(MathError::InvalidBase(format!(
                "The base must be greater than 1, but the provided is {}",
                base
            )))
        } else if self <= &Z::ZERO {
            Err(MathError::NotNaturalNumber(self.to_string()))
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
    /// # Example
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(15);
    /// let log = value.log_floor(&Z::from(4)).unwrap();
    ///
    /// assert_eq!(Z::from(1), log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidBase`](MathError::InvalidBase) if the `base` is not greater than `1`.
    /// - Returns a [`MathError`] of type
    /// [`NotNaturalNumber`](MathError::NotNaturalNumber) if the `self` is not
    ///  greater than `0`.
    pub fn log_floor(&self, base: &Z) -> Result<Z, MathError> {
        if base <= &Z::ONE {
            Err(MathError::InvalidBase(format!(
                "The base must be greater than 1, but the provided is {}",
                base
            )))
        } else if self <= &Z::ZERO {
            Err(MathError::NotNaturalNumber(self.to_string()))
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
    /// # Example
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
    /// [`NotNaturalNumber`](MathError::NotNaturalNumber) if the `self` is not
    ///  greater than `0`.
    pub fn ln(&self) -> Result<Q, MathError> {
        if self <= &Z::ZERO {
            Err(MathError::NotNaturalNumber(self.to_string()))
        } else {
            Ok(Q::from(unsafe { fmpz_dlog(&self.value) }))
        }
    }
}

#[cfg(test)]
mod test_log_ceil {
    use crate::integer::Z;

    /// ensure that an error is returned if the base is too small
    #[test]
    fn base_too_small() {
        let value = Z::from(17);

        assert!(value.log_ceil(&Z::ZERO).is_err());
        assert!(value.log_ceil(&Z::ONE).is_err());
        assert!(value.log_ceil(&Z::MINUS_ONE).is_err());
        assert!(value.log_ceil(&Z::from(i64::MIN)).is_err());
    }

    /// ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        let base = Z::from(2);

        assert!(Z::ZERO.log_ceil(&base).is_err());
        assert!(Z::MINUS_ONE.log_ceil(&base).is_err());
        assert!(Z::from(i64::MIN).log_ceil(&base).is_err());
    }

    /// ensure that the value is rounded up
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
}

#[cfg(test)]
mod test_log_floor {
    use crate::integer::Z;

    /// ensure that an error is returned if the base is too small
    #[test]
    fn base_too_small() {
        let value = Z::from(17);

        assert!(value.log_floor(&Z::ZERO).is_err());
        assert!(value.log_floor(&Z::ONE).is_err());
        assert!(value.log_floor(&Z::MINUS_ONE).is_err());
        assert!(value.log_floor(&Z::from(i64::MIN)).is_err());
    }

    /// ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        let base = Z::from(2);

        assert!(Z::ZERO.log_floor(&base).is_err());
        assert!(Z::MINUS_ONE.log_floor(&base).is_err());
        assert!(Z::from(i64::MIN).log_floor(&base).is_err());
    }

    /// ensure that the value is rounded down
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
}

#[cfg(test)]
mod test_natural_ln {
    use crate::{integer::Z, rational::Q};
    use std::f64::consts::{LN_10, LN_2};

    /// ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        assert!(Z::ZERO.ln().is_err());
        assert!(Z::MINUS_ONE.ln().is_err());
        assert!(Z::from(i64::MIN).ln().is_err());
    }

    /// ensure that the output of the function corresponds to the known
    /// approximated value in [`f64`]
    #[test]
    fn static_known_values() {
        assert_eq!(Q::ZERO, Z::ONE.ln().unwrap());
        assert_eq!(Q::from(LN_2), Z::from(2).ln().unwrap());
        assert_eq!(Q::from(LN_10), Z::from(10).ln().unwrap());
    }
}
