// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to call the logarithm on a [`Z`] integer.

use flint_sys::fmpz::{fmpz_clog, fmpz_dlog, fmpz_flog};

use super::Z;
use crate::error::MathError;

impl Z {
    /// Computes the logarithm on a natural number (i.e. an integer greater than `0`)
    /// with a base greater than `1` rounded up.
    ///
    /// **Warning**: It assumes that the return value fits in an [`i64`].
    ///
    /// Parameters:
    /// - `b`: the base of the logarithm
    ///
    /// Returns $\lceil log_b(self) \rceil$.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(15);
    /// let log = value.logarithm_ceil(&Z::from(4)).unwrap();
    ///
    /// assert_eq!(Z::from(2), log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidBase`](MathError::InvalidBase) if the base `b` is not greater than `1`.
    /// - Returns a [`MathError`] of type
    /// [`NatNaturalNumber`](MathError::NotNaturalNumber) if the `self` is not
    ///  greater than `0`.
    pub fn logarithm_ceil(&self, b: &Z) -> Result<Z, MathError> {
        if b <= &Z::ONE {
            Err(MathError::InvalidBase(format!(
                "The base must be greater than 1, but the provided is {}",
                b
            )))
        } else if self <= &Z::ZERO {
            Err(MathError::NotNaturalNumber(self.to_string()))
        } else {
            Ok(Z::from(unsafe { fmpz_clog(&self.value, &b.value) }))
        }
    }

    /// Computes the logarithm on a natural number (i.e. an integer greater than `0`)
    /// with a base greater than `1` rounded down.
    ///
    /// **Warning**: It assumes that the return value fits in an [`i64`].
    ///
    /// Parameters:
    /// - `b`: the base of the logarithm
    ///
    /// Returns $\lfloor log_b(self) \rfloor$.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(15);
    /// let log = value.logarithm_floor(&Z::from(4)).unwrap();
    ///
    /// assert_eq!(Z::from(1), log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidBase`](MathError::InvalidBase) if the base `b` is not greater than `1`.
    /// - Returns a [`MathError`] of type
    /// [`NatNaturalNumber`](MathError::NotNaturalNumber) if the `self` is not
    ///  greater than `0`.
    pub fn logarithm_floor(&self, b: &Z) -> Result<Z, MathError> {
        if b <= &Z::ONE {
            Err(MathError::InvalidBase(format!(
                "The base must be greater than 1, but the provided is {}",
                b
            )))
        } else if self <= &Z::ZERO {
            Err(MathError::NotNaturalNumber(self.to_string()))
        } else {
            Ok(Z::from(unsafe { fmpz_flog(&self.value, &b.value) }))
        }
    }

    /// Computes the natural logarithm on a natural number
    /// (i.e. an integer greater than `0`)
    /// approximated as an [`f64`].
    ///
    /// Returns the double precision approximation of the natural logarithm of `self`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(1);
    /// let log = value.logarithm_double().unwrap();
    ///
    /// assert_eq!(0_f64, log);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`NatNaturalNumber`](MathError::NotNaturalNumber) if the `self` is not
    ///  greater than `0`.
    pub fn logarithm_double(&self) -> Result<f64, MathError> {
        if self <= &Z::ZERO {
            Err(MathError::NotNaturalNumber(self.to_string()))
        } else {
            Ok(unsafe { fmpz_dlog(&self.value) })
        }
    }
}

#[cfg(test)]
mod test_logarithm_ceil {
    use crate::integer::Z;

    /// ensure that an error is returned if the base is too small
    #[test]
    fn base_too_small() {
        let value = Z::from(17);

        assert!(value.logarithm_ceil(&Z::ZERO).is_err());
        assert!(value.logarithm_ceil(&Z::ONE).is_err());
        assert!(value.logarithm_ceil(&Z::MINUS_ONE).is_err());
        assert!(value.logarithm_ceil(&Z::from(i64::MIN)).is_err());
    }

    /// ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        let base = Z::from(2);

        assert!(Z::ZERO.logarithm_ceil(&base).is_err());
        assert!(Z::MINUS_ONE.logarithm_ceil(&base).is_err());
        assert!(Z::from(i64::MIN).logarithm_ceil(&base).is_err());
    }

    /// ensure that the value is rounded up
    #[test]
    fn rounded_up() {
        let base = Z::from(2);

        assert_eq!(Z::ZERO, Z::from(1).logarithm_ceil(&base).unwrap());
        assert_eq!(Z::ONE, Z::from(2).logarithm_ceil(&base).unwrap());
        assert_eq!(Z::from(2), Z::from(3).logarithm_ceil(&base).unwrap());
        assert_eq!(Z::from(2), Z::from(4).logarithm_ceil(&base).unwrap());
        assert_eq!(
            Z::from(64),
            Z::from(u64::MAX).logarithm_ceil(&base).unwrap()
        );
        assert_eq!(
            Z::from(32),
            Z::from(u64::MAX).logarithm_ceil(&Z::from(4)).unwrap()
        );
    }
}

#[cfg(test)]
mod test_logarithm_floor {
    use crate::integer::Z;

    /// ensure that an error is returned if the base is too small
    #[test]
    fn base_too_small() {
        let value = Z::from(17);

        assert!(value.logarithm_floor(&Z::ZERO).is_err());
        assert!(value.logarithm_floor(&Z::ONE).is_err());
        assert!(value.logarithm_floor(&Z::MINUS_ONE).is_err());
        assert!(value.logarithm_floor(&Z::from(i64::MIN)).is_err());
    }

    /// ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        let base = Z::from(2);

        assert!(Z::ZERO.logarithm_floor(&base).is_err());
        assert!(Z::MINUS_ONE.logarithm_floor(&base).is_err());
        assert!(Z::from(i64::MIN).logarithm_floor(&base).is_err());
    }

    /// ensure that the value is rounded up
    #[test]
    fn rounded_up() {
        let base = Z::from(2);

        assert_eq!(Z::ZERO, Z::from(1).logarithm_floor(&base).unwrap());
        assert_eq!(Z::ONE, Z::from(2).logarithm_floor(&base).unwrap());
        assert_eq!(Z::ONE, Z::from(3).logarithm_floor(&base).unwrap());
        assert_eq!(Z::from(2), Z::from(4).logarithm_floor(&base).unwrap());
        assert_eq!(
            Z::from(63),
            Z::from(u64::MAX).logarithm_floor(&base).unwrap()
        );
        assert_eq!(
            Z::from(31),
            Z::from(u64::MAX).logarithm_floor(&Z::from(4)).unwrap()
        );
    }
}

#[cfg(test)]
mod test_natural_logarithm_double {
    use std::f64::consts::{LN_10, LN_2};

    use crate::integer::Z;

    /// ensure that an error is returned if `self` is too small
    #[test]
    fn value_too_small() {
        assert!(Z::ZERO.logarithm_double().is_err());
        assert!(Z::MINUS_ONE.logarithm_double().is_err());
        assert!(Z::from(i64::MIN).logarithm_double().is_err());
    }

    /// ensure that the output of the function corresponds to the known
    /// approximated value in [`f64`]
    #[test]
    fn static_known_values() {
        assert_eq!(0_f64, Z::ONE.logarithm_double().unwrap());
        assert_eq!(LN_2, Z::from(2).logarithm_double().unwrap());
        assert_eq!(LN_10, Z::from(10).logarithm_double().unwrap());
    }
}
