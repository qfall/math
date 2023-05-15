// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`Q`] instances.

use super::Q;
use flint_sys::fmpq::{fmpq_abs, fmpq_inv, fmpq_is_one, fmpq_is_zero};

impl Q {
    /// Returns the given [`Q`] instance with its absolute value.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// let mut value = Q::from(-1);
    ///
    /// let value = value.abs();
    ///
    /// assert_eq!(Q::ONE, value);
    /// ```
    pub fn abs(mut self) -> Self {
        unsafe {
            fmpq_abs(&mut self.value, &self.value);
        }
        self
    }

    /// Returns the inverse of `self` as a fresh [`Q`] instance.
    ///
    /// As the inverse of `0` is undefined, it returns `None` in case `self == 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// let value = Q::from(4);
    ///
    /// let inverse = value.inverse().unwrap();
    ///
    /// assert_eq!(Q::try_from((&1, &4)).unwrap(), inverse);
    /// ```
    pub fn inverse(&self) -> Option<Q> {
        if self == &Q::ZERO {
            return None;
        }

        let mut out = Q::ZERO;
        unsafe { fmpq_inv(&mut out.value, &self.value) };
        Some(out)
    }

    /// Checks if a [`Q`] is `0`.
    ///
    /// Returns true if the value is `0`.
    ///
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let value = Q::from(0);
    /// assert!(value.is_zero())
    /// ```
    pub fn is_zero(&self) -> bool {
        1 == unsafe { fmpq_is_zero(&self.value) }
    }

    /// Checks if a [`Q`] is `1`.
    ///
    /// Returns true if the value is `1`.
    ///
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let value = Q::from(1);
    /// assert!(value.is_one())
    /// ```
    pub fn is_one(&self) -> bool {
        1 == unsafe { fmpq_is_one(&self.value) }
    }
}

#[cfg(test)]
mod test_abs {
    use super::Q;

    /// Checks whether `abs` returns the positive value for small values correctly
    #[test]
    fn small_values() {
        let pos = Q::ONE;
        let zero = Q::ZERO;
        let neg = Q::from(-15);

        assert_eq!(Q::ONE, pos.abs());
        assert_eq!(Q::ZERO, zero.abs());
        assert_eq!(Q::from(15), neg.abs());
    }

    /// Checks whether `abs` returns the positive value for large values correctly
    #[test]
    fn large_values() {
        let pos = Q::from(i64::MAX);
        let neg = Q::try_from((&1, &i64::MIN)).unwrap();

        assert_eq!(Q::from(i64::MAX), pos.abs());
        assert_eq!(
            Q::try_from((&1, &i64::MIN)).unwrap() * Q::from(-1),
            neg.abs()
        );
    }
}

#[cfg(test)]
mod test_inv {
    use super::Q;

    /// Checks whether the inverse is correctly computed for small values
    #[test]
    fn small_values() {
        let val_0 = Q::from(4);
        let val_1 = Q::try_from((&2, &-7)).unwrap();

        let inv_0 = val_0.inverse().unwrap();
        let inv_1 = val_1.inverse().unwrap();

        assert_eq!(Q::try_from((&1, &4)).unwrap(), inv_0);
        assert_eq!(Q::try_from((&-7, &2)).unwrap(), inv_1);
    }

    /// Checks whether the inverse is correctly computed for large values
    #[test]
    fn large_values() {
        let val_0 = Q::try_from((&1, &i64::MAX)).unwrap();
        let val_1 = Q::from(i64::MIN);

        let inv_0 = val_0.inverse().unwrap();
        let inv_1 = val_1.inverse().unwrap();

        assert_eq!(Q::from(i64::MAX), inv_0);
        assert_eq!(Q::try_from((&1, &i64::MIN)).unwrap(), inv_1);
    }

    /// Checks whether the inverse of `0` returns `None`
    #[test]
    fn inv_zero_none() {
        let zero = Q::ZERO;

        let inv_zero = zero.inverse();

        assert!(inv_zero.is_none());
    }
}

#[cfg(test)]
mod test_is_zero {
    use super::Q;
    use std::str::FromStr;

    /// ensure that is_zero returns `true` for `0`
    #[test]
    fn zero_detection() {
        let zero = Q::from(0);

        assert!(zero.is_zero());
    }

    /// ensure that is_zero returns `false` for non-zero values
    #[test]
    fn zero_rejection() {
        let small = Q::from(2);
        let large = Q::from_str(&format!("{}", (u128::MAX - 1) / 2 + 1)).unwrap();

        assert!(!(small.is_zero()));
        assert!(!(large.is_zero()));
    }
}

#[cfg(test)]
mod test_is_one {
    use super::Q;
    use std::str::FromStr;

    /// ensure that is_one returns `true` for `1`
    #[test]
    fn one_detection() {
        let zero = Q::from(1);

        assert!(zero.is_one());
    }

    /// ensure that is_one returns `false` for other values
    #[test]
    fn one_rejection() {
        let small = Q::from(2);
        let large = Q::from_str(&format!("1/{}", (u128::MAX - 1) / 2 + 2)).unwrap();

        assert!(!(small.is_one()));
        assert!(!(large.is_one()));
    }
}
