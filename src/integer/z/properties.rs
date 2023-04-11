// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`Z`] instances.

use super::Z;
use flint_sys::fmpz::{fmpz_abs, fmpz_is_prime};

impl Z {
    /// Checks if a [`Z`] is prime.
    ///
    /// Returns true if the value is prime.
    ///
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(17);
    /// assert!(value.is_prime())
    /// ```
    pub fn is_prime(&self) -> bool {
        1 == unsafe { fmpz_is_prime(&self.value) }
    }

    /// Returns the given [`Z`] instance with its absolute value.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(-1);
    ///
    /// assert_eq!(Z::ONE, value.abs());
    /// ```
    pub fn abs(mut self) -> Self {
        unsafe {
            fmpz_abs(&mut self.value, &self.value);
        }
        self
    }
}

#[cfg(test)]
mod test_abs {
    use super::Z;

    /// Checks whether `abs` returns the positive value for small values correctly
    #[test]
    fn small_values() {
        let pos = Z::ONE;
        let zero = Z::ZERO;
        let neg = Z::from(-15);

        assert_eq!(Z::ONE, pos.abs());
        assert_eq!(Z::ZERO, zero.abs());
        assert_eq!(Z::from(15), neg.abs());
    }

    /// Checks whether `abs` returns the positive value for large values correctly
    #[test]
    fn large_values() {
        let pos = Z::from(i64::MAX);
        let neg = Z::from(i64::MIN);

        assert_eq!(Z::from(i64::MAX), pos.abs());
        assert_eq!(Z::from(i64::MIN) * Z::from(-1), neg.abs());
    }
}

#[cfg(test)]
mod test_is_prime {
    use super::Z;

    /// ensure that primes are correctly detected
    #[test]
    fn prime_detection() {
        let small = Z::from(2_i32.pow(16) + 1);
        let large = Z::from(u64::MAX - 58);
        assert!(small.is_prime());
        assert!(large.is_prime());
    }

    /// ensure that non-primes are correctly detected
    #[test]
    fn non_prime_detection() {
        let small = Z::from(2_i32.pow(16));
        let large = Z::from(i64::MAX);
        assert!(!small.is_prime());
        assert!(!large.is_prime());
    }
}
