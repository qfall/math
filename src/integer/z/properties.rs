// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`Z`] instances.

use super::Z;
use flint_sys::fmpz::fmpz_abs;

impl Z {
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
