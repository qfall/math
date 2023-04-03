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
    /// Computes the absolute distance between two [`Z`] instances.
    ///
    /// Parameters:
    /// - `other`: specifies one of the [`Z`] values whose distance
    /// is calculated to `self`
    ///
    /// Returns the absolute difference, i.e. distance between the two given [`Z`]
    /// instances as a new [`Z`] instance.
    ///
    /// # Example
    /// ```
    /// use math::integer::Z;
    ///
    /// let a = Z::from(-1);
    /// let b = Z::from(5);
    ///
    /// assert_eq!(Z::from(6), a.distance(&b));
    /// ```
    pub fn distance(&self, other: &Self) -> Z {
        let difference = self - other;
        difference.abs()
    }

    /// Returns the given [`Z`] instance with its absolute value.
    ///
    /// # Example
    /// ```
    /// use math::integer::Z;
    ///
    /// let value = Z::from(-1);
    ///
    /// assert_eq!(Z::ONE, value.abs());
    /// ```
    pub fn abs(mut self) -> Z {
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
mod test_distance {
    use super::Z;

    /// Checks if distance is correctly output for small [`Z`] values
    /// and whether distance(a,b) == distance(b,a), distance(a,a) == 0
    #[test]
    fn small_values() {
        let a = Z::ONE;
        let b = Z::from(-15);
        let zero = Z::ZERO;

        assert_eq!(Z::ONE, a.distance(&zero));
        assert_eq!(Z::ONE, zero.distance(&a));
        assert_eq!(Z::from(16), a.distance(&b));
        assert_eq!(Z::from(16), b.distance(&a));
        assert_eq!(Z::from(15), b.distance(&zero));
        assert_eq!(Z::from(15), zero.distance(&b));
        assert_eq!(Z::ZERO, b.distance(&b))
    }

    /// Checks if distance is correctly output for large [`Z`] values
    /// and whether distance(a,b) == distance(b,a), distance(a,a) == 0
    #[test]
    fn large_values() {
        let a = Z::from(i64::MAX);
        let b = Z::from(i64::MIN);
        let zero = Z::ZERO;

        assert_eq!(&a - &b, a.distance(&b));
        assert_eq!(&a - &b, b.distance(&a));
        assert_eq!(a, a.distance(&zero));
        assert_eq!(a, zero.distance(&a));
        assert_eq!(&a + Z::ONE, b.distance(&zero));
        assert_eq!(&a + Z::ONE, zero.distance(&b));
        assert_eq!(Z::ZERO, a.distance(&a));
    }
}
