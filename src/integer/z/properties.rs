// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`Z`] instances.

use super::Z;
use crate::rational::Q;
use flint_sys::{
    fmpq::{fmpq, fmpq_inv},
    fmpz::{fmpz, fmpz_abs, fmpz_bits, fmpz_is_prime},
};

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
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let mut value = Z::from(-1);
    ///
    /// let value = value.abs();
    ///
    /// assert_eq!(Z::ONE, value);
    /// ```
    pub fn abs(mut self) -> Self {
        unsafe {
            fmpz_abs(&mut self.value, &self.value);
        }
        self
    }

    /// Returns the inverse of `self` as a fresh [`Q`] instance.
    ///
    /// As the inverse of `0` is undefined, it returns `None` in case `self == 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::Z, rational::Q};
    /// let value = Z::from(4);
    ///
    /// let inverse = value.inverse().unwrap();
    ///
    /// assert_eq!(Q::try_from((&1, &4)).unwrap(), inverse);
    /// ```
    pub fn inverse(&self) -> Option<Q> {
        if self == &Z::ZERO {
            return None;
        }

        let mut out = Q::ZERO;
        // the manual construction of fmpq removes the need to clone self's value/
        // the numerator. the new fmpz value does not need to be cleared manually
        // as it's small the fmpq instance does neither as the fmpq value is
        // dropped automatically, but the numerator/ self's value is kept alive
        let self_fmpq = fmpq {
            num: self.value,
            den: fmpz(1),
        };
        unsafe { fmpq_inv(&mut out.value, &self_fmpq) };
        Some(out)
    }

    /// Computes the number of bits needed to store the absolute value of `self`.
    ///
    /// The number of bits needs to fit into an [`u64`],
    /// i.e. the size should not exceed `2^(2^64)`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let value = Z::from(4);
    ///
    /// let nr_bits = value.bits();
    ///
    /// assert_eq!(3, nr_bits);
    /// ```
    pub fn bits(&self) -> u64 {
        unsafe { fmpz_bits(&self.value) }
    }
}

#[cfg(test)]
mod test_bits {
    use super::Z;

    /// Checks whether the number of bits needed to store the absolute value
    /// is output correctly for small values
    #[test]
    fn small_values() {
        assert_eq!(0, Z::ZERO.bits());
        assert_eq!(1, Z::ONE.bits());
        assert_eq!(1, Z::MINUS_ONE.bits());
        assert_eq!(3, Z::from(4).bits());
        assert_eq!(31, Z::from(i32::MAX).bits());
        assert_eq!(32, Z::from(i32::MIN).bits());
        assert_eq!(32, Z::from(u32::MAX).bits());
    }

    /// Checks whether the number of bits needed to store the absolute value
    /// is output correctly for large values
    #[test]
    fn large_values() {
        let vector = vec![255; 16];
        let large = Z::from_bytes(&vector);

        assert_eq!(128, large.bits());
        assert_eq!(63, Z::from(i64::MAX).bits());
        assert_eq!(64, Z::from(i64::MIN).bits());
        assert_eq!(64, Z::from(u64::MAX).bits());
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

    /// Ensure that primes are correctly detected
    #[test]
    fn prime_detection() {
        let small = Z::from(2_i32.pow(16) + 1);
        let large = Z::from(u64::MAX - 58);
        assert!(small.is_prime());
        assert!(large.is_prime());
    }

    /// Ensure that non-primes are correctly detected
    #[test]
    fn non_prime_detection() {
        let small = Z::from(2_i32.pow(16));
        let large = Z::from(i64::MAX);
        assert!(!small.is_prime());
        assert!(!large.is_prime());
    }
}

#[cfg(test)]
mod test_inv {
    use super::{Q, Z};

    /// Checks whether the inverse is correctly computed for small values
    #[test]
    fn small_values() {
        let val_0 = Z::from(4);
        let val_1 = Z::from(-7);

        let inv_0 = val_0.inverse().unwrap();
        let inv_1 = val_1.inverse().unwrap();

        assert_eq!(Q::try_from((&1, &4)).unwrap(), inv_0);
        assert_eq!(Q::try_from((&-1, &7)).unwrap(), inv_1);
    }

    /// Checks whether the inverse is correctly computed for large values
    #[test]
    fn large_values() {
        let val_0 = Z::from(i64::MAX);
        let val_1 = Z::from(i64::MIN);

        let inv_0 = val_0.inverse().unwrap();
        let inv_1 = val_1.inverse().unwrap();

        assert_eq!(Q::try_from((&1, &i64::MAX)).unwrap(), inv_0);
        assert_eq!(Q::try_from((&1, &i64::MIN)).unwrap(), inv_1);
    }

    /// Checks whether the inverse of `0` returns `None`
    #[test]
    fn inv_zero_none() {
        let zero = Z::ZERO;

        let inv_zero = zero.inverse();

        assert!(inv_zero.is_none());
    }
}
