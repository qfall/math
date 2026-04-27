// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the `mod±` function for [`Zq`] values.

use super::super::Zq;
use crate::integer::Z;
use std::ops::Rem;

impl Zq {
    /// Computes `self` mod± `modulus` as long as `modulus` is greater than 1, i.e.
    /// it returns a value in `[-⌈q/2⌉, ⌈q/2⌉]`.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the remainder closest to `0` is computed
    ///
    /// Returns `self` mod± `modulus` as a [`Z`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let a = Zq::from((42, 24));
    /// let b = 24;
    ///
    /// let c = a.mod_pm(b);
    ///
    /// assert_eq!(-6, c);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    pub fn mod_pm(&self, modulus: impl Into<Z>) -> Z {
        let modulus = modulus.into();
        assert!(modulus > 1, "Modulus can not be smaller than 2.");

        let mut value = (&self.value).rem(&modulus);

        if value > modulus.div_floor(2) {
            value -= modulus;
        }
        value
    }
}

#[cfg(test)]
mod test_mod_pm {
    use super::{Z, Zq};
    use crate::integer_mod_q::Modulus;

    /// Testing mod± for two [`Zq`]
    #[test]
    fn mod_pm() {
        let a = Zq::from((42, 257));
        let b = Z::from(25);

        let c1 = a.mod_pm(b);
        let c2 = a.mod_pm(25);

        assert_eq!(c1, -8);
        assert_eq!(c2, -8);
    }

    /// Testing mod± for large numbers
    #[test]
    fn mod_pm_large_numbers() {
        let a = Zq::from((u64::MAX - 1, u64::MAX));
        let b = Z::from(u64::MAX - 2);

        let c1 = a.clone().mod_pm(&b);
        let c2 = a.mod_pm(&Z::from(u64::MAX - 2));

        assert_eq!(c1, 1);
        assert_eq!(c2, 1);
    }

    /// Ensures that computing mod± a negative number results in a panic
    #[test]
    #[should_panic]
    fn mod_pm_negative_error() {
        _ = Zq::from(42).mod_pm(-24);
    }

    /// Ensures that computing mod± 0 results in a panic
    #[test]
    #[should_panic]
    fn zero_modulus() {
        _ = Zq::from(15).mod_pm(0);
    }

    /// Ensures that `mod±` is available for several types.
    #[test]
    fn availability() {
        let _ = Zq::from((0, 7)).mod_pm(2u8);
        let _ = Zq::from((0, 7)).mod_pm(2u16);
        let _ = Zq::from((0, 7)).mod_pm(2u32);
        let _ = Zq::from((0, 7)).mod_pm(2u64);
        let _ = Zq::from((0, 7)).mod_pm(2i8);
        let _ = Zq::from((0, 7)).mod_pm(2i16);
        let _ = Zq::from((0, 7)).mod_pm(2i32);
        let _ = Zq::from((0, 7)).mod_pm(2i64);
        let _ = Zq::from((0, 7)).mod_pm(Z::from(2));
        let _ = Zq::from((0, 7)).mod_pm(Modulus::from(2));
    }
}
