// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the [`Lcm`] trait for [`Z`].

use super::Z;
use crate::traits::Lcm;
use flint_sys::fmpz::fmpz_lcm;

impl<Integer: Into<Z>> Lcm<Integer> for Z {
    type Output = Z;

    /// Outputs the least common multiple (lcm) of the two given values
    /// with `lcm(a, 0) = 0`.
    ///
    /// Parameters:
    /// - `other`: specifies one of the values of which the `lcm` is computed
    ///
    /// Returns the least common multiple of `self` and `other` as
    /// a new [`Z`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::traits::*;
    ///
    /// let val_1 = Z::from(10);
    /// let val_2 = Z::from(15);
    ///
    /// let lcm = val_1.lcm(&val_2);
    ///
    /// assert_eq!(Z::from(30), lcm);
    /// ```
    fn lcm(&self, other: Integer) -> Self::Output {
        let other = other.into();
        let mut out = Z::ZERO;
        unsafe { fmpz_lcm(&mut out.value, &self.value, &other.value) };
        out
    }
}

#[cfg(test)]
mod test_lcm {
    use super::{Lcm, Z};

    /// Ensures that the lcm is correctly computed for small [`Z`] instances
    /// and ensures properties: `lcm(a, b) == lcm(b, a)` and `lcm(a, a) == a`
    #[test]
    fn small() {
        let pos_1 = Z::from(10);
        let pos_2 = Z::from(15);
        let neg_1 = Z::from(-10);
        let neg_2 = Z::from(-15);

        let lcm_pos_1 = pos_1.lcm(&pos_2);
        let lcm_pos_2 = pos_2.lcm(&pos_1);
        let lcm_pos_eq = pos_1.lcm(&pos_1);
        let lcm_mix_1 = pos_1.lcm(&neg_1);
        let lcm_mix_2 = neg_2.lcm(&pos_1);
        let lcm_neg_1 = neg_1.lcm(&neg_2);
        let lcm_neg_2 = neg_2.lcm(&neg_1);
        let lcm_neg_eq = neg_2.lcm(&neg_2);

        assert_eq!(Z::from(30), lcm_pos_1);
        assert_eq!(Z::from(30), lcm_pos_2);
        assert_eq!(Z::from(10), lcm_pos_eq);
        assert_eq!(Z::from(10), lcm_mix_1);
        assert_eq!(Z::from(30), lcm_mix_2);
        assert_eq!(Z::from(30), lcm_neg_1);
        assert_eq!(Z::from(30), lcm_neg_2);
        assert_eq!(Z::from(15), lcm_neg_eq);
    }

    /// Ensures that the lcm is correctly computed for small [`Z`] instances
    /// and ensures properties: `lcm(a, b) == lcm(b, a)`, `lcm(a, a) == a`, and
    /// `lcm(a, 0) == 0`
    #[test]
    fn large() {
        let pos = Z::from(i64::MAX);
        let zero = Z::ZERO;
        let neg = Z::from(i64::MIN);
        let abs_neg = Z::MINUS_ONE * &neg;

        let lcm_1 = pos.lcm(&zero);
        let lcm_2 = pos.lcm(&pos);
        let lcm_3 = neg.lcm(&zero);
        let lcm_4 = neg.lcm(&neg);
        let lcm_5 = pos.lcm(&neg);

        assert_eq!(zero, lcm_1);
        assert_eq!(pos, lcm_2);
        assert_eq!(zero, lcm_3);
        assert_eq!(abs_neg, lcm_4);
        assert_eq!(pos * abs_neg, lcm_5);
    }

    /// Ensure that lcm trait/ implementation is available for other types
    #[test]
    fn availability() {
        let z = Z::ONE;

        let _ = z.lcm(z.clone());
        let _ = z.lcm(4_u8);
        let _ = z.lcm(4_u16);
        let _ = z.lcm(4_u32);
        let _ = z.lcm(4_u64);
        let _ = z.lcm(4_i8);
        let _ = z.lcm(4_i16);
        let _ = z.lcm(4_i32);
        let _ = z.lcm(4_i64);
    }
}
