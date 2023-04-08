// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the [`GCD`] trait for [`Z`].

use super::Z;
use crate::{
    macros::for_others::{implement_for_others, implement_for_owned},
    traits::Gcd,
};
use flint_sys::fmpz::fmpz_gcd;

impl Gcd for &Z {
    type Output = Z;

    /// Outputs the greatest common divisor (gcd) of the two given values
    /// with `gcd(a,0) = a`.
    ///
    /// Paramters:
    /// - `other`: specifies one of the values of which the gcd is computed
    ///
    /// Returns the greatest common divisor of `self` and `other` as
    /// a [`Z`] instance.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::traits::*;
    ///
    /// let val_1 = Z::from(10);
    /// let val_2 = Z::from(15);
    ///
    /// let gcd = val_1.gcd(&val_2);
    ///
    /// # assert_eq!(Z::from(5), gcd);
    /// ```
    fn gcd(self, other: Self) -> Self::Output {
        let mut out = Z::default();
        unsafe { fmpz_gcd(&mut out.value, &self.value, &other.value) };
        out
    }
}

implement_for_owned!(Z, Gcd);
implement_for_others!(Z, Gcd for u8 u16 u32 u64 i8 i16 i32 i64);

#[cfg(test)]
mod test_gcd {
    use super::{Gcd, Z};

    /// Ensures that the gcd is correctly computed for small [`Z`] instances
    /// and ensures properties: `gcd(a,b) == gcd(b,a)` and `gcd(a,a) == a`
    #[test]
    fn small() {
        let pos_1 = Z::from(10);
        let pos_2 = Z::from(15);
        let neg_1 = Z::from(-10);
        let neg_2 = Z::from(-15);

        let gcd_pos_1 = pos_1.gcd(&pos_2);
        let gcd_pos_2 = pos_2.gcd(&pos_1);
        let gcd_pos_eq = pos_1.gcd(&pos_1);
        let gcd_mix_1 = pos_1.gcd(&neg_1);
        let gcd_mix_2 = neg_2.gcd(&pos_1);
        let gcd_neg_1 = neg_1.gcd(&neg_2);
        let gcd_neg_2 = neg_2.gcd(&neg_1);
        let gcd_neg_eq = neg_2.gcd(&neg_2);

        assert_eq!(Z::from(5), gcd_pos_1);
        assert_eq!(Z::from(5), gcd_pos_2);
        assert_eq!(Z::from(10), gcd_pos_eq);
        assert_eq!(Z::from(10), gcd_mix_1);
        assert_eq!(Z::from(5), gcd_mix_2);
        assert_eq!(Z::from(5), gcd_neg_1);
        assert_eq!(Z::from(5), gcd_neg_2);
        assert_eq!(Z::from(15), gcd_neg_eq);
    }

    /// Ensures that the gcd is correctly computed for small [`Z`] instances
    /// and ensures properties: `gcd(a,b) == gcd(b,a)`, `gcd(a,a) == a`, and
    /// `gcd(a,0) == a`
    #[test]
    fn large() {
        let pos = Z::from(i64::MAX);
        let zero = Z::ZERO;
        let neg = Z::from(i64::MIN);
        let abs_neg = Z::MINUS_ONE * &neg;

        let gcd_1 = pos.gcd(&zero);
        let gcd_2 = pos.gcd(&pos);
        let gcd_3 = neg.gcd(&zero);
        let gcd_4 = neg.gcd(&neg);
        let gcd_5 = pos.gcd(&neg);

        assert_eq!(pos, gcd_1);
        assert_eq!(pos, gcd_2);
        assert_eq!(abs_neg, gcd_3);
        assert_eq!(abs_neg, gcd_4);
        assert_eq!(Z::ONE, gcd_5);
    }

    /// Ensure that gcd trait/ implementation is available for other types
    #[test]
    fn availability() {
        let z = Z::ONE;

        let _ = z.gcd(z.clone());
        let _ = z.gcd(4_u8);
        let _ = z.gcd(4_u16);
        let _ = z.gcd(4_u32);
        let _ = z.gcd(4_u64);
        let _ = z.gcd(4_i8);
        let _ = z.gcd(4_i16);
        let _ = z.gcd(4_i32);
        let _ = z.gcd(4_i64);
    }
}
