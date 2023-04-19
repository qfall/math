// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the [`Gcd`]
//! and [`Xgcd`] trait for [`Z`].

use super::Z;
use crate::{
    macros::for_others::{implement_for_others, implement_for_owned},
    traits::{Gcd, Xgcd},
};
use flint_sys::fmpz::{fmpz_gcd, fmpz_xgcd};

impl Gcd<&Z> for Z {
    type Output = Z;

    /// Outputs the greatest common divisor (gcd) of the two given values
    /// with `gcd(a,0) = |a|`.
    ///
    /// Paramters:
    /// - `other`: specifies one of the values of which the gcd is computed
    ///
    /// Returns the greatest common divisor of `self` and `other` as
    /// a [`Z`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::traits::*;
    ///
    /// let val_1 = Z::from(10);
    /// let val_2 = Z::from(15);
    ///
    /// let gcd = val_1.gcd(&val_2);
    ///
    /// assert_eq!(Z::from(5), gcd);
    /// ```
    fn gcd(&self, other: &Self) -> Self::Output {
        let mut out = Z::default();
        unsafe { fmpz_gcd(&mut out.value, &self.value, &other.value) };
        out
    }
}

implement_for_owned!(Z, Z, Gcd);
implement_for_others!(Z, Z, Gcd for u8 u16 u32 u64 i8 i16 i32 i64);

impl Xgcd<&Z> for Z {
    type Output = (Z, Z, Z);

    /// Outputs the extended greatest common divisor (xgcd) of the two given values,
    /// i.e. a triple `(gcd(a,b), x, y)`, where `a*x + b*y = gcd(a,b)*`.
    ///
    /// Paramters:
    /// - `other`: specifies one of the values of which the gcd is computed
    ///
    /// Returns a triple `(gcd(a,b), x, y)` containing the greatest common divisor,
    /// `x`, and `y` s.t. `gcd(a,b) = a*x + b*y`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::traits::*;
    ///
    /// let val_1 = Z::from(10);
    /// let val_2 = Z::from(15);
    ///
    /// let (gcd, x, y) = val_1.xgcd(&val_2);
    /// let cmp_gcd = &val_1 * &x + &val_2 * &y;
    ///
    /// assert_eq!(Z::from(5), gcd);
    /// assert_eq!(gcd, cmp_gcd);
    /// ```
    fn xgcd(&self, other: &Self) -> Self::Output {
        let mut gcd = Z::ZERO;
        let mut x = Z::ZERO;
        let mut y = Z::ZERO;
        unsafe {
            fmpz_xgcd(
                &mut gcd.value,
                &mut x.value,
                &mut y.value,
                &self.value,
                &other.value,
            )
        };
        (gcd, x, y)
    }
}

implement_for_owned!(Z, Z, Xgcd);
implement_for_others!(Z, Z, Xgcd for u8 u16 u32 u64 i8 i16 i32 i64);

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

#[cfg(test)]
mod test_xgcd {
    use super::{Xgcd, Z};

    /// Ensures that the gcd is correctly computed for small [`Z`] instances
    /// and ensures properties: `gcd(a,b) == gcd(b,a)` and `gcd(a,a) == a`
    #[test]
    fn gcd_small() {
        let pos_1 = Z::from(10);
        let pos_2 = Z::from(15);
        let neg_1 = Z::from(-10);
        let neg_2 = Z::from(-15);

        let xgcd_pos_1 = pos_1.xgcd(&pos_2);
        let xgcd_pos_2 = pos_2.xgcd(&pos_1);
        let xgcd_pos_eq = pos_1.xgcd(&pos_1);
        let xgcd_mix_1 = pos_1.xgcd(&neg_1);
        let xgcd_mix_2 = neg_2.xgcd(&pos_1);
        let xgcd_neg_1 = neg_1.xgcd(&neg_2);
        let xgcd_neg_2 = neg_2.xgcd(&neg_1);
        let xgcd_neg_eq = neg_2.xgcd(&neg_2);

        assert_eq!(Z::from(5), xgcd_pos_1.0);
        assert_eq!(Z::from(5), xgcd_pos_2.0);
        assert_eq!(Z::from(10), xgcd_pos_eq.0);
        assert_eq!(Z::from(10), xgcd_mix_1.0);
        assert_eq!(Z::from(5), xgcd_mix_2.0);
        assert_eq!(Z::from(5), xgcd_neg_1.0);
        assert_eq!(Z::from(5), xgcd_neg_2.0);
        assert_eq!(Z::from(15), xgcd_neg_eq.0);
    }

    /// Ensures that the gcd is correctly computed for small [`Z`] instances
    /// and ensures properties: `gcd(a,b) == gcd(b,a)`, `gcd(a,a) == a`, and
    /// `gcd(a,0) == a`
    #[test]
    fn gcd_large() {
        let pos = Z::from(i64::MAX);
        let zero = Z::ZERO;
        let neg = Z::from(i64::MIN);
        let abs_neg = Z::MINUS_ONE * &neg;

        let xgcd_1 = pos.xgcd(&zero);
        let xgcd_2 = pos.xgcd(&pos);
        let xgcd_3 = neg.xgcd(&zero);
        let xgcd_4 = neg.xgcd(&neg);
        let xgcd_5 = pos.xgcd(&neg);

        assert_eq!(pos, xgcd_1.0);
        assert_eq!(pos, xgcd_2.0);
        assert_eq!(abs_neg, xgcd_3.0);
        assert_eq!(abs_neg, xgcd_4.0);
        assert_eq!(Z::ONE, xgcd_5.0);
    }

    /// Ensures that the computation of `x` and `y` works correctly
    /// s.t. `a*x + b*y = gcd(a,b)` for small values
    #[test]
    fn xy_small() {
        let pos_1 = Z::from(10);
        let pos_2 = Z::from(15);
        let neg_1 = Z::from(-10);
        let neg_2 = Z::from(-15);

        let xgcd_pos_1 = pos_1.xgcd(&pos_2);
        let xgcd_pos_2 = pos_2.xgcd(&pos_1);
        let xgcd_pos_eq = pos_1.xgcd(&pos_1);
        let xgcd_mix_1 = pos_1.xgcd(&neg_1);
        let xgcd_mix_2 = neg_2.xgcd(&pos_1);
        let xgcd_neg_1 = neg_1.xgcd(&neg_2);
        let xgcd_neg_2 = neg_2.xgcd(&neg_1);
        let xgcd_neg_eq = neg_2.xgcd(&neg_2);

        // check that `gcd(a,b) == a * x + b * y`
        assert_eq!(
            xgcd_pos_1.0,
            &pos_1 * &xgcd_pos_1.1 + &pos_2 * &xgcd_pos_1.2
        );
        assert_eq!(
            xgcd_pos_2.0,
            &pos_2 * &xgcd_pos_2.1 + &pos_1 * &xgcd_pos_2.2
        );
        assert_eq!(
            xgcd_pos_eq.0,
            &pos_1 * &xgcd_pos_eq.1 + &pos_1 * &xgcd_pos_eq.2
        );
        assert_eq!(
            xgcd_mix_1.0,
            &pos_1 * &xgcd_mix_1.1 + &neg_1 * &xgcd_mix_1.2
        );
        assert_eq!(
            xgcd_mix_2.0,
            &neg_2 * &xgcd_mix_2.1 + &pos_1 * &xgcd_mix_2.2
        );
        assert_eq!(
            xgcd_neg_1.0,
            &neg_1 * &xgcd_neg_1.1 + &neg_2 * &xgcd_neg_1.2
        );
        assert_eq!(
            xgcd_neg_2.0,
            &neg_2 * &xgcd_neg_2.1 + &neg_1 * &xgcd_neg_2.2
        );
        assert_eq!(
            xgcd_neg_eq.0,
            &neg_2 * &xgcd_neg_eq.1 + &neg_2 * &xgcd_neg_eq.2
        );
    }

    /// Ensures that the computation of `x` and `y` works correctly
    /// s.t. `a*x + b*y = gcd(a,b)` for large values
    #[test]
    fn xy_large() {
        let pos = Z::from(i64::MAX);
        let zero = Z::ZERO;
        let neg = Z::from(i64::MIN);

        let xgcd_1 = pos.xgcd(&zero);
        let xgcd_2 = pos.xgcd(&pos);
        let xgcd_3 = neg.xgcd(&zero);
        let xgcd_4 = neg.xgcd(&neg);
        let xgcd_5 = pos.xgcd(&neg);

        // check that `gcd(a,b) == a * x + b * y`
        assert_eq!(xgcd_1.0, &pos * &xgcd_1.1 + &zero * &xgcd_1.2);
        assert_eq!(xgcd_2.0, &pos * &xgcd_2.1 + &pos * &xgcd_2.2);
        assert_eq!(xgcd_3.0, &neg * &xgcd_3.1 + &zero * &xgcd_3.2);
        assert_eq!(xgcd_4.0, &neg * &xgcd_4.1 + &neg * &xgcd_4.2);
        assert_eq!(xgcd_5.0, &pos * &xgcd_5.1 + &neg * &xgcd_5.2);
    }

    /// Ensure that xgcd trait/ implementation is available for other types
    #[test]
    fn availability() {
        let z = Z::ONE;

        let _ = z.xgcd(z.clone());
        let _ = z.xgcd(4_u8);
        let _ = z.xgcd(4_u16);
        let _ = z.xgcd(4_u32);
        let _ = z.xgcd(4_u64);
        let _ = z.xgcd(4_i8);
        let _ = z.xgcd(4_i16);
        let _ = z.xgcd(4_i32);
        let _ = z.xgcd(4_i64);
    }
}
