// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`Z`] values.

use super::super::Z;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpz::fmpz_sub;
use std::ops::Sub;

impl Sub for &Z {
    type Output = Z;
    /// Implements the [`Sub`] trait for two [`Z`] values.
    /// [`Sub`] is implemented for any combination of [`Z`] and borrowed [`Z`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the result of the subtraction as a [`Z`].
    ///
    /// # Example
    /// ```
    /// use math::integer::Z;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Z = Z::from(24);
    ///
    /// let c: Z = &a - &b;
    /// let d: Z = a - b;
    /// let e: Z = &c - d;
    /// let f: Z = c - &e;
    /// ```
    fn sub(self, other: Self) -> Self::Output {
        let mut out = Z::default();
        unsafe {
            fmpz_sub(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, Z, Z, Z);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, Z, Z, Z);

#[cfg(test)]
mod test_sub {

    use super::Z;

    /// testing subtraction for two Z
    #[test]
    fn sub() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a - b;
        assert!(c == Z::from(18));
    }

    /// testing subtraction for two borrowed [`Z`]
    #[test]
    fn sub_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a - &b;
        assert!(c == Z::from(18));
    }

    /// testing subtraction for borrowed [`Z`] and [`Z`]
    #[test]
    fn sub_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a - b;
        assert!(c == Z::from(18));
    }

    /// testing subtraction for [`Z`] and borrowed [`Z`]
    #[test]
    fn sub_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a - &b;
        assert!(c == Z::from(18));
    }

    /// testing subtraction for large integers
    #[test]
    fn sub_large() {
        let a: Z = Z::from(u64::MAX - 1);
        let b: Z = Z::from(i64::MAX);
        let c: Z = Z::from(738201034);
        let d: Z = &a - &b;
        let e: Z = &b - a;
        let f: Z = b - c;
        assert!(d == Z::from(i64::MAX));
        assert!(e == Z::from(i64::MIN + 1));
        assert!(f == Z::from(i64::MAX - 738201034));
    }
}
