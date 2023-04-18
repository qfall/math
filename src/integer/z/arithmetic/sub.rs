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
    arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
    arithmetic_trait_mixed_borrowed_owned,
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
    /// use qfall_math::integer::Z;
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
arithmetic_between_types!(Sub, sub, Z, i64 i32 i16 i8 u64 u32 u16 u8);

#[cfg(test)]
mod test_sub_between_types {

    use crate::integer::Z;
    use std::str::FromStr;

    /// testing subtraction between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn sub() {
        let a: Z = Z::from_str("42").unwrap();
        let b: u64 = 1;
        let c: u32 = 1;
        let d: u16 = 1;
        let e: u8 = 1;
        let f: i64 = 1;
        let g: i32 = 1;
        let h: i16 = 1;
        let i: i8 = 1;
        let _: Z = &a - &b;
        let _: Z = &a - &c;
        let _: Z = &a - &d;
        let _: Z = &a - &e;
        let _: Z = &a - &f;
        let _: Z = &a - &g;
        let _: Z = &a - &h;
        let _: Z = &a - &i;

        let _: Z = &b - &a;
        let _: Z = &c - &a;
        let _: Z = &d - &a;
        let _: Z = &e - &a;
        let _: Z = &f - &a;
        let _: Z = &g - &a;
        let _: Z = &h - &a;
        let _: Z = &i - &a;

        let _: Z = &a - b;
        let _: Z = &a - c;
        let _: Z = &a - d;
        let _: Z = &a - e;
        let _: Z = &a - f;
        let _: Z = &a - g;
        let _: Z = &a - h;
        let _: Z = &a - i;

        let _: Z = &b - Z::from_str("42").unwrap();
        let _: Z = &c - Z::from_str("42").unwrap();
        let _: Z = &d - Z::from_str("42").unwrap();
        let _: Z = &e - Z::from_str("42").unwrap();
        let _: Z = &f - Z::from_str("42").unwrap();
        let _: Z = &g - Z::from_str("42").unwrap();
        let _: Z = &h - Z::from_str("42").unwrap();
        let _: Z = &i - Z::from_str("42").unwrap();

        let _: Z = Z::from_str("42").unwrap() - &b;
        let _: Z = Z::from_str("42").unwrap() - &c;
        let _: Z = Z::from_str("42").unwrap() - &d;
        let _: Z = Z::from_str("42").unwrap() - &e;
        let _: Z = Z::from_str("42").unwrap() - &f;
        let _: Z = Z::from_str("42").unwrap() - &g;
        let _: Z = Z::from_str("42").unwrap() - &h;
        let _: Z = Z::from_str("42").unwrap() - &i;

        let _: Z = b - &a;
        let _: Z = c - &a;
        let _: Z = d - &a;
        let _: Z = e - &a;
        let _: Z = f - &a;
        let _: Z = g - &a;
        let _: Z = h - &a;
        let _: Z = i - &a;

        let _: Z = Z::from_str("42").unwrap() - b;
        let _: Z = Z::from_str("42").unwrap() - c;
        let _: Z = Z::from_str("42").unwrap() - d;
        let _: Z = Z::from_str("42").unwrap() - e;
        let _: Z = Z::from_str("42").unwrap() - f;
        let _: Z = Z::from_str("42").unwrap() - g;
        let _: Z = Z::from_str("42").unwrap() - h;
        let _: Z = Z::from_str("42").unwrap() - i;

        let _: Z = b - Z::from_str("42").unwrap();
        let _: Z = c - Z::from_str("42").unwrap();
        let _: Z = d - Z::from_str("42").unwrap();
        let _: Z = e - Z::from_str("42").unwrap();
        let _: Z = f - Z::from_str("42").unwrap();
        let _: Z = g - Z::from_str("42").unwrap();
        let _: Z = h - Z::from_str("42").unwrap();
        let _: Z = i - Z::from_str("42").unwrap();
    }
}

#[cfg(test)]
mod test_sub {

    use super::Z;

    /// testing subtraction for two Z
    #[test]
    fn sub() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a - b;
        assert_eq!(c, Z::from(18));
    }

    /// testing subtraction for two borrowed [`Z`]
    #[test]
    fn sub_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a - &b;
        assert_eq!(c, Z::from(18));
    }

    /// testing subtraction for borrowed [`Z`] and [`Z`]
    #[test]
    fn sub_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a - b;
        assert_eq!(c, Z::from(18));
    }

    /// testing subtraction for [`Z`] and borrowed [`Z`]
    #[test]
    fn sub_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a - &b;
        assert_eq!(c, Z::from(18));
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
        assert_eq!(d, Z::from(i64::MAX));
        assert_eq!(e, Z::from(i64::MIN + 1));
        assert_eq!(f, Z::from(i64::MAX - 738201034));
    }
}
