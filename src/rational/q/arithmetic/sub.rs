// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`Q`] values.

use super::super::Q;
use crate::{
    integer::Z,
    macros::arithmetics::{
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpq::{fmpq_sub, fmpq_sub_fmpz};
use std::ops::Sub;

impl Sub for &Q {
    type Output = Q;
    /// Implements the [`Sub`] trait for two [`Q`] values.
    /// [`Sub`] is implemented for any combination of [`Q`] and borrowed [`Q`].
    ///
    /// Parameters:
    ///  - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the result of the subtraction as a [`Q`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from(42);
    /// let b: Q = Q::from((-42, 2));
    ///
    /// let c: Q = &a - &b;
    /// let d: Q = a - b;
    /// let e: Q = &c - d;
    /// let f: Q = c - &e;
    /// ```
    fn sub(self, other: Self) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_sub(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, Q, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, Q, Q, Q);
arithmetic_between_types!(Sub, sub, Q, Q, i64 i32 i16 i8 u64 u32 u16 u8 f32 f64);

impl Sub<&Z> for &Q {
    type Output = Q;

    /// Implements the [`Sub`] trait for [`Q`] and [`Z`] values.
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the result of the subtraction of both numbers as a [`Q`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from((42, 19));
    /// let b: Z = Z::from(42);
    ///
    /// let c: Q = &a - &b;
    /// let d: Q = a - b;
    /// let e: Q = &c - Z::from(42);
    /// let f: Q = c - &Z::from(42);
    /// ```
    fn sub(self, other: &Z) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_sub_fmpz(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, Q, Z, Q);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, Q, Z, Q);

#[cfg(test)]
mod test_sub {
    use super::Q;

    /// Testing subtraction for two [`Q`]
    #[test]
    fn sub() {
        let a: Q = Q::from(42);
        let b: Q = Q::from((42, 2));
        let c: Q = a - b;
        assert_eq!(c, Q::from(21));
    }

    /// Testing subtraction for two borrowed [`Q`]
    #[test]
    fn sub_borrow() {
        let a: Q = Q::from(42);
        let b: Q = Q::from((42, 2));
        let c: Q = &a - &b;
        assert_eq!(c, Q::from(21));
    }

    /// Testing subtraction for borrowed [`Q`] and [`Q`]
    #[test]
    fn sub_first_borrowed() {
        let a: Q = Q::from((42, 5));
        let b: Q = Q::from((42, 10));
        let c: Q = &a - b;
        assert_eq!(c, Q::from((21, 5)));
    }

    /// Testing subtraction for [`Q`] and borrowed [`Q`]
    #[test]
    fn sub_second_borrowed() {
        let a: Q = Q::from(42);
        let b: Q = Q::from((42, 2));
        let c: Q = a - &b;
        assert_eq!(c, Q::from(21));
    }

    /// Testing subtraction for large numerators and divisors
    #[test]
    fn sub_large() {
        let a: Q = Q::from(i64::MAX);
        let b: Q = Q::from(u64::MAX - 1);
        let c: Q = Q::from((1, i64::MAX));
        let d: Q = Q::from((1, u64::MAX));
        let e: Q = &b - &a;
        let f: Q = &c - &d;
        assert_eq!(e, a);
        assert_eq!(f, Q::from((-1, u64::MAX)) + Q::from((1, i64::MAX)));
    }
}

#[cfg(test)]
mod test_sub_between_z_and_q {
    use super::Z;
    use crate::rational::Q;

    /// Testing subtraction for [`Q`] and [`Z`]
    #[test]
    fn sub() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = a - b;
        assert_eq!(c, Q::from((-23, 7)));
    }

    /// Testing subtraction for both borrowed [`Q`] and [`Z`]
    #[test]
    fn sub_borrow() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = &a - &b;
        assert_eq!(c, Q::from((-23, 7)));
    }

    /// Testing subtraction for borrowed [`Q`] and [`Z`]
    #[test]
    fn sub_first_borrowed() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = &a - b;
        assert_eq!(c, Q::from((-23, 7)));
    }

    /// Testing subtraction for [`Q`] and borrowed [`Z`]
    #[test]
    fn sub_second_borrowed() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = a - &b;
        assert_eq!(c, Q::from((-23, 7)));
    }

    /// Testing subtraction for big numbers
    #[test]
    fn sub_large_numbers() {
        let a: Q = Q::from((u64::MAX, 2));
        let b: Q = Q::from((1, u64::MAX));
        let c: Z = Z::from(u64::MAX);
        let d: Q = a - &c;
        let e: Q = b - c;
        assert_eq!(d, Q::from((u64::MAX, 2)) - Q::from(u64::MAX));
        assert_eq!(e, Q::from((1, u64::MAX)) - Q::from(u64::MAX));
    }
}

#[cfg(test)]
mod test_sub_between_types {
    use crate::rational::Q;

    /// Testing subtraction between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn sub() {
        let a: Q = Q::from(42);
        let b: u64 = 1;
        let c: u32 = 1;
        let d: u16 = 1;
        let e: u8 = 1;
        let f: i64 = 1;
        let g: i32 = 1;
        let h: i16 = 1;
        let i: i8 = 1;
        let j: f32 = 1.3;
        let k: f64 = 1.3;

        let _: Q = &a - &b;
        let _: Q = &a - &c;
        let _: Q = &a - &d;
        let _: Q = &a - &e;
        let _: Q = &a - &f;
        let _: Q = &a - &g;
        let _: Q = &a - &h;
        let _: Q = &a - &i;
        let _: Q = &a - &j;
        let _: Q = &a - &k;

        let _: Q = &b - &a;
        let _: Q = &c - &a;
        let _: Q = &d - &a;
        let _: Q = &e - &a;
        let _: Q = &f - &a;
        let _: Q = &g - &a;
        let _: Q = &h - &a;
        let _: Q = &i - &a;
        let _: Q = &j - &a;
        let _: Q = &k - &a;

        let _: Q = &a - b;
        let _: Q = &a - c;
        let _: Q = &a - d;
        let _: Q = &a - e;
        let _: Q = &a - f;
        let _: Q = &a - g;
        let _: Q = &a - h;
        let _: Q = &a - i;
        let _: Q = &a - j;
        let _: Q = &a - k;

        let _: Q = &b - Q::from(42);
        let _: Q = &c - Q::from(42);
        let _: Q = &d - Q::from(42);
        let _: Q = &e - Q::from(42);
        let _: Q = &f - Q::from(42);
        let _: Q = &g - Q::from(42);
        let _: Q = &h - Q::from(42);
        let _: Q = &i - Q::from(42);
        let _: Q = &j - Q::from(42);
        let _: Q = &k - Q::from(42);

        let _: Q = Q::from(42) - &b;
        let _: Q = Q::from(42) - &c;
        let _: Q = Q::from(42) - &d;
        let _: Q = Q::from(42) - &e;
        let _: Q = Q::from(42) - &f;
        let _: Q = Q::from(42) - &g;
        let _: Q = Q::from(42) - &h;
        let _: Q = Q::from(42) - &i;
        let _: Q = Q::from(42) - &j;
        let _: Q = Q::from(42) - &k;

        let _: Q = b - &a;
        let _: Q = c - &a;
        let _: Q = d - &a;
        let _: Q = e - &a;
        let _: Q = f - &a;
        let _: Q = g - &a;
        let _: Q = h - &a;
        let _: Q = i - &a;
        let _: Q = j - &a;
        let _: Q = k - &a;

        let _: Q = Q::from(42) - b;
        let _: Q = Q::from(42) - c;
        let _: Q = Q::from(42) - d;
        let _: Q = Q::from(42) - e;
        let _: Q = Q::from(42) - f;
        let _: Q = Q::from(42) - g;
        let _: Q = Q::from(42) - h;
        let _: Q = Q::from(42) - i;
        let _: Q = Q::from(42) - j;
        let _: Q = Q::from(42) - k;

        let _: Q = b - Q::from(42);
        let _: Q = c - Q::from(42);
        let _: Q = d - Q::from(42);
        let _: Q = e - Q::from(42);
        let _: Q = f - Q::from(42);
        let _: Q = g - Q::from(42);
        let _: Q = h - Q::from(42);
        let _: Q = i - Q::from(42);
        let _: Q = j - Q::from(42);
        let _: Q = k - Q::from(42);
    }
}
