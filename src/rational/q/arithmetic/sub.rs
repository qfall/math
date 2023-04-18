// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`Q`] values.

use super::super::Q;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpq::fmpq_sub;
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
    /// # Example
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from_str("42").unwrap();
    /// let b: Q = Q::from_str("-42/2").unwrap();
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

#[cfg(test)]
mod test_sub {
    use super::Q;
    use std::str::FromStr;

    /// testing subtraction for two [`Q`]
    #[test]
    fn sub() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a - b;
        assert_eq!(c, Q::from_str("21").unwrap());
    }

    /// testing subtraction for two borrowed [`Q`]
    #[test]
    fn sub_borrow() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = &a - &b;
        assert_eq!(c, Q::from_str("21").unwrap());
    }

    /// testing subtraction for borrowed [`Q`] and [`Q`]
    #[test]
    fn sub_first_borrowed() {
        let a: Q = Q::from_str("42/5").unwrap();
        let b: Q = Q::from_str("42/10").unwrap();
        let c: Q = &a - b;
        assert_eq!(c, Q::from_str("21/5").unwrap());
    }

    /// testing subtraction for [`Q`] and borrowed [`Q`]
    #[test]
    fn sub_second_borrowed() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a - &b;
        assert_eq!(c, Q::from_str("21").unwrap());
    }

    #[test]
    /// testing subtraction for large numerators and divisors
    fn sub_large() {
        let a: Q = Q::from_str(&(i64::MAX).to_string()).unwrap();
        let b: Q = Q::from_str(&(u64::MAX - 1).to_string()).unwrap();
        let c: Q = Q::from_str(&format!("1/{}", (i64::MAX))).unwrap();
        let d: Q = Q::from_str(&format!("1/{}", (u64::MAX))).unwrap();
        let e: Q = &b - &a;
        let f: Q = &c - &d;
        assert_eq!(e, a);
        assert_eq!(
            f,
            Q::from_str(&format!("-1/{}", (u64::MAX))).unwrap()
                + Q::from_str(&format!("1/{}", (i64::MAX))).unwrap()
        );
    }
}
