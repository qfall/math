// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Div`] trait for [`Q`] values.

use super::super::Q;
use crate::{
    error::MathError,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpq::{fmpq_div, fmpq_is_zero};
use std::ops::Div;

impl Div for &Q {
    type Output = Q;
    /// Implements the [`Div`] trait for two [`Q`] values.
    /// [`Div`] is implemented for any combination of [`Q`] and borrowed [`Q`].
    ///
    /// Parameters:
    /// - `other`: specifies the value `self` is divided by.
    ///
    /// Returns the result ot the division as a [`Q`].
    ///
    /// # Example
    /// ```
    /// use math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from_str("42").unwrap();
    /// let b: Q = Q::from_str("24").unwrap();
    ///
    /// let c: Q = &a / &b;
    /// let d: Q = a / b;
    /// let e: Q = &c / d;
    /// let f: Q = c / &e;
    /// ```
    ///
    /// # Panics
    /// - Panics if the `other` value is `0`.
    fn div(self, other: Self) -> Self::Output {
        self.div_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, Q, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Div, div, Q, Q, Q);

impl Q {
    /// Implements division for two borrowed [`Q`] values.
    ///
    /// Parameters:
    /// - `divisor`: specifies the value `self` is divided by.
    ///
    /// Returns the result ot the division as a [`Q`] or an error, if division by zero occurs.
    ///
    /// # Example
    /// ```
    /// use math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from_str("42").unwrap();
    /// let b: Q = Q::from_str("24").unwrap();
    ///
    /// let c: Q = a.div_safe(&b).unwrap();
    /// ```
    ///
    ///  # Errors
    /// - Returns a [`MathError`] of type [`MathError::DivisionByZeroError`] if
    /// the `divisor` is `0`.
    ///
    pub fn div_safe(&self, divisor: &Q) -> Result<Q, MathError> {
        if 0 != unsafe { fmpq_is_zero(&divisor.value) } {
            return Err(MathError::DivisionByZeroError(format!(
                "tried to divide Q with value {} by Q with value {}",
                self, divisor
            )));
        }
        let mut out = Q::default();
        unsafe {
            fmpq_div(&mut out.value, &self.value, &divisor.value);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_div {
    use super::Q;
    use std::str::FromStr;

    /// testing division for two [`Q`]
    #[test]
    fn div() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a / b;
        assert!(c == Q::from_str("4/42").unwrap());
    }

    /// testing division for two borrowed [`Q`]
    #[test]
    fn div_borrow() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = &a / &b;
        assert!(c == Q::from_str("4/42").unwrap());
    }

    /// testing division for borrowed [`Q`] and [`Q`]
    #[test]
    fn div_first_borrowed() {
        let a: Q = Q::from_str("4").unwrap();
        let b: Q = Q::from_str("42/10").unwrap();
        let c: Q = &a / b;
        assert!(c == Q::from_str("40/42").unwrap());
    }

    /// testing division for [`Q`] and borrowed [`Q`]
    #[test]
    fn div_second_borrowed() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a / &b;
        assert!(c == Q::from_str("4/42").unwrap());
    }

    #[test]
    /// testing division for large numerators and divisors
    fn div_large() {
        let a: Q = Q::from_str(&(u64::MAX - 1).to_string()).unwrap();
        let b: Q = Q::from_str("2").unwrap();
        let c: Q = Q::from_str(&format!("1/{}", (i32::MAX))).unwrap();
        let d: Q = Q::from_str(&format!("1/{}", (u32::MAX))).unwrap();
        let e: Q = &a / &b;
        let f: Q = c / d;
        assert!(e == Q::from_str(&(i64::MAX).to_string()).unwrap());
        assert!(
            f == Q::from_str(&format!(
                "{}/{}",
                u64::from(u32::MAX),
                u64::from((u32::MAX - 1) / 2)
            ))
            .unwrap()
        );
    }

    /// testing division by `0` throws an error
    #[test]
    #[should_panic]
    fn div_by_zero() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("0").unwrap();
        let _c = a / b;
    }

    /// testing division by `0` throws an error
    #[test]
    fn div_by_zero_safe() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("0").unwrap();
        assert!(&a.div_safe(&b).is_err());
    }
}
