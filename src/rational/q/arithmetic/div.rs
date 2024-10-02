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
    integer::Z,
    macros::arithmetics::{
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpq::{fmpq_div, fmpq_div_fmpz, fmpq_is_zero};
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
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from(42);
    /// let b: Q = Q::from(24);
    ///
    /// let c: Q = &a / &b;
    /// let d: Q = a / b;
    /// let e: Q = &c / d;
    /// let f: Q = c / &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the `other` value is `0`.
    fn div(self, other: Self) -> Self::Output {
        self.div_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, Q, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Div, div, Q, Q, Q);
arithmetic_between_types!(Div, div, Q, Q, i64 i32 i16 i8 u64 u32 u16 u8 f32 f64);

impl Div<&Z> for &Q {
    type Output = Q;

    /// Implements the [`Div`] trait for [`Q`] and [`Z`] values.
    /// [`Div`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to divide `self` by
    ///
    /// Returns the ratio of both numbers as a [`Q`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from((42, 19));
    /// let b: Z = Z::from(-42);
    ///
    /// let c: Q = &a / &b;
    /// let d: Q = a / b;
    /// let e: Q = &c / Z::from(42);
    /// let f: Q = c / &Z::from(42);
    /// ```
    fn div(self, other: &Z) -> Self::Output {
        assert!(!other.is_zero(), "Tried to divide {self} by zero.");

        let mut out = Q::default();
        unsafe {
            fmpq_div_fmpz(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, Q, Z, Q);
arithmetic_trait_mixed_borrowed_owned!(Div, div, Q, Z, Q);

impl Q {
    /// Implements division for two borrowed [`Q`] values.
    ///
    /// Parameters:
    /// - `divisor`: specifies the value `self` is divided by.
    ///
    /// Returns the result ot the division as a [`Q`] or an error if division by zero occurs.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from(42);
    /// let b: Q = Q::from(24);
    ///
    /// let c: Q = a.div_safe(&b).unwrap();
    /// ```
    ///
    ///  # Errors
    /// - Returns a [`MathError`] of type [`MathError::DivisionByZeroError`] if
    ///     the `divisor` is `0`.
    pub fn div_safe(&self, divisor: &Q) -> Result<Q, MathError> {
        if 0 != unsafe { fmpq_is_zero(&divisor.value) } {
            return Err(MathError::DivisionByZeroError(format!(
                "tried to divide Q with value {self} by Q with value {divisor}"
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

    /// Testing division for two [`Q`]
    #[test]
    fn div() {
        let a: Q = Q::from(2);
        let b: Q = Q::from((42, 2));
        let c: Q = a / b;
        assert_eq!(c, Q::from((4, 42)));
    }

    /// Testing division for two borrowed [`Q`]
    #[test]
    fn div_borrow() {
        let a: Q = Q::from(2);
        let b: Q = Q::from((42, 2));
        let c: Q = &a / &b;
        assert_eq!(c, Q::from((4, 42)));
    }

    /// Testing division for borrowed [`Q`] and [`Q`]
    #[test]
    fn div_first_borrowed() {
        let a: Q = Q::from(4);
        let b: Q = Q::from((42, 10));
        let c: Q = &a / b;
        assert_eq!(c, Q::from((40, 42)));
    }

    /// Testing division for [`Q`] and borrowed [`Q`]
    #[test]
    fn div_second_borrowed() {
        let a: Q = Q::from(2);
        let b: Q = Q::from((42, 2));
        let c: Q = a / &b;
        assert_eq!(c, Q::from((4, 42)));
    }

    /// Testing division for large numerators and divisors
    #[test]
    fn div_large() {
        let a: Q = Q::from(u64::MAX - 1);
        let b: Q = Q::from(2);
        let c: Q = Q::from((1, i32::MAX));
        let d: Q = Q::from((1, u32::MAX));

        let e: Q = &a / &b;
        let f: Q = c / d;

        assert_eq!(e, Q::from(i64::MAX));
        assert_eq!(f, Q::from((u32::MAX, (u32::MAX - 1) / 2)));
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero() {
        let a: Q = Q::from(2);
        let b: Q = Q::ZERO;
        let _c = a / b;
    }

    /// Testing division by `0` throws an error
    #[test]
    fn div_by_zero_safe() {
        let a: Q = Q::from(2);
        let b: Q = Q::ZERO;
        assert!(&a.div_safe(&b).is_err());
    }
}

#[cfg(test)]
mod test_div_between_q_and_z {
    use crate::integer::Z;
    use crate::rational::Q;

    /// Testing division for [`Q`] and [`Z`]
    #[test]
    fn div() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = a / b;
        assert_eq!(c, Q::from((5, 28)));
    }

    /// Testing division for both borrowed [`Q`] and [`Z`]
    #[test]
    fn div_borrow() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = &a / &b;
        assert_eq!(c, Q::from((5, 28)));
    }

    /// Testing division for borrowed [`Q`] and [`Z`]
    #[test]
    fn div_first_borrowed() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = &a / b;
        assert_eq!(c, Q::from((5, 28)));
    }

    /// Testing division for [`Q`] and borrowed [`Z`]
    #[test]
    fn div_second_borrowed() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = a / &b;
        assert_eq!(c, Q::from((5, 28)));
    }

    /// Testing division for large numbers
    #[test]
    fn div_large_numbers() {
        let a: Q = Q::from((u64::MAX, 2));
        let b: Q = Q::from((1, u64::MAX));
        let c: Z = Z::from(u64::MAX);

        let d: Q = a / &c;
        let e: Q = b / c;

        assert_eq!(d, Q::from((u64::MAX, 2)) / Q::from(u64::MAX));
        assert_eq!(e, Q::from((1, u64::MAX)) / Q::from(u64::MAX));
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero() {
        let a: Q = Q::from((2, 3));
        let b: Z = Z::ZERO;
        let _c = a / b;
    }
}

#[cfg(test)]
mod test_div_between_types {
    use crate::rational::Q;

    /// Testing division between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn div() {
        let a: Q = Q::from(42);
        let b: u64 = 1;
        let c: u32 = 1;
        let d: u16 = 1;
        let e: u8 = 1;
        let f: i64 = 1;
        let g: i32 = 1;
        let h: i16 = 1;
        let i: i8 = 1;
        let j: f32 = 0.3;
        let k: f64 = 0.3;

        let _: Q = &a / &b;
        let _: Q = &a / &c;
        let _: Q = &a / &d;
        let _: Q = &a / &e;
        let _: Q = &a / &f;
        let _: Q = &a / &g;
        let _: Q = &a / &h;
        let _: Q = &a / &i;
        let _: Q = &a / &j;
        let _: Q = &a / &k;

        let _: Q = &b / &a;
        let _: Q = &c / &a;
        let _: Q = &d / &a;
        let _: Q = &e / &a;
        let _: Q = &f / &a;
        let _: Q = &g / &a;
        let _: Q = &h / &a;
        let _: Q = &i / &a;
        let _: Q = &j / &a;
        let _: Q = &k / &a;

        let _: Q = &a / b;
        let _: Q = &a / c;
        let _: Q = &a / d;
        let _: Q = &a / e;
        let _: Q = &a / f;
        let _: Q = &a / g;
        let _: Q = &a / h;
        let _: Q = &a / i;
        let _: Q = &a / j;
        let _: Q = &a / k;

        let _: Q = &b / Q::from(42);
        let _: Q = &c / Q::from(42);
        let _: Q = &d / Q::from(42);
        let _: Q = &e / Q::from(42);
        let _: Q = &f / Q::from(42);
        let _: Q = &g / Q::from(42);
        let _: Q = &h / Q::from(42);
        let _: Q = &i / Q::from(42);
        let _: Q = &j / Q::from(42);
        let _: Q = &k / Q::from(42);

        let _: Q = Q::from(42) / &b;
        let _: Q = Q::from(42) / &c;
        let _: Q = Q::from(42) / &d;
        let _: Q = Q::from(42) / &e;
        let _: Q = Q::from(42) / &f;
        let _: Q = Q::from(42) / &g;
        let _: Q = Q::from(42) / &h;
        let _: Q = Q::from(42) / &i;
        let _: Q = Q::from(42) / &j;
        let _: Q = Q::from(42) / &k;

        let _: Q = b / &a;
        let _: Q = c / &a;
        let _: Q = d / &a;
        let _: Q = e / &a;
        let _: Q = f / &a;
        let _: Q = g / &a;
        let _: Q = h / &a;
        let _: Q = i / &a;
        let _: Q = j / &a;
        let _: Q = k / &a;

        let _: Q = Q::from(42) / b;
        let _: Q = Q::from(42) / c;
        let _: Q = Q::from(42) / d;
        let _: Q = Q::from(42) / e;
        let _: Q = Q::from(42) / f;
        let _: Q = Q::from(42) / g;
        let _: Q = Q::from(42) / h;
        let _: Q = Q::from(42) / i;
        let _: Q = Q::from(42) / j;
        let _: Q = Q::from(42) / k;

        let _: Q = b / Q::from(42);
        let _: Q = c / Q::from(42);
        let _: Q = d / Q::from(42);
        let _: Q = e / Q::from(42);
        let _: Q = f / Q::from(42);
        let _: Q = g / Q::from(42);
        let _: Q = h / Q::from(42);
        let _: Q = i / Q::from(42);
        let _: Q = j / Q::from(42);
        let _: Q = k / Q::from(42);
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero_u64() {
        let a: Q = Q::from(23);
        let b: u64 = 0;
        let _c = a / b;
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero_u32() {
        let a: Q = Q::from(23);
        let b: u32 = 0;
        let _c = a / b;
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero_u16() {
        let a: Q = Q::from(23);
        let b: u16 = 0;
        let _c = a / b;
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero_u8() {
        let a: Q = Q::from(23);
        let b: u8 = 0;
        let _c = a / b;
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero_i64() {
        let a: Q = Q::from(23);
        let b: i64 = 0;
        let _c = a / b;
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero_i32() {
        let a: Q = Q::from(23);
        let b: i32 = 0;
        let _c = a / b;
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero_i16() {
        let a: Q = Q::from(23);
        let b: i16 = 0;
        let _c = a / b;
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero_i8() {
        let a: Q = Q::from(23);
        let b: i8 = 0;
        let _c = a / b;
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero_f32() {
        let a: Q = Q::from(23);
        let b: f32 = 0.0;
        let _c = a / b;
    }

    /// Testing division by `0` panics
    #[test]
    #[should_panic]
    fn div_by_zero_f64() {
        let a: Q = Q::from(23);
        let b: f64 = 0.0;
        let _c = a / b;
    }

    /// Testing if division for different types returns the correct results.
    #[test]
    fn div_correct_i32() {
        let a: i32 = 1;
        let b: Q = Q::from(23);

        let c = a / &b;
        let d = &b / a;

        assert_eq!(c, Q::from((1, 23)));
        assert_eq!(d, Q::from(23));
    }
}
