// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`Z`] values.

use super::super::Z;
use crate::macros::arithmetics::{
    arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
    arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpz::fmpz_mul;
use std::ops::Mul;

impl Mul for &Z {
    type Output = Z;
    /// Implements the [`Mul`] trait for two [`Z`] values.
    /// [`Mul`] is implemented for any combination of [`Z`] and borrowed [`Z`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both numbers as a [`Z`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Z = Z::from(24);
    ///
    /// let c: Z = &a * &b;
    /// let d: Z = a * b;
    /// let e: Z = &c * d;
    /// let f: Z = c * &e;
    /// ```
    fn mul(self, other: Self) -> Self::Output {
        let mut out = Z::default();
        unsafe {
            fmpz_mul(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, Z, Z);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, Z, Z);
arithmetic_between_types!(Mul, mul, Z, i64 i32 i16 i8 u64 u32 u16 u8);

#[cfg(test)]
mod test_mul_between_types {

    use crate::integer::Z;
    use std::str::FromStr;

    /// testing multiplication between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn mul() {
        let a: Z = Z::from_str("42").unwrap();
        let b: u64 = 5;
        let c: u32 = 5;
        let d: u16 = 5;
        let e: u8 = 5;
        let f: i64 = 5;
        let g: i32 = 5;
        let h: i16 = 5;
        let i: i8 = 5;
        let _: Z = &a * &b;
        let _: Z = &a * &c;
        let _: Z = &a * &d;
        let _: Z = &a * &e;
        let _: Z = &a * &f;
        let _: Z = &a * &g;
        let _: Z = &a * &h;
        let _: Z = &a * &i;

        let _: Z = &b * &a;
        let _: Z = &c * &a;
        let _: Z = &d * &a;
        let _: Z = &e * &a;
        let _: Z = &f * &a;
        let _: Z = &g * &a;
        let _: Z = &h * &a;
        let _: Z = &i * &a;

        let _: Z = &a * b;
        let _: Z = &a * c;
        let _: Z = &a * d;
        let _: Z = &a * e;
        let _: Z = &a * f;
        let _: Z = &a * g;
        let _: Z = &a * h;
        let _: Z = &a * i;

        let _: Z = &b * Z::from_str("42").unwrap();
        let _: Z = &c * Z::from_str("42").unwrap();
        let _: Z = &d * Z::from_str("42").unwrap();
        let _: Z = &e * Z::from_str("42").unwrap();
        let _: Z = &f * Z::from_str("42").unwrap();
        let _: Z = &g * Z::from_str("42").unwrap();
        let _: Z = &h * Z::from_str("42").unwrap();
        let _: Z = &i * Z::from_str("42").unwrap();

        let _: Z = Z::from_str("42").unwrap() * &b;
        let _: Z = Z::from_str("42").unwrap() * &c;
        let _: Z = Z::from_str("42").unwrap() * &d;
        let _: Z = Z::from_str("42").unwrap() * &e;
        let _: Z = Z::from_str("42").unwrap() * &f;
        let _: Z = Z::from_str("42").unwrap() * &g;
        let _: Z = Z::from_str("42").unwrap() * &h;
        let _: Z = Z::from_str("42").unwrap() * &i;

        let _: Z = b * &a;
        let _: Z = c * &a;
        let _: Z = d * &a;
        let _: Z = e * &a;
        let _: Z = f * &a;
        let _: Z = g * &a;
        let _: Z = h * &a;
        let _: Z = i * &a;

        let _: Z = Z::from_str("42").unwrap() * b;
        let _: Z = Z::from_str("42").unwrap() * c;
        let _: Z = Z::from_str("42").unwrap() * d;
        let _: Z = Z::from_str("42").unwrap() * e;
        let _: Z = Z::from_str("42").unwrap() * f;
        let _: Z = Z::from_str("42").unwrap() * g;
        let _: Z = Z::from_str("42").unwrap() * h;
        let _: Z = Z::from_str("42").unwrap() * i;

        let _: Z = b * Z::from_str("42").unwrap();
        let _: Z = c * Z::from_str("42").unwrap();
        let _: Z = d * Z::from_str("42").unwrap();
        let _: Z = e * Z::from_str("42").unwrap();
        let _: Z = f * Z::from_str("42").unwrap();
        let _: Z = g * Z::from_str("42").unwrap();
        let _: Z = h * Z::from_str("42").unwrap();
        let _: Z = i * Z::from_str("42").unwrap();
    }
}

#[cfg(test)]
mod test_mul {

    use super::Z;

    /// testing multiplication for two [`Z`]
    #[test]
    fn mul() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = a * b;
        assert_eq!(c, Z::from(168));
    }

    /// testing multiplication for two borrowed [`Z`]
    #[test]
    fn mul_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = &a * &b;
        assert_eq!(c, Z::from(168));
    }

    /// testing multiplication for borrowed [`Z`] and [`Z`]
    #[test]
    fn mul_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = &a * b;
        assert_eq!(c, Z::from(168));
    }

    /// testing multiplication for [`Z`] and borrowed [`Z`]
    #[test]
    fn mul_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = a * &b;
        assert_eq!(c, Z::from(168));
    }

    /// testing multiplication for big [`Z`]
    #[test]
    fn mul_large_numbers() {
        let a: Z = Z::from(i64::MAX);
        let b: Z = Z::from(2);
        let c: Z = Z::from(i32::MIN);
        let d: Z = Z::from(i32::MAX);
        let e: Z = a * b;
        let f: Z = c * d;
        assert_eq!(e, Z::from(u64::MAX - 1));
        assert_eq!(f, Z::from(i64::from(i32::MAX) * i64::from(i32::MIN)));
    }
}
