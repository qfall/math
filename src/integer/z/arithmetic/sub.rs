// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`Z`] values.

use super::super::Z;
use crate::{
    integer_mod_q::Zq,
    macros::arithmetics::{
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
    rational::Q,
};
use flint_sys::{
    fmpq::{fmpq, fmpq_set_fmpz_frac, fmpq_sub},
    fmpz::{fmpz, fmpz_sub},
    fmpz_mod::fmpz_mod_sub_fmpz,
};
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
    /// # Examples
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
arithmetic_between_types!(Sub, sub, Z, Z, i64 i32 i16 i8 u64 u32 u16 u8);

impl Sub<&Q> for &Z {
    type Output = Q;

    /// Implements the [`Sub`] trait for [`Z`] and [`Q`] values.
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the result of the subtraction as a [`Q`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Z = Z::from_str("-42").unwrap();
    /// let b: Q = Q::from_str("42/19").unwrap();
    ///
    /// let c: Q = &a - &b;
    /// let d: Q = a - b;
    /// let e: Q = &c - d;
    /// let f: Q = c - &e;
    /// ```
    fn sub(self, other: &Q) -> Self::Output {
        let mut out = Q::default();
        let mut fmpq1 = fmpq::default();
        unsafe { fmpq_set_fmpz_frac(&mut fmpq1, &self.value, &fmpz(1)) }
        unsafe {
            fmpq_sub(&mut out.value, &fmpq1, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, Z, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, Z, Q, Q);

impl Sub<&Zq> for &Z {
    type Output = Zq;
    /// Implements the [`Sub`] trait for [`Z`] and [`Zq`] values.
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the result of subtraction of both numbers as a [`Zq`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Zq = Zq::from_str("42 mod 19").unwrap();
    ///
    /// let c: Zq = &a - &b;
    /// let d: Zq = a - b;
    /// let e: Zq = &Z::from(42) - d;
    /// let f: Zq = Z::from(42) - &e;
    /// ```
    fn sub(self, other: &Zq) -> Self::Output {
        let mut out = fmpz(0);
        unsafe {
            fmpz_mod_sub_fmpz(
                &mut out,
                &self.value,
                &other.value.value,
                &*other.modulus.modulus,
            );
        }
        Zq::from_z_modulus(&Z::from_fmpz(&out), &other.modulus)
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, Z, Zq, Zq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, Z, Zq, Zq);

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

#[cfg(test)]
mod test_sub_between_z_and_q {

    use super::Z;
    use crate::rational::Q;
    use std::str::FromStr;

    /// testing subtraction for [`Z`] and [`Q`]
    #[test]
    fn sub() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = a - b;
        assert_eq!(c, Q::from_str("23/7").unwrap());
    }

    /// testing subtraction for both borrowed [`Z`] and [`Q`]
    #[test]
    fn sub_borrow() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = &a - &b;
        assert_eq!(c, Q::from_str("23/7").unwrap());
    }

    /// testing subtraction for borrowed [`Z`] and [`Q`]
    #[test]
    fn sub_first_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = &a - b;
        assert_eq!(c, Q::from_str("23/7").unwrap());
    }

    /// testing subtraction for [`Z`] and borrowed [`Q`]
    #[test]
    fn sub_second_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = a - &b;
        assert_eq!(c, Q::from_str("23/7").unwrap());
    }

    /// testing subtraction for big numbers
    #[test]
    fn sub_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Q = Q::from_str(&format!("1/{}", u64::MAX)).unwrap();
        let c: Q = Q::from_str(&format!("{}/2", u64::MAX)).unwrap();
        let d: Q = &a - b;
        let e: Q = a - c;

        assert_eq!(
            d,
            Q::from_str(&format!("{}/1", u64::MAX)).unwrap()
                - Q::from_str(&format!("1/{}", u64::MAX)).unwrap()
        );
        assert_eq!(
            e,
            Q::from_str(&format!("{}/1", u64::MAX)).unwrap()
                - Q::from_str(&format!("{}/2", u64::MAX)).unwrap()
        );
    }
}

#[cfg(test)]
mod test_sub_between_z_and_zq {

    use super::Z;
    use crate::integer_mod_q::Zq;

    /// testing subtraction for [`Z`] and [`Zq`]
    #[test]
    fn sub() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::try_from((10, 11)).unwrap();
        let c: Zq = a - b;
        assert_eq!(c, Zq::try_from((10, 11)).unwrap());
    }

    /// testing subtraction for both borrowed [`Z`] and [`Zq`]
    #[test]
    fn sub_borrow() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::try_from((4, 11)).unwrap();
        let c: Zq = a - b;
        assert_eq!(c, Zq::try_from((5, 11)).unwrap());
    }

    /// testing subtraction for borrowed [`Z`] and [`Zq`]
    #[test]
    fn sub_first_borrowed() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::try_from((4, 11)).unwrap();
        let c: Zq = a - b;
        assert_eq!(c, Zq::try_from((5, 11)).unwrap());
    }

    /// testing subtraction for [`Z`] and borrowed [`Zq`]
    #[test]
    fn sub_second_borrowed() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::try_from((4, 11)).unwrap();
        let c: Zq = a - b;
        assert_eq!(c, Zq::try_from((5, 11)).unwrap());
    }

    /// testing subtraction for big numbers
    #[test]
    fn sub_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Zq = Zq::try_from((i64::MAX, u64::MAX - 58)).unwrap();
        let c: Zq = Zq::try_from((i64::MAX - 1, i64::MAX)).unwrap();

        let d: Zq = &a - b;
        let e: Zq = a - c;

        assert_eq!(
            d,
            Zq::try_from(((u64::MAX - 1) / 2 + 1, u64::MAX - 58)).unwrap()
        );
        assert_eq!(e, Zq::try_from((2, i64::MAX)).unwrap());
    }
}
