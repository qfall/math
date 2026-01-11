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
        arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
    rational::Q,
};
use flint_sys::{
    fmpq::{fmpq, fmpq_set_fmpz_frac, fmpq_sub},
    fmpz::{fmpz, fmpz_sub, fmpz_sub_si, fmpz_sub_ui},
    fmpz_mod::fmpz_mod_sub_fmpz,
};
use std::ops::{Sub, SubAssign};

impl SubAssign<&Z> for Z {
    /// Computes the subtraction of `self` and `other` reusing
    /// the memory of `self`.
    /// [`SubAssign`] can be used on [`Z`] in combination with
    /// [`Z`], [`i64`], [`i32`], [`i16`], [`i8`], [`u64`], [`u32`], [`u16`] and [`u8`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the difference of both numbers as a [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let mut a: Z = Z::from(42);
    /// let b: Z = Z::from(24);
    ///
    /// a -= &b;
    /// a -= b;
    /// a -= 5;
    /// ```
    fn sub_assign(&mut self, other: &Self) {
        unsafe { fmpz_sub(&mut self.value, &self.value, &other.value) };
    }
}
impl SubAssign<i64> for Z {
    /// Documentation at [`Z::sub_assign`].
    fn sub_assign(&mut self, other: i64) {
        unsafe { fmpz_sub_si(&mut self.value, &self.value, other) };
    }
}
impl SubAssign<u64> for Z {
    /// Documentation at [`Z::sub_assign`].
    fn sub_assign(&mut self, other: u64) {
        unsafe { fmpz_sub_ui(&mut self.value, &self.value, other) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(SubAssign, sub_assign, Z, Z);
arithmetic_assign_between_types!(SubAssign, sub_assign, Z, i64, i32 i16 i8);
arithmetic_assign_between_types!(SubAssign, sub_assign, Z, u64, u32 u16 u8);

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
    /// let e: Z = &Z::from(42) - d;
    /// let f: Z = Z::from(42) - &e;
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
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Z = Z::from(-42);
    /// let b: Q = Q::from((42, 19));
    ///
    /// let c: Q = &a - &b;
    /// let d: Q = a - b;
    /// let e: Q = &Z::from(42) - d;
    /// let f: Q = Z::from(42) - &e;
    /// ```
    fn sub(self, other: &Q) -> Self::Output {
        let mut out = Q::default();
        let mut fmpq_1 = fmpq::default();
        unsafe { fmpq_set_fmpz_frac(&mut fmpq_1, &self.value, &fmpz(1)) }
        unsafe {
            fmpq_sub(&mut out.value, &fmpq_1, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, Z, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, Z, Q, Q);
arithmetic_between_types!(Sub, sub, Z, Q, f64 f32);

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
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Zq = Zq::from((42, 19));
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
                other.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        Zq {
            modulus: other.modulus.clone(),
            value: Z { value: out },
        }
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, Z, Zq, Zq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, Z, Zq, Zq);

#[cfg(test)]
mod test_sub_assign {
    use crate::integer::Z;

    /// Ensure that `sub_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a: Z = Z::MINUS_ONE;
        let b = Z::ONE;
        let c = Z::MINUS_ONE;

        a -= &b;
        assert_eq!(-2, a);
        a -= &c;
        assert_eq!(-1, a);
        a -= &c;
        assert_eq!(0, a);
        a -= &c;
        assert_eq!(1, a);
        a -= &c;
        assert_eq!(2, a);
        a -= 2 * b;
        assert_eq!(0, a);
    }

    /// Ensure that `sub_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a: Z = Z::from(i64::MAX);
        let b = Z::from(i64::MAX as u64 + 1);
        let c = -1 * Z::from(u64::MAX);

        a -= b;
        assert_eq!(-1, a);
        a -= c;
        assert_eq!(u64::MAX - 1, a);
    }

    /// Ensure that `sub_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a: Z = Z::from(42);
        let b: Z = Z::from(1);

        a -= &b;
        a -= b;
        a -= 1_u8;
        a -= 1_u16;
        a -= 1_u32;
        a -= 1_u64;
        a -= 1_i8;
        a -= 1_i16;
        a -= 1_i32;
        a -= 1_i64;
    }
}

#[cfg(test)]
mod test_sub_between_types {
    use crate::integer::Z;

    /// Testing subtraction between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn sub() {
        let a: Z = Z::from(42);
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

        let _: Z = &b - Z::from(42);
        let _: Z = &c - Z::from(42);
        let _: Z = &d - Z::from(42);
        let _: Z = &e - Z::from(42);
        let _: Z = &f - Z::from(42);
        let _: Z = &g - Z::from(42);
        let _: Z = &h - Z::from(42);
        let _: Z = &i - Z::from(42);

        let _: Z = Z::from(42) - &b;
        let _: Z = Z::from(42) - &c;
        let _: Z = Z::from(42) - &d;
        let _: Z = Z::from(42) - &e;
        let _: Z = Z::from(42) - &f;
        let _: Z = Z::from(42) - &g;
        let _: Z = Z::from(42) - &h;
        let _: Z = Z::from(42) - &i;

        let _: Z = b - &a;
        let _: Z = c - &a;
        let _: Z = d - &a;
        let _: Z = e - &a;
        let _: Z = f - &a;
        let _: Z = g - &a;
        let _: Z = h - &a;
        let _: Z = i - &a;

        let _: Z = Z::from(42) - b;
        let _: Z = Z::from(42) - c;
        let _: Z = Z::from(42) - d;
        let _: Z = Z::from(42) - e;
        let _: Z = Z::from(42) - f;
        let _: Z = Z::from(42) - g;
        let _: Z = Z::from(42) - h;
        let _: Z = Z::from(42) - i;

        let _: Z = b - Z::from(42);
        let _: Z = c - Z::from(42);
        let _: Z = d - Z::from(42);
        let _: Z = e - Z::from(42);
        let _: Z = f - Z::from(42);
        let _: Z = g - Z::from(42);
        let _: Z = h - Z::from(42);
        let _: Z = i - Z::from(42);
    }
}

#[cfg(test)]
mod test_sub {
    use super::Z;

    /// Testing subtraction for two Z
    #[test]
    fn sub() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a - b;
        assert_eq!(c, Z::from(18));
    }

    /// Testing subtraction for two borrowed [`Z`]
    #[test]
    fn sub_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a - &b;
        assert_eq!(c, Z::from(18));
    }

    /// Testing subtraction for borrowed [`Z`] and [`Z`]
    #[test]
    fn sub_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a - b;
        assert_eq!(c, Z::from(18));
    }

    /// Testing subtraction for [`Z`] and borrowed [`Z`]
    #[test]
    fn sub_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a - &b;
        assert_eq!(c, Z::from(18));
    }

    /// Testing subtraction for large integers
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

    /// Ensuring subtraction between different types is available
    #[test]
    fn availability() {
        let a: Z = Z::from(42);
        let b: Q = Q::from((5, 7));

        let _: Q = &a - &b;
        let _: Q = &a - b.clone();
        let _: Q = a.clone() - &b;
        let _: Q = a.clone() - b;
        let _: Q = &a - 0.5_f32;
        let _: Q = &a - 0.5_f64;
        let _: Q = a.clone() - 0.5_f32;
        let _: Q = a.clone() - 0.5_f64;
        let _: Q = 0.5_f32 - &a;
        let _: Q = 0.5_f64 - &a;
        let _: Q = 0.5_f32 - a.clone();
        let _: Q = 0.5_f64 - a.clone();
    }

    /// Ensures that division is performed the right way around
    #[test]
    fn order_retained() {
        let a = Z::from(4);

        assert_eq!(2, &a - 2);
        assert_eq!(Q::from((-2, 1)), 2 - &a);
    }

    /// Testing subtraction for [`Z`] and [`Q`]
    #[test]
    fn sub() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = a - b;
        assert_eq!(c, Q::from((23, 7)));
    }

    /// Testing subtraction for both borrowed [`Z`] and [`Q`]
    #[test]
    fn sub_borrow() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = &a - &b;
        assert_eq!(c, Q::from((23, 7)));
    }

    /// Testing subtraction for borrowed [`Z`] and [`Q`]
    #[test]
    fn sub_first_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = &a - b;
        assert_eq!(c, Q::from((23, 7)));
    }

    /// Testing subtraction for [`Z`] and borrowed [`Q`]
    #[test]
    fn sub_second_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = a - &b;
        assert_eq!(c, Q::from((23, 7)));
    }

    /// Testing subtraction for large numbers
    #[test]
    fn sub_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Q = Q::from((1, u64::MAX));
        let c: Q = Q::from((u64::MAX, 2));

        let d: Q = &a - b;
        let e: Q = a - c;

        assert_eq!(d, Q::from(u64::MAX) - Q::from((1, u64::MAX)));
        assert_eq!(e, Q::from(u64::MAX) - Q::from((u64::MAX, 2)));
    }
}

#[cfg(test)]
mod test_sub_between_z_and_zq {
    use super::Z;
    use crate::integer_mod_q::Zq;

    /// Testing subtraction for [`Z`] and [`Zq`]
    #[test]
    fn sub() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((10, 11));
        let c: Zq = a - b;
        assert_eq!(c, Zq::from((10, 11)));
    }

    /// Testing subtraction for both borrowed [`Z`] and [`Zq`]
    #[test]
    fn sub_borrow() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = &a - &b;
        assert_eq!(c, Zq::from((5, 11)));
    }

    /// Testing subtraction for borrowed [`Z`] and [`Zq`]
    #[test]
    fn sub_first_borrowed() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = &a - b;
        assert_eq!(c, Zq::from((5, 11)));
    }

    /// Testing subtraction for [`Z`] and borrowed [`Zq`]
    #[test]
    fn sub_second_borrowed() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = a - &b;
        assert_eq!(c, Zq::from((5, 11)));
    }

    /// Testing subtraction for large numbers
    #[test]
    fn sub_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Zq = Zq::from((i64::MAX, u64::MAX - 58));
        let c: Zq = Zq::from((i64::MAX - 1, i64::MAX));

        let d: Zq = &a - b;
        let e: Zq = a - c;

        assert_eq!(d, Zq::from(((u64::MAX - 1) / 2 + 1, u64::MAX - 58)));
        assert_eq!(e, Zq::from((2, i64::MAX)));
    }
}
