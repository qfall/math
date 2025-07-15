// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`Q`] values.

use super::super::Q;
use crate::{
    integer::Z,
    macros::arithmetics::{
        arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpq::{fmpq_mul, fmpq_mul_fmpz, fmpq_mul_si, fmpq_mul_ui};
use std::ops::{Mul, MulAssign};

impl MulAssign<&Q> for Q {
    /// Computes the multiplication of `self` and `other` reusing
    /// the memory of `self`.
    /// [`MulAssign`] can be used on [`Q`] in combination with
    /// [`Q`], [`Z`], [`f64`], [`f32`], [`i64`], [`i32`], [`i16`], [`i8`], [`u64`], [`u32`], [`u16`] and [`u8`].
    ///
    /// Parameters:
    ///  - `other`: specifies the value to multiply to `self`
    ///
    /// Returns the product of both rationals as a [`Q`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{rational::Q, integer::Z};
    ///
    /// let mut a: Q = Q::from(42);
    /// let b: Q = Q::from((-42, 2));
    /// let c: Z = Z::from(5);
    ///
    /// a *= &b;
    /// a *= b;
    /// a *= 5;
    /// a *= c;
    /// a *= 5.0;
    /// ```
    fn mul_assign(&mut self, other: &Self) {
        unsafe { fmpq_mul(&mut self.value, &self.value, &other.value) };
    }
}
impl MulAssign<&Z> for Q {
    /// Documentation at [`Q::mul_assign`].
    fn mul_assign(&mut self, other: &Z) {
        unsafe { fmpq_mul_fmpz(&mut self.value, &self.value, &other.value) };
    }
}
impl MulAssign<i64> for Q {
    /// Documentation at [`Q::mul_assign`].
    fn mul_assign(&mut self, other: i64) {
        unsafe { fmpq_mul_si(&mut self.value, &self.value, other) };
    }
}
impl MulAssign<u64> for Q {
    /// Documentation at [`Q::mul_assign`].
    fn mul_assign(&mut self, other: u64) {
        unsafe { fmpq_mul_ui(&mut self.value, &self.value, other) };
    }
}
impl MulAssign<f64> for Q {
    /// Documentation at [`Q::mul_assign`].
    fn mul_assign(&mut self, other: f64) {
        let other = Q::from(other);

        unsafe { fmpq_mul(&mut self.value, &self.value, &other.value) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, Q, Q);
arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, Q, Z);
arithmetic_assign_between_types!(MulAssign, mul_assign, Q, i64, i32 i16 i8);
arithmetic_assign_between_types!(MulAssign, mul_assign, Q, u64, u32 u16 u8);
arithmetic_assign_between_types!(MulAssign, mul_assign, Q, f64, f32);

impl Mul for &Q {
    type Output = Q;
    /// Implements the [`Mul`] trait for two [`Q`] values.
    /// [`Mul`] is implemented for any combination of [`Q`] and borrowed [`Q`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both numbers as a [`Q`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from(42);
    /// let b: Q = Q::from(24);
    ///
    /// let c: Q = &a * &b;
    /// let d: Q = a * b;
    /// let e: Q = &c * d;
    /// let f: Q = c * &e;
    /// ```
    fn mul(self, other: Self) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_mul(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, Q, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Q, Q, Q);
arithmetic_between_types!(Mul, mul, Q, Q, i64 i32 i16 i8 u64 u32 u16 u8 f32 f64);

impl Mul<&Z> for &Q {
    type Output = Q;

    /// Implements the [`Mul`] trait for [`Q`] and [`Z`] values.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both numbers as a [`Q`].
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
    /// let c: Q = &a * &b;
    /// let d: Q = a * b;
    /// let e: Q = &c * Z::from(42);
    /// let f: Q = c * &Z::from(42);
    /// ```
    fn mul(self, other: &Z) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_mul_fmpz(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, Q, Z, Q);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Q, Z, Q);

#[cfg(test)]
mod test_mul_assign {
    use crate::{integer::Z, rational::Q};

    /// Ensure that `mul_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = Q::MINUS_ONE;
        let b = Q::MINUS_ONE;
        let c = Q::ZERO;
        let d = Q::from((-1, 2));

        a *= &b;
        assert_eq!(1, a);
        a *= &b;
        assert_eq!(-1, a);
        a *= &d;
        assert_eq!(Q::from((1, 2)), a);
        a *= &c;
        assert_eq!(0, a);
    }

    /// Ensure that `mul_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a: Q = Q::from((2, u64::MAX));
        let b = Q::from(u64::MAX);

        a *= b;

        assert_eq!(a, Q::from(2));
    }

    /// Ensure that `mul_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = Q::from((1, 2));
        let b = Q::from((4, 5));
        let c = Z::ONE;

        a *= &b;
        a *= b;
        a *= &c;
        a *= c;
        a *= 0.5_f64;
        a *= 0.5_f32;
        a *= 1_u8;
        a *= 1_u16;
        a *= 1_u32;
        a *= 1_u64;
        a *= 1_i8;
        a *= 1_i16;
        a *= 1_i32;
        a *= 1_i64;
    }
}

#[cfg(test)]
mod test_mul {
    use super::Q;
    use std::str::FromStr;

    /// Testing multiplication for two [`Q`]
    #[test]
    fn mul() {
        let a: Q = Q::from(2);
        let b: Q = Q::from((42, 2));
        let c: Q = a * b;
        assert_eq!(c, Q::from(42));
    }

    /// Testing multiplication for two borrowed [`Q`]
    #[test]
    fn mul_borrow() {
        let a: Q = Q::from(2);
        let b: Q = Q::from((42, 2));
        let c: Q = &a * &b;
        assert_eq!(c, Q::from(42));
    }

    /// Testing multiplication for borrowed [`Q`] and [`Q`]
    #[test]
    fn mul_first_borrowed() {
        let a: Q = Q::from(4);
        let b: Q = Q::from((42, 10));
        let c: Q = &a * b;
        assert_eq!(c, Q::from((168, 10)));
    }

    /// Testing multiplication for [`Q`] and borrowed [`Q`]
    #[test]
    fn mul_second_borrowed() {
        let a: Q = Q::from(2);
        let b: Q = Q::from((42, 2));
        let c: Q = a * &b;
        assert_eq!(c, Q::from(42));
    }

    /// Testing multiplication for large numerators and divisors
    #[test]
    fn mul_large() {
        let a: Q = Q::from(i64::MAX);
        let b: Q = Q::from(2);
        let c: Q = Q::from((1, i32::MAX));
        let d: Q = Q::from((1, u32::MAX));

        let e: Q = &a * &b;
        let f: Q = c * d;

        assert_eq!(e, Q::from(u64::MAX - 1));
        assert_eq!(
            f,
            Q::from_str(&format!(
                "1/{}",
                u64::from(u32::MAX) * u64::from((u32::MAX - 1) / 2)
            ))
            .unwrap()
        );
    }
}

#[cfg(test)]
mod test_mul_between_q_and_z {
    use crate::integer::Z;
    use crate::rational::Q;

    /// Testing multiplication for [`Q`] and [`Z`]
    #[test]
    fn mul() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = a * b;
        assert_eq!(c, Q::from((20, 7)));
    }

    /// Testing multiplication for both borrowed [`Q`] and [`Z`]
    #[test]
    fn mul_borrow() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = &a * &b;
        assert_eq!(c, Q::from((20, 7)));
    }

    /// Testing multiplication for borrowed [`Q`] and [`Z`]
    #[test]
    fn mul_first_borrowed() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = &a * b;
        assert_eq!(c, Q::from((20, 7)));
    }

    /// Testing multiplication for [`Q`] and borrowed [`Z`]
    #[test]
    fn mul_second_borrowed() {
        let a: Q = Q::from((5, 7));
        let b: Z = Z::from(4);
        let c: Q = a * &b;
        assert_eq!(c, Q::from((20, 7)));
    }

    /// Testing multiplication for large numbers
    #[test]
    fn mul_large_numbers() {
        let a: Q = Q::from((u64::MAX, 2));
        let b: Q = Q::from((1, u64::MAX));
        let c: Z = Z::from(u64::MAX);

        let d: Q = a * &c;
        let e: Q = b * c;

        assert_eq!(d, Q::from(u64::MAX) * Q::from((u64::MAX, 2)));
        assert_eq!(e, Q::from((1, u64::MAX)) * Q::from(u64::MAX));
    }
}

#[cfg(test)]
mod test_mul_between_types {
    use crate::rational::Q;

    /// Testing multiplication between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn mul() {
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

        let _: Q = &a * &b;
        let _: Q = &a * &c;
        let _: Q = &a * &d;
        let _: Q = &a * &e;
        let _: Q = &a * &f;
        let _: Q = &a * &g;
        let _: Q = &a * &h;
        let _: Q = &a * &i;
        let _: Q = &a * &j;
        let _: Q = &a * &k;

        let _: Q = &b * &a;
        let _: Q = &c * &a;
        let _: Q = &d * &a;
        let _: Q = &e * &a;
        let _: Q = &f * &a;
        let _: Q = &g * &a;
        let _: Q = &h * &a;
        let _: Q = &i * &a;
        let _: Q = &j * &a;
        let _: Q = &k * &a;

        let _: Q = &a * b;
        let _: Q = &a * c;
        let _: Q = &a * d;
        let _: Q = &a * e;
        let _: Q = &a * f;
        let _: Q = &a * g;
        let _: Q = &a * h;
        let _: Q = &a * i;
        let _: Q = &a * j;
        let _: Q = &a * k;

        let _: Q = &b * Q::from(42);
        let _: Q = &c * Q::from(42);
        let _: Q = &d * Q::from(42);
        let _: Q = &e * Q::from(42);
        let _: Q = &f * Q::from(42);
        let _: Q = &g * Q::from(42);
        let _: Q = &h * Q::from(42);
        let _: Q = &i * Q::from(42);
        let _: Q = &j * Q::from(42);
        let _: Q = &k * Q::from(42);

        let _: Q = Q::from(42) * &b;
        let _: Q = Q::from(42) * &c;
        let _: Q = Q::from(42) * &d;
        let _: Q = Q::from(42) * &e;
        let _: Q = Q::from(42) * &f;
        let _: Q = Q::from(42) * &g;
        let _: Q = Q::from(42) * &h;
        let _: Q = Q::from(42) * &i;
        let _: Q = Q::from(42) * &j;
        let _: Q = Q::from(42) * &k;

        let _: Q = b * &a;
        let _: Q = c * &a;
        let _: Q = d * &a;
        let _: Q = e * &a;
        let _: Q = f * &a;
        let _: Q = g * &a;
        let _: Q = h * &a;
        let _: Q = i * &a;
        let _: Q = j * &a;
        let _: Q = k * &a;

        let _: Q = Q::from(42) * b;
        let _: Q = Q::from(42) * c;
        let _: Q = Q::from(42) * d;
        let _: Q = Q::from(42) * e;
        let _: Q = Q::from(42) * f;
        let _: Q = Q::from(42) * g;
        let _: Q = Q::from(42) * h;
        let _: Q = Q::from(42) * i;
        let _: Q = Q::from(42) * j;
        let _: Q = Q::from(42) * k;

        let _: Q = b * Q::from(42);
        let _: Q = c * Q::from(42);
        let _: Q = d * Q::from(42);
        let _: Q = e * Q::from(42);
        let _: Q = f * Q::from(42);
        let _: Q = g * Q::from(42);
        let _: Q = h * Q::from(42);
        let _: Q = i * Q::from(42);
        let _: Q = j * Q::from(42);
        let _: Q = k * Q::from(42);
    }
}
