// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`Z`] values.

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
    fmpq::fmpq_mul_fmpz,
    fmpz::{fmpz, fmpz_mul},
    fmpz_mod::fmpz_mod_mul_fmpz,
};
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
    /// # Examples
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
arithmetic_between_types!(Mul, mul, Z, Z, i64 i32 i16 i8 u64 u32 u16 u8);

impl Mul<&Q> for &Z {
    type Output = Q;

    /// Implements the [`Mul`] trait for [`Z`] and [`Q`] values.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both numbers as a [`Q`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Z = Z::from(-42);
    /// let b: Q = Q::from_str("42/19").unwrap();
    ///
    /// let c: Q = &a * &b;
    /// let d: Q = a * b;
    /// let e: Q = &Z::from(42) * d;
    /// let f: Q = Z::from(42) * &e;
    /// ```
    fn mul(self, other: &Q) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_mul_fmpz(&mut out.value, &other.value, &self.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, Q, Q);

impl Mul<&Zq> for &Z {
    type Output = Zq;
    /// Implements the [`Mul`] trait for [`Z`] and [`Zq`] values.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both numbers as a [`Zq`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Zq = Zq::from((42, 9));
    ///
    /// let c: Zq = &a * &b;
    /// let d: Zq = a * b;
    /// let e: Zq = &Z::from(42) * d;
    /// let f: Zq = Z::from(42) * &e;
    /// ```
    fn mul(self, other: &Zq) -> Self::Output {
        let mut out = fmpz(0);
        unsafe {
            fmpz_mod_mul_fmpz(
                &mut out,
                &other.value.value,
                &self.value,
                other.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        Zq {
            modulus: other.modulus.clone(),
            value: Z { value: out },
        }
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, Zq, Zq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, Zq, Zq);

#[cfg(test)]
mod test_mul_between_types {
    use crate::integer::Z;

    /// Testing multiplication between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn mul() {
        let a: Z = Z::from(42);
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

        let _: Z = &b * Z::from(42);
        let _: Z = &c * Z::from(42);
        let _: Z = &d * Z::from(42);
        let _: Z = &e * Z::from(42);
        let _: Z = &f * Z::from(42);
        let _: Z = &g * Z::from(42);
        let _: Z = &h * Z::from(42);
        let _: Z = &i * Z::from(42);

        let _: Z = Z::from(42) * &b;
        let _: Z = Z::from(42) * &c;
        let _: Z = Z::from(42) * &d;
        let _: Z = Z::from(42) * &e;
        let _: Z = Z::from(42) * &f;
        let _: Z = Z::from(42) * &g;
        let _: Z = Z::from(42) * &h;
        let _: Z = Z::from(42) * &i;

        let _: Z = b * &a;
        let _: Z = c * &a;
        let _: Z = d * &a;
        let _: Z = e * &a;
        let _: Z = f * &a;
        let _: Z = g * &a;
        let _: Z = h * &a;
        let _: Z = i * &a;

        let _: Z = Z::from(42) * b;
        let _: Z = Z::from(42) * c;
        let _: Z = Z::from(42) * d;
        let _: Z = Z::from(42) * e;
        let _: Z = Z::from(42) * f;
        let _: Z = Z::from(42) * g;
        let _: Z = Z::from(42) * h;
        let _: Z = Z::from(42) * i;

        let _: Z = b * Z::from(42);
        let _: Z = c * Z::from(42);
        let _: Z = d * Z::from(42);
        let _: Z = e * Z::from(42);
        let _: Z = f * Z::from(42);
        let _: Z = g * Z::from(42);
        let _: Z = h * Z::from(42);
        let _: Z = i * Z::from(42);
    }
}

#[cfg(test)]
mod test_mul {
    use super::Z;

    /// Testing multiplication for two [`Z`]
    #[test]
    fn mul() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = a * b;
        assert_eq!(c, Z::from(168));
    }

    /// Testing multiplication for two borrowed [`Z`]
    #[test]
    fn mul_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = &a * &b;
        assert_eq!(c, Z::from(168));
    }

    /// Testing multiplication for borrowed [`Z`] and [`Z`]
    #[test]
    fn mul_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = &a * b;
        assert_eq!(c, Z::from(168));
    }

    /// Testing multiplication for [`Z`] and borrowed [`Z`]
    #[test]
    fn mul_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = a * &b;
        assert_eq!(c, Z::from(168));
    }

    /// Testing multiplication for big [`Z`]
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

#[cfg(test)]
mod test_mul_between_z_and_zq {
    use super::Z;
    use crate::integer_mod_q::Zq;

    /// Testing multiplication for [`Z`] and [`Zq`]
    #[test]
    fn mul() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = a * b;
        assert_eq!(c, Zq::from((3, 11)));
    }

    /// Testing multiplication for both borrowed [`Z`] and [`Zq`]
    #[test]
    fn mul_borrow() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = &a * &b;
        assert_eq!(c, Zq::from((3, 11)));
    }

    /// Testing multiplication for borrowed [`Z`] and [`Zq`]
    #[test]
    fn mul_first_borrowed() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = &a * b;
        assert_eq!(c, Zq::from((3, 11)));
    }

    /// Testing multiplication for [`Z`] and borrowed [`Zq`]
    #[test]
    fn mul_second_borrowed() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = a * &b;
        assert_eq!(c, Zq::from((3, 11)));
    }

    /// Testing multiplication for big numbers
    #[test]
    fn mul_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Zq = Zq::from((i64::MAX, u64::MAX - 58));
        let c: Zq = Zq::from((i64::MAX - 1, i64::MAX));

        let d: Zq = &a * b;
        let e: Zq = a * c;

        assert_eq!(
            d,
            Zq::from(((u64::MAX - 1) / 2, u64::MAX - 58)) * Zq::from((u64::MAX, u64::MAX - 58))
        );
        assert_eq!(e, Zq::from((u64::MAX, i64::MAX)) * Zq::from((-1, i64::MAX)));
    }
}

#[cfg(test)]
mod test_mul_between_z_and_q {
    use super::Z;
    use crate::rational::Q;
    use std::str::FromStr;

    /// Testing multiplication for [`Z`] and [`Q`]
    #[test]
    fn mul() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = a * b;
        assert_eq!(c, Q::from_str("20/7").unwrap());
    }

    /// Testing multiplication for both borrowed [`Z`] and [`Q`]
    #[test]
    fn mul_borrow() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = &a * &b;
        assert_eq!(c, Q::from_str("20/7").unwrap());
    }

    /// Testing multiplication for borrowed [`Z`] and [`Q`]
    #[test]
    fn mul_first_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = &a * b;
        assert_eq!(c, Q::from_str("20/7").unwrap());
    }

    /// Testing multiplication for [`Z`] and borrowed [`Q`]
    #[test]
    fn mul_second_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = a * &b;
        assert_eq!(c, Q::from_str("20/7").unwrap());
    }

    /// Testing multiplication for big numbers
    #[test]
    fn mul_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Q = Q::from_str(&format!("1/{}", u64::MAX)).unwrap();
        let c: Q = Q::from_str(&format!("{}/2", u64::MAX)).unwrap();

        let d: Q = &a * b;
        let e: Q = a * c;

        assert_eq!(
            d,
            Q::from_str(&format!("1/{}", u64::MAX)).unwrap()
                * Q::from_str(&format!("{}/1", u64::MAX)).unwrap()
        );
        assert_eq!(
            e,
            Q::from_str(&format!("{}/1", u64::MAX)).unwrap()
                * Q::from_str(&format!("{}/2", u64::MAX)).unwrap()
        );
    }
}
