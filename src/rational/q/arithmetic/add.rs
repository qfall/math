// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`Q`] values.

use super::super::Q;
use crate::{
    integer::Z,
    integer_mod_q::Zq,
    macros::arithmetics::{
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpq::{fmpq_add, fmpq_add_fmpz};
use std::ops::Add;

impl Add for &Q {
    type Output = Q;

    /// Implements the [`Add`] trait for two [`Q`] values.
    /// [`Add`] is implemented for any combination of [`Q`] and borrowed [`Q`].
    ///
    /// Parameters:
    ///  - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both rationals as a [`Q`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from(42);
    /// let b: Q = Q::from_str("-42/2").unwrap();
    ///
    /// let c: Q = &a + &b;
    /// let d: Q = a + b;
    /// let e: Q = &c + d;
    /// let f: Q = c + &e;
    /// ```
    fn add(self, other: Self) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_add(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Q, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Q, Q, Q);
arithmetic_between_types!(Add, add, Q, Q, i64 i32 i16 i8 u64 u32 u16 u8 f32 f64);

impl Add<&Z> for &Q {
    type Output = Q;

    /// Implements the [`Add`] trait for [`Q`] and [`Z`] values.
    /// [`Add`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Q`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from_str("42/19").unwrap();
    /// let b: Z = Z::from_str("-42").unwrap();
    ///
    /// let c: Q = &a + &b;
    /// let d: Q = a + b;
    /// let e: Q = &c + Z::from(42);
    /// let f: Q = c + &Z::from(42);
    /// ```
    fn add(self, other: &Z) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_add_fmpz(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Q, Z, Q);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Q, Z, Q);

impl Add<&Zq> for &Q {
    type Output = Q;

    /// Implements the [`Add`] trait for [`Q`] and [`Zq`] values.
    /// [`Add`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Q`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer_mod_q::Zq;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from_str("42/19").unwrap();
    /// let b: Zq = Zq::from_str("42 mod 11").unwrap();
    ///
    /// let c: Q = &a + &b;
    /// let d: Q = a + b;
    /// let e: Q = &c + Zq::from_str("42 mod 11").unwrap();
    /// let f: Q = c + &Zq::from_str("42 mod 11").unwrap();
    /// ```
    fn add(self, other: &Zq) -> Self::Output {
        self + Z::from(other.clone()) // todo do it more efficient -> later
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Q, Zq, Q);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Q, Zq, Q);

#[cfg(test)]
mod test_add {
    use super::Q;
    use std::str::FromStr;

    /// testing addition for two [`Q`]
    #[test]
    fn add() {
        let a: Q = Q::from(42);
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a + b;
        assert_eq!(c, Q::from_str("63").unwrap());
    }

    /// testing addition for two borrowed [`Q`]
    #[test]
    fn add_borrow() {
        let a: Q = Q::from(42);
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = &a + &b;
        assert_eq!(c, Q::from_str("63").unwrap());
    }

    /// testing addition for borrowed [`Q`] and [`Q`]
    #[test]
    fn add_first_borrowed() {
        let a: Q = Q::from_str("42/5").unwrap();
        let b: Q = Q::from_str("42/10").unwrap();
        let c: Q = &a + b;
        assert_eq!(c, Q::from_str("63/5").unwrap());
    }

    /// testing addition for [`Q`] and borrowed [`Q`]
    #[test]
    fn add_second_borrowed() {
        let a: Q = Q::from(42);
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a + &b;
        assert_eq!(c, Q::from_str("63").unwrap());
    }

    #[test]
    /// testing addition for large numerators and divisors
    fn add_large() {
        let a: Q = Q::from_str(&(i64::MAX).to_string()).unwrap();
        let b: Q = Q::from_str(&(u64::MAX - 1).to_string()).unwrap();
        let c: Q = Q::from_str(&format!("1/{}", (i32::MAX))).unwrap();
        let d: Q = Q::from_str(&format!("1/{}", (u32::MAX))).unwrap();
        let e: Q = &a + &a;
        let f: Q = c + d;
        assert_eq!(e, b);
        assert_eq!(
            f,
            Q::from_str(&format!(
                "{}/{}",
                u64::from(u32::MAX) + u64::from((u32::MAX - 1) / 2),
                u64::from(u32::MAX) * u64::from((u32::MAX - 1) / 2)
            ))
            .unwrap()
        );
    }
}

#[cfg(test)]
mod test_add_between_q_and_z {

    use crate::integer::Z;
    use crate::rational::Q;
    use std::str::FromStr;

    /// testing addition for [`Q`] and [`Z`]
    #[test]
    fn add() {
        let a: Q = Q::from_str("5/7").unwrap();
        let b: Z = Z::from(4);
        let c: Q = a + b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for both borrowed [`Q`] and [`Z`]
    #[test]
    fn add_borrow() {
        let a: Q = Q::from_str("5/7").unwrap();
        let b: Z = Z::from(4);
        let c: Q = &a + &b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for borrowed [`Q`] and [`Z`]
    #[test]
    fn add_first_borrowed() {
        let a: Q = Q::from_str("5/7").unwrap();
        let b: Z = Z::from(4);
        let c: Q = &a + b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for [`Q`] and borrowed [`Z`]
    #[test]
    fn add_second_borrowed() {
        let a: Q = Q::from_str("5/7").unwrap();
        let b: Z = Z::from(4);
        let c: Q = a + &b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for big numbers
    #[test]
    fn add_large_numbers() {
        let a: Q = Q::from_str(&format!("{}/2", u64::MAX)).unwrap();
        let b: Q = Q::from_str(&format!("1/{}", u64::MAX)).unwrap();
        let c: Z = Z::from(u64::MAX);
        let d: Q = a + &c;
        let e: Q = b + c;
        assert_eq!(
            d,
            Q::from_str(&format!("{}/1", u64::MAX)).unwrap()
                + Q::from_str(&format!("{}/2", u64::MAX)).unwrap()
        );
        assert_eq!(
            e,
            Q::from_str(&format!("1/{}", u64::MAX)).unwrap()
                + Q::from_str(&format!("{}/1", u64::MAX)).unwrap()
        );
    }
}

#[cfg(test)]
mod test_add_between_q_and_zq {

    use crate::integer_mod_q::Zq;
    use crate::rational::Q;
    use std::str::FromStr;

    /// testing addition for [`Q`] and [`Zq`]
    #[test]
    fn add() {
        let a: Q = Q::from_str("5/7").unwrap();
        let b: Zq = Zq::try_from_int_int(4, 17).unwrap();
        let c: Q = a + b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for both borrowed [`Q`] and [`Zq`]
    #[test]
    fn add_borrow() {
        let a: Q = Q::from_str("5/7").unwrap();
        let b: Zq = Zq::try_from_int_int(4, 17).unwrap();
        let c: Q = &a + &b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for borrowed [`Q`] and [`Zq`]
    #[test]
    fn add_first_borrowed() {
        let a: Q = Q::from_str("5/7").unwrap();
        let b: Zq = Zq::try_from_int_int(4, 17).unwrap();
        let c: Q = &a + b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for [`Q`] and borrowed [`Zq`]
    #[test]
    fn add_second_borrowed() {
        let a: Q = Q::from_str("5/7").unwrap();
        let b: Zq = Zq::try_from_int_int(4, 17).unwrap();
        let c: Q = a + &b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for big numbers
    #[test]
    fn add_large_numbers() {
        let a: Q = Q::from_str(&format!("{}/2", u64::MAX)).unwrap();
        let b: Q = Q::from_str(&format!("1/{}", u64::MAX)).unwrap();
        let c: Zq = Zq::try_from_int_int(i64::MAX, u64::MAX - 58).unwrap();
        let d: Q = a + &c;
        let e: Q = b + c;
        assert_eq!(
            d,
            Q::from_str(&format!("{}/1", i64::MAX)).unwrap()
                + Q::from_str(&format!("{}/2", u64::MAX)).unwrap()
        );
        assert_eq!(
            e,
            Q::from_str(&format!("1/{}", u64::MAX)).unwrap()
                + Q::from_str(&format!("{}/1", i64::MAX)).unwrap()
        );
    }
}

#[cfg(test)]
mod test_add_between_types {

    use crate::rational::Q;

    /// testing addition between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn add() {
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
        let _: Q = &a + &b;
        let _: Q = &a + &c;
        let _: Q = &a + &d;
        let _: Q = &a + &e;
        let _: Q = &a + &f;
        let _: Q = &a + &g;
        let _: Q = &a + &h;
        let _: Q = &a + &i;
        let _: Q = &a + &j;
        let _: Q = &a + &k;

        let _: Q = &b + &a;
        let _: Q = &c + &a;
        let _: Q = &d + &a;
        let _: Q = &e + &a;
        let _: Q = &f + &a;
        let _: Q = &g + &a;
        let _: Q = &h + &a;
        let _: Q = &i + &a;
        let _: Q = &j + &a;
        let _: Q = &k + &a;

        let _: Q = &a + b;
        let _: Q = &a + c;
        let _: Q = &a + d;
        let _: Q = &a + e;
        let _: Q = &a + f;
        let _: Q = &a + g;
        let _: Q = &a + h;
        let _: Q = &a + i;
        let _: Q = &a + j;
        let _: Q = &a + k;

        let _: Q = &b + Q::from(42);
        let _: Q = &c + Q::from(42);
        let _: Q = &d + Q::from(42);
        let _: Q = &e + Q::from(42);
        let _: Q = &f + Q::from(42);
        let _: Q = &g + Q::from(42);
        let _: Q = &h + Q::from(42);
        let _: Q = &i + Q::from(42);
        let _: Q = &j + Q::from(42);
        let _: Q = &k + Q::from(42);

        let _: Q = Q::from(42) + &b;
        let _: Q = Q::from(42) + &c;
        let _: Q = Q::from(42) + &d;
        let _: Q = Q::from(42) + &e;
        let _: Q = Q::from(42) + &f;
        let _: Q = Q::from(42) + &g;
        let _: Q = Q::from(42) + &h;
        let _: Q = Q::from(42) + &i;
        let _: Q = Q::from(42) + &j;
        let _: Q = Q::from(42) + &k;

        let _: Q = b + &a;
        let _: Q = c + &a;
        let _: Q = d + &a;
        let _: Q = e + &a;
        let _: Q = f + &a;
        let _: Q = g + &a;
        let _: Q = h + &a;
        let _: Q = i + &a;
        let _: Q = j + &a;
        let _: Q = k + &a;

        let _: Q = Q::from(42) + b;
        let _: Q = Q::from(42) + c;
        let _: Q = Q::from(42) + d;
        let _: Q = Q::from(42) + e;
        let _: Q = Q::from(42) + f;
        let _: Q = Q::from(42) + g;
        let _: Q = Q::from(42) + h;
        let _: Q = Q::from(42) + i;
        let _: Q = Q::from(42) + j;
        let _: Q = Q::from(42) + k;

        let _: Q = b + Q::from(42);
        let _: Q = c + Q::from(42);
        let _: Q = d + Q::from(42);
        let _: Q = e + Q::from(42);
        let _: Q = f + Q::from(42);
        let _: Q = g + Q::from(42);
        let _: Q = h + Q::from(42);
        let _: Q = i + Q::from(42);
        let _: Q = j + Q::from(42);
        let _: Q = k + Q::from(42);
    }
}
