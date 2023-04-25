// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`Z`] values.

use super::super::Z;
use crate::{
    macros::arithmetics::{
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
    rational::Q,
};
use flint_sys::{fmpq::fmpq_add_fmpz, fmpz::fmpz_add};
use std::ops::Add;

impl Add for &Z {
    type Output = Z;
    /// Implements the [`Add`] trait for two [`Z`] values.
    /// [`Add`] is implemented for any combination of [`Z`] and borrowed [`Z`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Z = Z::from(24);
    ///
    /// let c: Z = &a + &b;
    /// let d: Z = a + b;
    /// let e: Z = &c + d;
    /// let f: Z = c + &e;
    /// ```
    fn add(self, other: Self) -> Self::Output {
        let mut out = Z::default();
        unsafe {
            fmpz_add(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Z, Z, Z);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Z, Z, Z);
arithmetic_between_types!(Add, add, Z, Z, i64 i32 i16 i8 u64 u32 u16 u8);

impl Add<&Q> for &Z {
    type Output = Q;

    /// Implements the [`Add`] trait for [`Z`] and [`Q`] values.
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
    /// let a: Z = Z::from_str("-42").unwrap();
    /// let b: Q = Q::from_str("42/19").unwrap();
    ///
    /// let c: Q = &a + &b;
    /// let d: Q = a + b;
    /// let e: Q = &c + d;
    /// let f: Q = c + &e;
    /// ```
    fn add(self, other: &Q) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_add_fmpz(&mut out.value, &other.value, &self.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Z, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Z, Q, Q);

#[cfg(test)]
mod test_add_between_types {

    use crate::integer::Z;
    use std::str::FromStr;

    /// testing addition between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn add() {
        let a: Z = Z::from(42);
        let b: u64 = 1;
        let c: u32 = 1;
        let d: u16 = 1;
        let e: u8 = 1;
        let f: i64 = 1;
        let g: i32 = 1;
        let h: i16 = 1;
        let i: i8 = 1;
        let _: Z = &a + &b;
        let _: Z = &a + &c;
        let _: Z = &a + &d;
        let _: Z = &a + &e;
        let _: Z = &a + &f;
        let _: Z = &a + &g;
        let _: Z = &a + &h;
        let _: Z = &a + &i;

        let _: Z = &b + &a;
        let _: Z = &c + &a;
        let _: Z = &d + &a;
        let _: Z = &e + &a;
        let _: Z = &f + &a;
        let _: Z = &g + &a;
        let _: Z = &h + &a;
        let _: Z = &i + &a;

        let _: Z = &a + b;
        let _: Z = &a + c;
        let _: Z = &a + d;
        let _: Z = &a + e;
        let _: Z = &a + f;
        let _: Z = &a + g;
        let _: Z = &a + h;
        let _: Z = &a + i;

        let _: Z = &b + Z::from_str("42").unwrap();
        let _: Z = &c + Z::from_str("42").unwrap();
        let _: Z = &d + Z::from_str("42").unwrap();
        let _: Z = &e + Z::from_str("42").unwrap();
        let _: Z = &f + Z::from_str("42").unwrap();
        let _: Z = &g + Z::from_str("42").unwrap();
        let _: Z = &h + Z::from_str("42").unwrap();
        let _: Z = &i + Z::from_str("42").unwrap();

        let _: Z = Z::from_str("42").unwrap() + &b;
        let _: Z = Z::from_str("42").unwrap() + &c;
        let _: Z = Z::from_str("42").unwrap() + &d;
        let _: Z = Z::from_str("42").unwrap() + &e;
        let _: Z = Z::from_str("42").unwrap() + &f;
        let _: Z = Z::from_str("42").unwrap() + &g;
        let _: Z = Z::from_str("42").unwrap() + &h;
        let _: Z = Z::from_str("42").unwrap() + &i;

        let _: Z = b + &a;
        let _: Z = c + &a;
        let _: Z = d + &a;
        let _: Z = e + &a;
        let _: Z = f + &a;
        let _: Z = g + &a;
        let _: Z = h + &a;
        let _: Z = i + &a;

        let _: Z = Z::from_str("42").unwrap() + b;
        let _: Z = Z::from_str("42").unwrap() + c;
        let _: Z = Z::from_str("42").unwrap() + d;
        let _: Z = Z::from_str("42").unwrap() + e;
        let _: Z = Z::from_str("42").unwrap() + f;
        let _: Z = Z::from_str("42").unwrap() + g;
        let _: Z = Z::from_str("42").unwrap() + h;
        let _: Z = Z::from_str("42").unwrap() + i;

        let _: Z = b + Z::from_str("42").unwrap();
        let _: Z = c + Z::from_str("42").unwrap();
        let _: Z = d + Z::from_str("42").unwrap();
        let _: Z = e + Z::from_str("42").unwrap();
        let _: Z = f + Z::from_str("42").unwrap();
        let _: Z = g + Z::from_str("42").unwrap();
        let _: Z = h + Z::from_str("42").unwrap();
        let _: Z = i + Z::from_str("42").unwrap();
    }
}

#[cfg(test)]
mod test_add_between_z_and_q {

    use super::Z;
    use crate::rational::Q;
    use std::str::FromStr;

    /// testing addition for [`Z`] and [`Q`]
    #[test]
    fn add() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = a + b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for both borrowed [`Z`] and [`Q`]
    #[test]
    fn add_borrow() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = &a + &b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for borrowed [`Z`] and [`Q`]
    #[test]
    fn add_first_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = &a + b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for [`Z`] and borrowed [`Q`]
    #[test]
    fn add_second_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from_str("5/7").unwrap();
        let c: Q = a + &b;
        assert_eq!(c, Q::from_str("33/7").unwrap());
    }

    /// testing addition for big numbers
    #[test]
    fn add_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Q = Q::from_str(&format!("1/{}", u64::MAX)).unwrap();
        let c: Q = Q::from_str(&format!("{}/2", u64::MAX)).unwrap();
        let d: Q = &a + b;
        let e: Q = a + c;
        assert_eq!(
            d,
            Q::from_str(&format!("1/{}", u64::MAX)).unwrap()
                + Q::from_str(&format!("{}/1", u64::MAX)).unwrap()
        );
        assert_eq!(
            e,
            Q::from_str(&format!("{}/1", u64::MAX)).unwrap()
                + Q::from_str(&format!("{}/2", u64::MAX)).unwrap()
        );
    }
}

#[cfg(test)]
mod test_add {

    use super::Z;

    /// testing addition for two [`Z`]
    #[test]
    fn add() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a + b;
        assert_eq!(c, Z::from(66));
    }

    /// testing addition for two borrowed [`Z`]
    #[test]
    fn add_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a + &b;
        assert_eq!(c, Z::from(66));
    }

    /// testing addition for borrowed [`Z`] and [`Z`]
    #[test]
    fn add_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a + b;
        assert_eq!(c, Z::from(66));
    }

    /// testing addition for [`Z`] and borrowed [`Z`]
    #[test]
    fn add_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a + &b;
        assert_eq!(c, Z::from(66));
    }

    /// testing addition for big numbers
    #[test]
    fn add_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Z = Z::from(-221319874);
        let c: Z = Z::from(i64::MIN);
        let d: Z = &a + b;
        let e: Z = a + c;
        assert_eq!(d, Z::from(u64::MAX - 221319874));
        assert_eq!(e, Z::from(i64::MAX));
    }
}
