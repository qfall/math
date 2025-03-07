// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations of logic traits.

use crate::{
    integer::Z,
    macros::arithmetics::{
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpz::fmpz_or;
use std::ops::BitOr;

impl BitOr for &Z {
    type Output = Z;

    /// Computes the bit-wise logical `or` of `self` and `other`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to apply the bit-wise logical `or` action to
    ///     apart from `self`
    ///
    /// Returns a new instance of [`Z`] containing the number resulting
    /// from the bit-wise logical `or` operation performed on `self` and `other`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let a = Z::from(5);
    /// let b = Z::from(7);
    ///
    /// let c: Z = &a | &b;
    /// let d: Z = a | 1;
    /// let e: Z = b | 15_u64;
    /// ```
    fn bitor(self, other: Self) -> Self::Output {
        let mut out = Z::default();
        unsafe { fmpz_or(&mut out.value, &self.value, &other.value) };
        out
    }
}

arithmetic_trait_borrowed_to_owned!(BitOr, bitor, Z, Z, Z);
arithmetic_trait_mixed_borrowed_owned!(BitOr, bitor, Z, Z, Z);
arithmetic_between_types!(BitOr, bitor, Z, Z, i64 i32 i16 i8 u64 u32 u16 u8);

#[cfg(test)]
mod test_bitor {
    use super::Z;

    /// Testing `bitor` for two [`Z`]
    #[test]
    fn bitor() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);

        let c: Z = a | b;

        assert_eq!(Z::from(58), c);
    }

    /// Testing `bitor` for two borrowed [`Z`]
    #[test]
    fn bitor_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);

        let c: Z = &a | &b;

        assert_eq!(Z::from(58), c);
    }

    /// Testing `bitor` for borrowed [`Z`] and [`Z`]
    #[test]
    fn bitor_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);

        let c: Z = &a | b;

        assert_eq!(Z::from(58), c);
    }

    /// Testing `bitor` for [`Z`] and borrowed [`Z`]
    #[test]
    fn bitor_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);

        let c: Z = a | &b;

        assert_eq!(Z::from(58), c);
    }

    /// Testing `bitor` for large numbers
    #[test]
    fn bitor_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Z = Z::from(221319874);
        let c: Z = Z::from(i64::MAX);

        let d: Z = &c | b;
        let e: Z = a | c;

        assert_eq!(Z::from(i64::MAX), d);
        assert_eq!(Z::from(u64::MAX), e);
    }

    /// Testing `bitor` between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn availability() {
        let a: Z = Z::from(42);
        let b: u64 = 1;
        let c: u32 = 1;
        let d: u16 = 1;
        let e: u8 = 1;
        let f: i64 = 1;
        let g: i32 = 1;
        let h: i16 = 1;
        let i: i8 = 1;

        let _: Z = &a | &b;
        let _: Z = &a | &c;
        let _: Z = &a | &d;
        let _: Z = &a | &e;
        let _: Z = &a | &f;
        let _: Z = &a | &g;
        let _: Z = &a | &h;
        let _: Z = &a | &i;

        let _: Z = &b | &a;
        let _: Z = &c | &a;
        let _: Z = &d | &a;
        let _: Z = &e | &a;
        let _: Z = &f | &a;
        let _: Z = &g | &a;
        let _: Z = &h | &a;
        let _: Z = &i | &a;

        let _: Z = &a | b;
        let _: Z = &a | c;
        let _: Z = &a | d;
        let _: Z = &a | e;
        let _: Z = &a | f;
        let _: Z = &a | g;
        let _: Z = &a | h;
        let _: Z = &a | i;

        let _: Z = &b | Z::from(42);
        let _: Z = &c | Z::from(42);
        let _: Z = &d | Z::from(42);
        let _: Z = &e | Z::from(42);
        let _: Z = &f | Z::from(42);
        let _: Z = &g | Z::from(42);
        let _: Z = &h | Z::from(42);
        let _: Z = &i | Z::from(42);

        let _: Z = Z::from(42) | &b;
        let _: Z = Z::from(42) | &c;
        let _: Z = Z::from(42) | &d;
        let _: Z = Z::from(42) | &e;
        let _: Z = Z::from(42) | &f;
        let _: Z = Z::from(42) | &g;
        let _: Z = Z::from(42) | &h;
        let _: Z = Z::from(42) | &i;

        let _: Z = b | &a;
        let _: Z = c | &a;
        let _: Z = d | &a;
        let _: Z = e | &a;
        let _: Z = f | &a;
        let _: Z = g | &a;
        let _: Z = h | &a;
        let _: Z = i | &a;

        let _: Z = Z::from(42) | b;
        let _: Z = Z::from(42) | c;
        let _: Z = Z::from(42) | d;
        let _: Z = Z::from(42) | e;
        let _: Z = Z::from(42) | f;
        let _: Z = Z::from(42) | g;
        let _: Z = Z::from(42) | h;
        let _: Z = Z::from(42) | i;

        let _: Z = b | Z::from(42);
        let _: Z = c | Z::from(42);
        let _: Z = d | Z::from(42);
        let _: Z = e | Z::from(42);
        let _: Z = f | Z::from(42);
        let _: Z = g | Z::from(42);
        let _: Z = h | Z::from(42);
        let _: Z = i | Z::from(42);
    }
}
