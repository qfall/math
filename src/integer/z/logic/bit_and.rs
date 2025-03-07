// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations of the [`BitAnd`] trait.

use crate::{
    integer::Z,
    macros::arithmetics::{
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpz::fmpz_and;
use std::ops::BitAnd;

impl BitAnd for &Z {
    type Output = Z;

    /// Computes the bit-wise logical `and` of `self` and `other`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to apply the bit-wise logical `and` action to
    ///     apart from `self`
    ///
    /// Returns a new instance of [`Z`] containing the number resulting
    /// from the bit-wise logical `and` operation performed on `self` and `other`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let a = Z::from(5);
    /// let b = Z::from(7);
    ///
    /// let c: Z = &a & &b;
    /// let d: Z = a & 1;
    /// let e: Z = b & 15_u64;
    /// ```
    fn bitand(self, other: Self) -> Self::Output {
        let mut out = Z::default();
        unsafe { fmpz_and(&mut out.value, &self.value, &other.value) };
        out
    }
}

arithmetic_trait_borrowed_to_owned!(BitAnd, bitand, Z, Z, Z);
arithmetic_trait_mixed_borrowed_owned!(BitAnd, bitand, Z, Z, Z);
arithmetic_between_types!(BitAnd, bitand, Z, Z, i64 i32 i16 i8 u64 u32 u16 u8);

#[cfg(test)]
mod test_bitand {
    use super::Z;

    /// Testing `bitand` for two [`Z`]
    #[test]
    fn bitand() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);

        let c: Z = a & b;

        assert_eq!(Z::from(8), c);
    }

    /// Testing `bitand` for two borrowed [`Z`]
    #[test]
    fn bitand_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);

        let c: Z = &a & &b;

        assert_eq!(Z::from(8), c);
    }

    /// Testing `bitand` for borrowed [`Z`] and [`Z`]
    #[test]
    fn bitand_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);

        let c: Z = &a & b;

        assert_eq!(Z::from(8), c);
    }

    /// Testing `bitand` for [`Z`] and borrowed [`Z`]
    #[test]
    fn bitand_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);

        let c: Z = a & &b;

        assert_eq!(Z::from(8), c);
    }

    /// Testing `bitand` for large numbers
    #[test]
    fn bitand_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Z = Z::from(-221319874);
        let c: Z = Z::from(i64::MIN);
        let d_cmp = Z::from(18446744073488231742_u64);
        let e_cmp = Z::from(9223372036854775808_u64);

        let d: Z = &a & b;
        let e: Z = a & c;

        assert_eq!(d_cmp, d);
        assert_eq!(e_cmp, e);
    }

    /// Testing `bitand` between different types
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

        let _: Z = &a & &b;
        let _: Z = &a & &c;
        let _: Z = &a & &d;
        let _: Z = &a & &e;
        let _: Z = &a & &f;
        let _: Z = &a & &g;
        let _: Z = &a & &h;
        let _: Z = &a & &i;

        let _: Z = &b & &a;
        let _: Z = &c & &a;
        let _: Z = &d & &a;
        let _: Z = &e & &a;
        let _: Z = &f & &a;
        let _: Z = &g & &a;
        let _: Z = &h & &a;
        let _: Z = &i & &a;

        let _: Z = &a & b;
        let _: Z = &a & c;
        let _: Z = &a & d;
        let _: Z = &a & e;
        let _: Z = &a & f;
        let _: Z = &a & g;
        let _: Z = &a & h;
        let _: Z = &a & i;

        let _: Z = &b & Z::from(42);
        let _: Z = &c & Z::from(42);
        let _: Z = &d & Z::from(42);
        let _: Z = &e & Z::from(42);
        let _: Z = &f & Z::from(42);
        let _: Z = &g & Z::from(42);
        let _: Z = &h & Z::from(42);
        let _: Z = &i & Z::from(42);

        let _: Z = Z::from(42) & &b;
        let _: Z = Z::from(42) & &c;
        let _: Z = Z::from(42) & &d;
        let _: Z = Z::from(42) & &e;
        let _: Z = Z::from(42) & &f;
        let _: Z = Z::from(42) & &g;
        let _: Z = Z::from(42) & &h;
        let _: Z = Z::from(42) & &i;

        let _: Z = b & &a;
        let _: Z = c & &a;
        let _: Z = d & &a;
        let _: Z = e & &a;
        let _: Z = f & &a;
        let _: Z = g & &a;
        let _: Z = h & &a;
        let _: Z = i & &a;

        let _: Z = Z::from(42) & b;
        let _: Z = Z::from(42) & c;
        let _: Z = Z::from(42) & d;
        let _: Z = Z::from(42) & e;
        let _: Z = Z::from(42) & f;
        let _: Z = Z::from(42) & g;
        let _: Z = Z::from(42) & h;
        let _: Z = Z::from(42) & i;

        let _: Z = b & Z::from(42);
        let _: Z = c & Z::from(42);
        let _: Z = d & Z::from(42);
        let _: Z = e & Z::from(42);
        let _: Z = f & Z::from(42);
        let _: Z = g & Z::from(42);
        let _: Z = h & Z::from(42);
        let _: Z = i & Z::from(42);
    }
}
