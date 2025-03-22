// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`PolyOverQ`] values.

use super::super::PolyOverQ;
use crate::{
    integer::PolyOverZ,
    macros::arithmetics::{
        arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpq_poly::fmpq_poly_add;
use std::ops::{Add, AddAssign};

impl AddAssign<&PolyOverQ> for PolyOverQ {
    /// Computes the addition of `self` and `other` reusing
    /// the memory of `self`.
    /// [`AddAssign`] can be used on [`PolyOverQ`] in combination with
    /// [`PolyOverQ`] and [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to add to `self`
    ///
    /// Returns the sum of both polynomials as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{rational::PolyOverQ, integer::PolyOverZ};
    /// use std::str::FromStr;
    ///
    /// let mut a = PolyOverQ::from_str("3  1 2/3 -3/4").unwrap();
    /// let b = PolyOverQ::from_str("5  1 2 -3 0 8/9").unwrap();
    /// let c = PolyOverZ::from_str("2  -1 2").unwrap();
    ///
    /// a += &b;
    /// a += b;
    /// a += &c;
    /// a += c;
    /// ```
    fn add_assign(&mut self, other: &Self) {
        unsafe { fmpq_poly_add(&mut self.poly, &self.poly, &other.poly) };
    }
}
impl AddAssign<&PolyOverZ> for PolyOverQ {
    /// Documentation at [`PolyOverQ::add_assign`].
    fn add_assign(&mut self, other: &PolyOverZ) {
        let other = PolyOverQ::from(other);

        self.add_assign(other);
    }
}

arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, PolyOverQ, PolyOverQ);
arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, PolyOverQ, PolyOverZ);

impl Add for &PolyOverQ {
    type Output = PolyOverQ;
    /// Implements the [`Add`] trait for two [`PolyOverQ`] values.
    /// [`Add`] is implemented for any combination of [`PolyOverQ`] and borrowed [`PolyOverQ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both polynomials as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverQ = PolyOverQ::from_str("3  1/8 2/7 -7").unwrap();
    /// let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/9 -3/8 0 8/9").unwrap();
    ///
    /// let c: PolyOverQ = &a + &b;
    /// let d: PolyOverQ = a + b;
    /// let e: PolyOverQ = &c + d;
    /// let f: PolyOverQ = c + &e;
    /// ```
    fn add(self, other: Self) -> Self::Output {
        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_add(&mut out.poly, &self.poly, &other.poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, PolyOverQ, PolyOverQ, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, PolyOverQ, PolyOverQ, PolyOverQ);

#[cfg(test)]
mod test_add_assign {
    use super::PolyOverQ;
    use crate::{integer::PolyOverZ, rational::Q};
    use std::str::FromStr;

    /// Ensure that `add_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = PolyOverQ::from_str("3  1/7 2/7 -3").unwrap();
        let b = PolyOverQ::from_str("3  1 -2/7 3").unwrap();
        let cmp = PolyOverQ::from_str("1  8/7").unwrap();

        a += &b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `add_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a: PolyOverQ = PolyOverQ::from_str(&format!(
            "3  {} {}/{} {}",
            u64::MAX,
            i64::MIN,
            u128::MAX,
            i64::MAX
        ))
        .unwrap();
        let b = PolyOverQ::from_str(&format!("2  {} {}", u64::MAX, i64::MAX)).unwrap();
        let cmp = PolyOverQ::from_str(&format!(
            "3  {} {} {}",
            u128::from(u64::MAX) * 2,
            (Q::from_str(&format!("{}/{}", i64::MIN, u128::MAX)).unwrap() + Q::from(i64::MAX)),
            i64::MAX
        ))
        .unwrap();

        a += b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `add_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = PolyOverQ::from_str("3  1 2 -3").unwrap();
        let b = PolyOverQ::from_str("3  -1 -2 3").unwrap();
        let c = PolyOverZ::from_str("4  2 -1 2 3").unwrap();

        a += &b;
        a += b;
        a += &c;
        a += c;
    }
}

#[cfg(test)]
mod test_add {
    use super::PolyOverQ;
    use crate::rational::Q;
    use std::str::FromStr;

    /// Testing addition for two [`PolyOverQ`]
    #[test]
    fn add() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/9 5/2 1 2/7").unwrap();
        let c: PolyOverQ = a + b;
        assert_eq!(c, PolyOverQ::from_str("5  16/63 20/9 -1/2 1 2/7").unwrap());
    }

    /// Testing addition for two borrowed [`PolyOverQ`]
    #[test]
    fn add_borrow() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/9 5/2 1 2/7").unwrap();
        let c: PolyOverQ = a + b;
        assert_eq!(c, PolyOverQ::from_str("5  16/63 20/9 -1/2 1 2/7").unwrap());
    }

    /// Testing addition for borrowed [`PolyOverQ`] and [`PolyOverQ`]
    #[test]
    fn add_first_borrowed() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/9 5/2 1 2/7").unwrap();
        let c: PolyOverQ = &a + &b;
        assert_eq!(c, PolyOverQ::from_str("5  16/63 20/9 -1/2 1 2/7").unwrap());
    }

    /// Testing addition for [`PolyOverQ`] and borrowed [`PolyOverQ`]
    #[test]
    fn add_second_borrowed() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/9 5/2 1 2/7").unwrap();
        let c: PolyOverQ = &a + b;
        assert_eq!(c, PolyOverQ::from_str("5  16/63 20/9 -1/2 1 2/7").unwrap());
    }

    /// Testing addition with eliminating coefficients
    #[test]
    fn add_eliminating_coefficients() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2/7 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("3  1 -2/7 3").unwrap();
        let c: PolyOverQ = a + &b;
        assert_eq!(c, PolyOverQ::from_str("1  8/7").unwrap());
    }

    /// Testing addition for large [`PolyOverQ`]
    #[test]
    fn add_large_numbers() {
        let a: PolyOverQ = PolyOverQ::from_str(&format!(
            "3  {} {}/{} {}",
            u64::MAX,
            i64::MIN,
            u128::MAX,
            i64::MAX
        ))
        .unwrap();
        let b: PolyOverQ = PolyOverQ::from_str(&format!("2  {} {}", u64::MAX, i64::MAX)).unwrap();
        let c: PolyOverQ = a + b;
        assert_eq!(
            c,
            PolyOverQ::from_str(&format!(
                "3  {} {} {}",
                u128::from(u64::MAX) * 2,
                (Q::from_str(&format!("{}/{}", i64::MIN, u128::MAX)).unwrap() + Q::from(i64::MAX)),
                i64::MAX
            ))
            .unwrap()
        );
    }
}
