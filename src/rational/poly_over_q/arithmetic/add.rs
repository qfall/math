// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`PolyOverQ`] values.

use super::super::PolyOverQ;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpq_poly::fmpq_poly_add;
use std::ops::Add;

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
    /// # Example
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
mod test_add {

    use super::PolyOverQ;
    use crate::rational::Q;
    use std::str::FromStr;

    /// testing addition for two [`PolyOverQ`]
    #[test]
    fn add() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/9 5/2 1 2/7").unwrap();
        let c: PolyOverQ = a + b;
        assert_eq!(c, PolyOverQ::from_str("5  16/63 20/9 -1/2 1 2/7").unwrap());
    }

    /// testing addition for two borrowed [`PolyOverQ`]
    #[test]
    fn add_borrow() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/9 5/2 1 2/7").unwrap();
        let c: PolyOverQ = a + b;
        assert_eq!(c, PolyOverQ::from_str("5  16/63 20/9 -1/2 1 2/7").unwrap());
    }

    /// testing addition for borrowed [`PolyOverQ`] and [`PolyOverQ`]
    #[test]
    fn add_first_borrowed() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/9 5/2 1 2/7").unwrap();
        let c: PolyOverQ = &a + &b;
        assert_eq!(c, PolyOverQ::from_str("5  16/63 20/9 -1/2 1 2/7").unwrap());
    }

    /// testing addition for [`PolyOverQ`] and borrowed [`PolyOverQ`]
    #[test]
    fn add_second_borrowed() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/9 5/2 1 2/7").unwrap();
        let c: PolyOverQ = &a + b;
        assert_eq!(c, PolyOverQ::from_str("5  16/63 20/9 -1/2 1 2/7").unwrap());
    }

    /// testing addition with eliminating coefficients
    #[test]
    fn add_eliminating_coefficients() {
        let a: PolyOverQ = PolyOverQ::from_str("3  1/7 2 -3").unwrap();
        let b: PolyOverQ = PolyOverQ::from_str("5  1/9 2/9 5/2 1 2/7").unwrap();
        let c: PolyOverQ = a + &b;
        assert_eq!(c, PolyOverQ::from_str("5  16/63 20/9 -1/2 1 2/7").unwrap());
    }

    /// testing addition for large [`PolyOverQ`]
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
                (Q::from_str(&format!("{}/{}", i64::MIN, u128::MAX)).unwrap()
                    + Q::from_str(&format!("{}", i64::MAX)).unwrap()),
                i64::MAX
            ))
            .unwrap()
        );
    }
}
