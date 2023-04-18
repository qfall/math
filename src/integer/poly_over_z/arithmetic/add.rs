// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`PolyOverZ`] values.

use super::super::PolyOverZ;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpz_poly::fmpz_poly_add;
use std::ops::Add;

impl Add for &PolyOverZ {
    type Output = PolyOverZ;
    /// Implements the [`Add`] trait for two [`PolyOverZ`] values.
    /// [`Add`] is implemented for any combination of [`PolyOverZ`] and borrowed [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both polynomials as a [`PolyOverZ`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
    /// let b: PolyOverZ = PolyOverZ::from_str("5  1 2 -3 0 8").unwrap();
    ///
    /// let c: PolyOverZ = &a + &b;
    /// let d: PolyOverZ = a + b;
    /// let e: PolyOverZ = &c + d;
    /// let f: PolyOverZ = c + &e;
    /// ```
    fn add(self, other: Self) -> Self::Output {
        let mut out = PolyOverZ::default();
        unsafe {
            fmpz_poly_add(&mut out.poly, &self.poly, &other.poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, PolyOverZ, PolyOverZ, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, PolyOverZ, PolyOverZ, PolyOverZ);

#[cfg(test)]
mod test_add {

    use super::PolyOverZ;
    use std::str::FromStr;

    /// testing addition for two [`PolyOverZ`]
    #[test]
    fn add() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a + b;
        assert!(c == PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// testing addition for two borrowed [`PolyOverZ`]
    #[test]
    fn add_borrow() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a + &b;
        assert!(c == PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// testing addition for borrowed [`PolyOverZ`] and [`PolyOverZ`]
    #[test]
    fn add_first_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a + b;
        assert!(c == PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// testing addition for [`PolyOverZ`] and borrowed P[`PolyOverZ`]
    #[test]
    fn add_second_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a + &b;
        assert!(c == PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// testing addition with eliminating coefficients
    #[test]
    fn add_eliminating_coefficients() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("3  -1 -2 3").unwrap();
        let c: PolyOverZ = a + b;
        assert!(c == PolyOverZ::default());
    }

    /// testing addition for large [`PolyOverZ`]
    #[test]
    fn add_large_numbers() {
        let a: PolyOverZ =
            PolyOverZ::from_str(&format!("3  {} {} {}", u32::MAX, i32::MIN, i32::MAX)).unwrap();
        let b: PolyOverZ = PolyOverZ::from_str(&format!("2  {} {}", u32::MAX, i32::MAX)).unwrap();
        let c: PolyOverZ = a + b;
        assert!(
            c == PolyOverZ::from_str(&format!("3  {} -1 {}", u64::from(u32::MAX) * 2, i32::MAX))
                .unwrap()
        );
    }
}
