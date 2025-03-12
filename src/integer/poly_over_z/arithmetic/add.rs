// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`PolyOverZ`] values.

use super::super::PolyOverZ;
use crate::integer::Z;
use crate::macros::arithmetics::{
    arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
    arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::{fmpz::fmpz_add, fmpz_poly::fmpz_poly_add};
use std::ops::{Add, AddAssign};

impl AddAssign<&PolyOverZ> for PolyOverZ {
    /// Computes the addition of `self` and `other` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mut a = PolyOverZ::from_str("3  1 2 -3").unwrap();
    /// let b = PolyOverZ::from_str("5  1 2 -3 0 8").unwrap();
    ///
    /// a += &b;
    /// a += b;
    /// ```
    fn add_assign(&mut self, other: &Self) {
        unsafe { fmpz_poly_add(&mut self.poly, &self.poly, &other.poly) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, PolyOverZ, PolyOverZ);

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
    /// # Examples
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

impl Add<&Z> for &PolyOverZ {
    type Output = PolyOverZ;
    /// Implements the [`Add`] trait for [`PolyOverZ`] and [`Z`] values.
    /// [`Add`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the [`Z`] to add to `self`
    ///
    /// Returns the sum of both as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let b: PolyOverZ = PolyOverZ::from_str("4  5 1 2 3").unwrap();
    /// let a: Z = Z::from(42);
    ///
    /// let c: PolyOverZ = &a + &b;
    /// let d: PolyOverZ = a + b;
    /// let e: PolyOverZ = d + &Z::from(42);
    /// let f: PolyOverZ = &e + Z::from(42);
    /// ```
    fn add(self, other: &Z) -> Self::Output {
        // check if the first coefficient of the polynomial is initiated and
        // can be addressed
        if self.is_zero() {
            PolyOverZ::from(other)
        } else {
            let out = self.clone();
            unsafe {
                fmpz_add(out.poly.coeffs, &other.value, out.poly.coeffs);
            }
            out
        }
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, PolyOverZ, Z, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, PolyOverZ, Z, PolyOverZ);

#[cfg(test)]
mod test_add_assign {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that `add_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = PolyOverZ::from_str("3  -1 2 -3").unwrap();
        let b = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let cmp = PolyOverZ::from_str("5  0 4 2 1 2").unwrap();

        a += b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `add_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a =
            PolyOverZ::from_str(&format!("3  {} {} {}", u32::MAX, i32::MIN, i32::MAX)).unwrap();
        let b = PolyOverZ::from_str(&format!("2  {} {}", u32::MAX, i32::MAX)).unwrap();
        let cmp = PolyOverZ::from_str(&format!("3  {} -1 {}", u64::from(u32::MAX) * 2, i32::MAX))
            .unwrap();

        a += b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `add_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b = PolyOverZ::from_str("3  -1 -2 3").unwrap();

        a += &b;
        a += b;
    }
}

#[cfg(test)]
mod test_add {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Testing addition for two [`PolyOverZ`]
    #[test]
    fn add() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a + b;
        assert_eq!(c, PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// Testing addition for two borrowed [`PolyOverZ`]
    #[test]
    fn add_borrow() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a + &b;
        assert_eq!(c, PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// Testing addition for borrowed [`PolyOverZ`] and [`PolyOverZ`]
    #[test]
    fn add_first_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a + b;
        assert_eq!(c, PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// Testing addition for [`PolyOverZ`] and borrowed P[`PolyOverZ`]
    #[test]
    fn add_second_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a + &b;
        assert_eq!(c, PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// Testing addition with eliminating coefficients
    #[test]
    fn add_eliminating_coefficients() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("3  -1 -2 3").unwrap();
        let c: PolyOverZ = a + b;
        assert_eq!(c, PolyOverZ::default());
    }

    /// Testing addition for large [`PolyOverZ`]
    #[test]
    fn add_large_numbers() {
        let a: PolyOverZ =
            PolyOverZ::from_str(&format!("3  {} {} {}", u32::MAX, i32::MIN, i32::MAX)).unwrap();
        let b: PolyOverZ = PolyOverZ::from_str(&format!("2  {} {}", u32::MAX, i32::MAX)).unwrap();
        let c: PolyOverZ = a + b;
        assert_eq!(
            c,
            PolyOverZ::from_str(&format!("3  {} -1 {}", u64::from(u32::MAX) * 2, i32::MAX))
                .unwrap()
        );
    }
}

#[cfg(test)]
mod test_add_between_z_and_poly_over_z {
    use crate::integer::PolyOverZ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Testing addition for [`Z`] and [`PolyOverZ`]
    #[test]
    fn add() {
        let a: PolyOverZ = PolyOverZ::from_str("4  1 1 2 3").unwrap();
        let b: Z = Z::from(9);
        let c: PolyOverZ = a + b;
        assert_eq!(c, PolyOverZ::from_str("4  10 1 2 3").unwrap());
    }

    /// Testing addition for both borrowed [`Z`] and [`PolyOverZ`]
    #[test]
    fn add_borrow() {
        let a: PolyOverZ = PolyOverZ::from_str("4  1 1 2 3").unwrap();
        let b: Z = Z::from(9);
        let c: PolyOverZ = &a + &b;
        assert_eq!(c, PolyOverZ::from_str("4  10 1 2 3").unwrap());
    }

    /// Testing addition for borrowed [`Z`] and [`PolyOverZ`]
    #[test]
    fn add_first_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("4  1 1 2 3").unwrap();
        let b: Z = Z::from(9);
        let c: PolyOverZ = &a + b;
        assert_eq!(c, PolyOverZ::from_str("4  10 1 2 3").unwrap());
    }

    /// Testing addition for [`Z`] and borrowed [`PolyOverZ`]
    #[test]
    fn add_second_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("4  1 1 2 3").unwrap();
        let b: Z = Z::from(9);
        let c: PolyOverZ = a + &b;
        assert_eq!(c, PolyOverZ::from_str("4  10 1 2 3").unwrap());
    }

    /// Testing addition for large numbers
    #[test]
    fn add_large_numbers() {
        let a: PolyOverZ =
            PolyOverZ::from_str(&format!("3  {} {} {}", i64::MAX, u64::MAX, i32::MAX)).unwrap();
        let b: Z = Z::from(i64::MAX);
        let c: PolyOverZ = a + b;
        assert_eq!(
            c,
            PolyOverZ::from_str(&format!("3  {} {} {}", u64::MAX - 1, u64::MAX, i32::MAX)).unwrap()
        );
    }

    /// Testing addition for an empty polynomial and a zero [`Z`]
    #[test]
    fn add_zero() {
        let a: PolyOverZ = PolyOverZ::default();
        let b: Z = Z::from(15);
        let c: PolyOverZ = a + b;
        assert_eq!(c, PolyOverZ::from_str("1  15").unwrap());

        let d: PolyOverZ = PolyOverZ::from_str("1  15").unwrap();
        let e: Z = Z::ZERO;
        let f: PolyOverZ = d + e;
        assert_eq!(f, PolyOverZ::from_str("1  15").unwrap());
    }
}
