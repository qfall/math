// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`MatPolyOverZ`] values.

use super::super::MatPolyOverZ;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_sub;
use std::ops::Sub;

impl Sub for &MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Implements the [`Sub`] trait for two [`MatPolyOverZ`] values.
    /// [`Sub`] is implemented for any combination of [`MatPolyOverZ`] and borrowed [`MatPolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract to `self`
    ///
    /// Returns the result of the subtraction as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
    /// let b: MatPolyOverZ = MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
    ///
    /// let c: MatPolyOverZ = &a - &b;
    /// let d: MatPolyOverZ = a - b;
    /// let e: MatPolyOverZ = &c - d;
    /// let f: MatPolyOverZ = c - &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
    }
}

impl MatPolyOverZ {
    /// Implements subtraction for two [`MatPolyOverZ`] matrices.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract to `self`
    ///
    /// Returns the result of the subtraction as a [`MatPolyOverZ`] or an
    /// error if the matrix dimensions mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
    /// let b: MatPolyOverZ = MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
    ///
    /// let c: MatPolyOverZ = a.sub_safe(&b).unwrap();

    /// ```
    /// # Errors
    /// Returns a [`MathError`] of type
    /// [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    /// mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<MatPolyOverZ, MathError> {
        if self.get_num_rows() != other.get_num_rows()
            || self.get_num_columns() != other.get_num_columns()
        {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to subtract a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            )));
        }
        let mut out = MatPolyOverZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpz_poly_mat_sub(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, MatPolyOverZ, MatPolyOverZ, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, MatPolyOverZ, MatPolyOverZ, MatPolyOverZ);

#[cfg(test)]
mod test_sub {
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Testing subtraction for two [`MatPolyOverZ`]
    #[test]
    fn sub() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
        let c: MatPolyOverZ = a - b;
        assert_eq!(
            c,
            MatPolyOverZ::from_str("[[1  42, 1  42, 2  18 -18],[3  16 12 38, 1  18, 1  25]]")
                .unwrap()
        );
    }

    /// Testing subtraction for two borrowed [`MatPolyOverZ`]
    #[test]
    fn sub_borrow() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
        let c: MatPolyOverZ = &a - &b;
        assert_eq!(
            c,
            MatPolyOverZ::from_str("[[1  42, 1  42, 2  18 -18],[3  16 12 38, 1  18, 1  25]]")
                .unwrap()
        );
    }

    /// Testing subtraction for borrowed [`MatPolyOverZ`] and [`MatPolyOverZ`]
    #[test]
    fn sub_first_borrowed() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
        let c: MatPolyOverZ = &a - b;
        assert_eq!(
            c,
            MatPolyOverZ::from_str("[[1  42, 1  42, 2  18 -18],[3  16 12 38, 1  18, 1  25]]")
                .unwrap()
        );
    }

    /// Testing subtraction for [`MatPolyOverZ`] and borrowed [`MatPolyOverZ`]
    #[test]
    fn sub_second_borrowed() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
        let c: MatPolyOverZ = a - &b;
        assert_eq!(
            c,
            MatPolyOverZ::from_str("[[1  42, 1  42, 2  18 -18],[3  16 12 38, 1  18, 1  25]]")
                .unwrap()
        );
    }

    /// Testing subtraction for big numbers
    #[test]
    fn sub_large_numbers() {
        let a: MatPolyOverZ = MatPolyOverZ::from_str(&format!(
            "[[1  {},2  1 {}],[2  -{} 7, 0]]",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str(&format!(
            "[[1  {},2  1 {}],[2  {} 7, 0]]",
            i64::MAX,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let c: MatPolyOverZ = a - &b;
        assert_eq!(
            c,
            MatPolyOverZ::from_str(&format!("[[0,2  0 -{}],[1  -{}, 0]]", u64::MAX, i64::MAX))
                .unwrap()
        );
    }

    /// Testing sub_safe
    #[test]
    fn sub_safe() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
        let c: MatPolyOverZ = a.sub_safe(&b).unwrap();
        assert_eq!(
            c,
            MatPolyOverZ::from_str("[[1  42, 1  42, 2  18 -18],[3  16 12 38, 1  18, 1  25]]")
                .unwrap()
        );
    }

    /// Testing sub_safe throws error
    #[test]
    fn sub_safe_is_err() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str("[[1  -42, 0],[3  1 12 4, 1  17]]").unwrap();
        let c: MatPolyOverZ = MatPolyOverZ::from_str("[[0, 1  42, 2  42 24]]").unwrap();
        assert!(a.sub_safe(&b).is_err());
        assert!(c.sub_safe(&b).is_err());
    }
}
