// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`MatPolyOverZ`] values.

use super::super::MatPolyOverZ;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_mul;
use std::ops::Mul;

impl Mul for &MatPolyOverZ {
    type Output = MatPolyOverZ;

    /// Implements the [`Mul`] trait for two [`MatPolyOverZ`] values.
    ///
    /// [`Mul`] is implemented for any combination of owned and borrowed [`MatPolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
    /// let b: MatPolyOverZ = MatPolyOverZ::from_str("[[1  -42, 2  24 42],[1  -1, 1  17],[0, 2  1 42]]").unwrap();

    ///
    /// let c = &a * &b;
    /// let d = a * b;
    /// let e = &c * d;
    /// let f = c * &e;
    /// ```
    ///
    /// # Errors and Failures
    /// - Panics if the dimensions of `self` and `other` do not match for multiplication.
    fn mul(self, other: Self) -> Self::Output {
        self.mul_safe(other).unwrap()
    }
}

impl MatPolyOverZ {
    /// Implements multiplication for two [`MatPolyOverZ`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[0, 2  42 24],[3  17 24 42, 1  17]]").unwrap();
    /// let b: MatPolyOverZ = MatPolyOverZ::from_str("[[1  -42, 2  24 42],[3  1 12 4, 1  17]]").unwrap();
    ///
    /// let c: MatPolyOverZ = a.mul_safe(&b).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`MathError::MismatchingMatrixDimension`] if the dimensions of `self`
    ///  and `other` do not match for multiplication.
    pub fn mul_safe(&self, other: &Self) -> Result<Self, MathError> {
        if self.get_num_columns() != other.get_num_rows() {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to multiply a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            )));
        }

        let mut new = MatPolyOverZ::new(self.get_num_rows(), other.get_num_columns()).unwrap();
        unsafe { fmpz_poly_mat_mul(&mut new.matrix, &self.matrix, &other.matrix) };
        Ok(new)
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatPolyOverZ, MatPolyOverZ, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatPolyOverZ, MatPolyOverZ, MatPolyOverZ);

#[cfg(test)]
mod test_mul {
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for squared matrices
    #[test]
    fn square_correctness() {
        let mat_1 = MatPolyOverZ::from_str("[[2  0 1, 1  4],[0, 3  1 2 3]]").unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[2  0 1, 1  4],[0, 3  1 2 3]]").unwrap();
        let res = MatPolyOverZ::from_str("[[3  0 0 1,3  4 12 12],[0,5  1 4 10 12 9]]").unwrap();
        assert_eq!(res, &mat_1 * &mat_2);
    }

    /// Checks if matrix multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat = MatPolyOverZ::from_str("[[2  1 4,1  7],[1  3,3  12 3 4]]").unwrap();
        let vec = MatPolyOverZ::from_str("[[1  4],[0]]").unwrap();
        let cmp = MatPolyOverZ::from_str("[[2  4 16],[1  12]]").unwrap();

        assert_eq!(cmp, &mat * &vec);
    }

    /// Checks if matrix multiplication works fine for large entries
    #[test]
    fn large_entries() {
        let mat = MatPolyOverZ::from_str(&format!("[[2  3 {},1  15],[1  1,0]]", u64::MAX)).unwrap();
        let vec = MatPolyOverZ::from_str(&format!("[[2  1 {}],[0]]", u64::MAX)).unwrap();
        let cmp = MatPolyOverZ::from_str(&format!(
            "[[3  3 {} {}],[2  1 {}]]",
            u128::from(u64::MAX) * 4,
            u128::from(u64::MAX) * u128::from(u64::MAX),
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp, mat * vec);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// throws an error as expected
    #[test]
    fn incompatible_dimensions() {
        let a: MatPolyOverZ = MatPolyOverZ::from_str("[[2  0 1, 1  4],[0, 3  1 2 3]]").unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str("[[2  0 1, 1  4]]").unwrap();
        let c: MatPolyOverZ =
            MatPolyOverZ::from_str("[[2  0 1, 1  4, 0],[0, 3  1 2 3, 1  3]]").unwrap();
        assert!(a.mul_safe(&b).is_err());
        assert!(c.mul_safe(&b).is_err());
    }
}
