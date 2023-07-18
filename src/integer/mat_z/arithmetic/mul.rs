// Copyright © 2023 Niklas Siemer, Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`MatZ`] values.

use super::super::MatZ;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_mat::fmpz_mat_mul;
use std::ops::Mul;

impl Mul for &MatZ {
    type Output = MatZ;

    /// Implements the [`Mul`] trait for two [`MatZ`] values.
    ///
    /// [`Mul`] is implemented for any combination of owned and borrowed [`MatZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::from_str("[[2,1],[1,2]]").unwrap();
    /// let b = MatZ::identity(2, 2);
    ///
    /// let c = &a * &b;
    /// let d = a * b;
    /// let e = &c * d;
    /// let f = c * &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    fn mul(self, other: Self) -> Self::Output {
        self.mul_safe(other).unwrap()
    }
}

impl MatZ {
    /// Implements multiplication for two [`MatZ`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::from_str("[[2,1],[1,2]]").unwrap();
    /// let b = MatZ::identity(2, 2);
    ///
    /// let c: MatZ = a.mul_safe(&b).unwrap();
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

        let mut new = MatZ::new(self.get_num_rows(), other.get_num_columns());
        unsafe { fmpz_mat_mul(&mut new.matrix, &self.matrix, &other.matrix) };
        Ok(new)
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZ, MatZ, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZ, MatZ, MatZ);

#[cfg(test)]
mod test_mul {
    use super::MatZ;
    use crate::{integer::Z, traits::SetEntry};
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for squared matrices
    #[test]
    fn square_correctness() {
        let mat_1 = MatZ::from_str("[[2,1],[1,2]]").unwrap();
        let mat_2 = MatZ::identity(2, 2);
        let mat_3 = MatZ::from_str("[[1,2],[2,1]]").unwrap();
        let cmp = MatZ::from_str("[[4,5],[5,4]]").unwrap();

        assert_eq!(mat_1, &mat_1 * &mat_2);
        assert_eq!(cmp, &mat_1 * &mat_3);
    }

    /// Checks if matrix multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat = MatZ::from_str("[[2,1],[1,2]]").unwrap();
        let vec = MatZ::from_str("[[1],[0]]").unwrap();
        let cmp = MatZ::from_str("[[2],[1]]").unwrap();

        assert_eq!(cmp, &mat * &vec);
    }

    /// Checks if matrix multiplication works fine for large entries
    #[test]
    fn large_entries() {
        let mat = MatZ::from_str(&format!("[[{},1],[0,2]]", i64::MAX)).unwrap();
        let vec = MatZ::from_str(&format!("[[{}],[0]]", i64::MAX)).unwrap();
        let mut cmp = MatZ::new(2, 1);
        let max: Z = i64::MAX.into();
        cmp.set_entry(0, 0, &(&max * &max)).unwrap();

        assert_eq!(cmp, mat * vec);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// throws an error as expected
    #[test]
    fn incompatible_dimensions() {
        let mat_1 = MatZ::from_str("[[2,1],[1,2]]").unwrap();
        let mat_2 = MatZ::from_str("[[1,0],[0,1],[0,0]]").unwrap();

        assert!((mat_1.mul_safe(&mat_2)).is_err());
    }
}
