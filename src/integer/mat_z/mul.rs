// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`MatZ`] values.

use super::MatZ;
use crate::{
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
    traits::{GetNumColumns, GetNumRows},
};
use flint_sys::fmpz_mat::fmpz_mat_mul;
use std::ops::Mul;

impl Mul for &MatZ {
    type Output = MatZ;

    /// Implements the [`Mul`] trait for two [`MatZ`] values.
    /// [`Mul`] is implemented for any combination of owned and borrowed [`MatZ`] and any kind of [`VecZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatZ`].
    ///
    /// # Example
    /// ```
    /// use math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::from_str("[[2,1],[1,2]]").unwrap();
    /// let b = MatZ::from_str("[[1,0],[0,1]]").unwrap();
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
        // TODO: mul_safe
        if self.get_num_columns() != other.get_num_rows() {
            panic!("Matrix dimensions do not match for matrix multiplication!");
        }

        let mut new = MatZ::new(self.get_num_rows(), other.get_num_columns()).unwrap();
        unsafe { fmpz_mat_mul(&mut new.matrix, &self.matrix, &other.matrix) };
        new
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZ);

#[cfg(test)]
mod test_mul {

    use super::MatZ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for sqaured matrices
    #[test]
    fn square_correctness() {
        let mat_1 = MatZ::from_str("[[2,1],[1,2]]").unwrap();
        let mat_2 = MatZ::from_str("[[1,0],[0,1]]").unwrap();
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
        let mut cmp = MatZ::new(2, 1).unwrap();
        let max: Z = i64::MAX.into();
        cmp.set_entry_ref_z(0, 0, &(&max * &max)).unwrap();

        assert_eq!(cmp, mat * vec);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// results in panic
    #[test]
    #[should_panic]
    fn incompatible_dimensions() {
        let mat_1 = MatZ::from_str("[[2,1],[1,2]]").unwrap();
        let mat_2 = MatZ::from_str("[[1,0],[0,1],[0,0]]").unwrap();

        let _ = mat_1 * mat_2;
    }
}
