// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`MatZ`] matrices.

use super::super::MatZ;
use crate::integer::Z;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_mat::fmpz_mat_scalar_mul_fmpz;
use std::ops::Mul;

impl Mul<&Z> for &MatZ {
    type Output = MatZ;
    /// Implements the [`Mul`] trait for a [`MatZ`] matrix with a [`Z`] integer.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat_2 = &mat_1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpz_mat_scalar_mul_fmpz(&mut out.matrix, &self.matrix, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Z, MatZ, MatZ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZ, Z, MatZ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, MatZ, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZ, Z, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, MatZ, MatZ);

implement_for_others!(Z, MatZ, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

#[cfg(test)]
mod test_mul {
    use super::MatZ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatZ::from_str("[[6, 3],[3, 6]]").unwrap();
        let integer = Z::from(3);

        let mat_1 = &mat_1 * &integer;
        let mat_2 = &integer * &mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatZ::from_str("[[6, 3],[3, 6]]").unwrap();
        let integer_1 = Z::from(3);
        let integer_2 = Z::from(3);

        let mat_1 = mat_1 * integer_1;
        let mat_2 = integer_2 * mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = mat_1.clone();
        let mat_4 = mat_1.clone();
        let mat_5 = MatZ::from_str("[[6, 3],[3, 6]]").unwrap();
        let integer_1 = Z::from(3);
        let integer_2 = Z::from(3);

        let mat_1 = mat_1 * &integer_1;
        let mat_2 = &integer_2 * mat_2;
        let mat_3 = &mat_3 * integer_1;
        let mat_4 = integer_2 * &mat_4;

        assert_eq!(mat_5, mat_1);
        assert_eq!(mat_5, mat_2);
        assert_eq!(mat_5, mat_3);
        assert_eq!(mat_5, mat_4);
    }

    /// Checks if scalar multiplication works fine for different scalar types
    #[test]
    #[allow(clippy::erasing_op)]
    fn different_types() {
        let mat_1 = MatZ::from_str("[[1],[0],[4]]").unwrap();
        let mat_2 = MatZ::from_str("[[2, 5, 6],[1, 3, 1]]").unwrap();
        let mat_3 = MatZ::from_str("[[2],[0],[8]]").unwrap();
        let mat_4 = MatZ::from_str("[[0],[0],[0]]").unwrap();
        let mat_5 = MatZ::from_str("[[-1],[0],[-4]]").unwrap();
        let mat_6 = MatZ::from_str("[[6, 15, 18],[3, 9, 3]]").unwrap();

        assert_eq!(mat_3, 2 * &mat_1);
        assert_eq!(mat_4, 0 * &mat_1);
        assert_eq!(mat_5, -1 * mat_1);
        assert_eq!(mat_6, mat_2 * 3);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat_1 = MatZ::from_str("[[1],[0],[4]]").unwrap();
        let mat_2 = MatZ::from_str("[[2, 5, 6],[1, 3, 1]]").unwrap();
        let mat_3 = MatZ::from_str("[[3],[0],[12]]").unwrap();
        let mat_4 = MatZ::from_str("[[6, 15, 18],[3, 9, 3]]").unwrap();
        let integer = Z::from(3);

        assert_eq!(mat_3, &integer * mat_1);
        assert_eq!(mat_4, integer * mat_2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat_1 = MatZ::from_str(&format!("[[1],[{}],[4]]", i64::MAX)).unwrap();
        let mat_2 = MatZ::from_str("[[3]]").unwrap();
        let mat_3 = MatZ::from_str(&format!("[[3],[{}],[12]]", 3 * i64::MAX as i128)).unwrap();
        let mat_4 = MatZ::from_str(&format!("[[{}]]", 3 * i64::MAX as i128)).unwrap();
        let integer_1 = Z::from(3);
        let integer_2 = Z::from(i64::MAX);

        assert_eq!(mat_3, integer_1 * mat_1);
        assert_eq!(mat_4, integer_2 * mat_2);
    }
}
