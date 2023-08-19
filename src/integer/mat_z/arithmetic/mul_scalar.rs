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
    /// Implements multiplication for a [`MatZ`] matrix with a [`Z`] integer.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `other` as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mat1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat2 = &mat1 * &integer;
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
        let mat1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatZ::from_str("[[6, 3],[3, 6]]").unwrap();
        let integer = Z::from(3);

        let mat1 = &mat1 * &integer;
        let mat2 = &integer * &mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatZ::from_str("[[6, 3],[3, 6]]").unwrap();
        let integer1 = Z::from(3);
        let integer2 = Z::from(3);

        let mat1 = mat1 * integer1;
        let mat2 = integer2 * mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = mat1.clone();
        let mat4 = mat1.clone();
        let mat5 = MatZ::from_str("[[6, 3],[3, 6]]").unwrap();
        let integer1 = Z::from(3);
        let integer2 = Z::from(3);

        let mat1 = mat1 * &integer1;
        let mat2 = &integer2 * mat2;
        let mat3 = &mat3 * integer1;
        let mat4 = integer2 * &mat4;

        assert_eq!(mat5, mat1);
        assert_eq!(mat5, mat2);
        assert_eq!(mat5, mat3);
        assert_eq!(mat5, mat4);
    }

    /// Checks if scalar multiplication works fine for different scalar types
    #[test]
    #[allow(clippy::erasing_op)]
    fn different_types() {
        let mat1 = MatZ::from_str("[[1],[0],[4]]").unwrap();
        let mat2 = MatZ::from_str("[[2, 5, 6],[1, 3, 1]]").unwrap();
        let mat3 = MatZ::from_str("[[2],[0],[8]]").unwrap();
        let mat4 = MatZ::from_str("[[0],[0],[0]]").unwrap();
        let mat5 = MatZ::from_str("[[-1],[0],[-4]]").unwrap();
        let mat6 = MatZ::from_str("[[6, 15, 18],[3, 9, 3]]").unwrap();

        assert_eq!(mat3, 2 * &mat1);
        assert_eq!(mat4, 0 * &mat1);
        assert_eq!(mat5, -1 * mat1);
        assert_eq!(mat6, mat2 * 3);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatZ::from_str("[[1],[0],[4]]").unwrap();
        let mat2 = MatZ::from_str("[[2, 5, 6],[1, 3, 1]]").unwrap();
        let mat3 = MatZ::from_str("[[3],[0],[12]]").unwrap();
        let mat4 = MatZ::from_str("[[6, 15, 18],[3, 9, 3]]").unwrap();
        let integer = Z::from(3);

        assert_eq!(mat3, &integer * mat1);
        assert_eq!(mat4, integer * mat2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat1 = MatZ::from_str(&format!("[[1],[{}],[4]]", i64::MAX)).unwrap();
        let mat2 = MatZ::from_str("[[3]]").unwrap();
        let mat3 = MatZ::from_str(&format!("[[3],[{}],[12]]", 3 * i64::MAX as i128)).unwrap();
        let mat4 = MatZ::from_str(&format!("[[{}]]", 3 * i64::MAX as i128)).unwrap();
        let integer1 = Z::from(3);
        let integer2 = Z::from(i64::MAX);

        assert_eq!(mat3, integer1 * mat1);
        assert_eq!(mat4, integer2 * mat2);
    }
}
