// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`MatPolyOverZ`] matrices.

use super::super::MatPolyOverZ;
use crate::integer::{PolyOverZ, Z};
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_poly_mat::{fmpz_poly_mat_scalar_mul_fmpz, fmpz_poly_mat_scalar_mul_fmpz_poly};
use std::ops::Mul;

impl Mul<&Z> for &MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Implements multiplication for a [`MatPolyOverZ`] matrix with a [`Z`] integer.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `other` as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mat1 = MatPolyOverZ::from_str("[[2  1 42,1  17],[1  8,2  5 6]]").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat2 = &mat1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out = MatPolyOverZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpz_poly_mat_scalar_mul_fmpz(&mut out.matrix, &self.matrix, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Z, MatPolyOverZ, MatPolyOverZ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatPolyOverZ, Z, MatPolyOverZ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, MatPolyOverZ, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatPolyOverZ, Z, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, MatPolyOverZ, MatPolyOverZ);

implement_for_others!(Z, MatPolyOverZ, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Mul<&PolyOverZ> for &MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Implements multiplication for a [`MatPolyOverZ`] matrix with a [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `other` as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mat1 = MatPolyOverZ::from_str("[[2  1 42,1  17],[1  8,2  5 6]]").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat2 = &mat1 * &integer;
    /// ```
    fn mul(self, scalar: &PolyOverZ) -> Self::Output {
        let mut out = MatPolyOverZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpz_poly_mat_scalar_mul_fmpz_poly(&mut out.matrix, &self.matrix, &scalar.poly);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, PolyOverZ, MatPolyOverZ, MatPolyOverZ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatPolyOverZ, PolyOverZ, MatPolyOverZ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZ, MatPolyOverZ, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatPolyOverZ, PolyOverZ, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZ, MatPolyOverZ, MatPolyOverZ);

#[cfg(test)]
mod test_mul_z {
    use crate::integer::MatPolyOverZ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat1 = MatPolyOverZ::from_str("[[2  1 42,1  17],[1  8,2  1 2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatPolyOverZ::from_str("[[2  2 84,1  34],[1  16,2  2 4]]").unwrap();
        let integer = Z::from(2);

        let mat1 = &mat1 * &integer;
        let mat2 = &integer * &mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat1 = MatPolyOverZ::from_str("[[2  1 42,1  17],[1  8,2  1 2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatPolyOverZ::from_str("[[2  2 84,1  34],[1  16,2  2 4]]").unwrap();
        let integer1 = Z::from(2);
        let integer2 = Z::from(2);

        let mat1 = mat1 * integer1;
        let mat2 = integer2 * mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat1 = MatPolyOverZ::from_str("[[2  1 42,1  17],[1  8,2  1 2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = mat1.clone();
        let mat4 = mat1.clone();
        let mat5 = MatPolyOverZ::from_str("[[2  2 84,1  34],[1  16,2  2 4]]").unwrap();
        let integer1 = Z::from(2);
        let integer2 = Z::from(2);

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
        let mat1 = MatPolyOverZ::from_str("[[1  42],[0],[2  1 2]]").unwrap();
        let mat2 = MatPolyOverZ::from_str("[[1  2,1  6,1  5],[1  4,2  17 42,1  3]]").unwrap();
        let mat3 = MatPolyOverZ::from_str("[[1  84],[0],[2  2 4]]").unwrap();
        let mat4 = MatPolyOverZ::from_str("[[0],[0],[0]]").unwrap();
        let mat5 = MatPolyOverZ::from_str("[[1  -42],[0],[2  -1 -2]]").unwrap();
        let mat6 = MatPolyOverZ::from_str("[[1  4,1  12,1  10],[1  8,2  34 84,1  6]]").unwrap();

        assert_eq!(mat3, 2 * &mat1);
        assert_eq!(mat4, 0 * &mat1);
        assert_eq!(mat5, -1 * mat1);
        assert_eq!(mat6, mat2 * 2);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatPolyOverZ::from_str("[[1  42],[0],[2  1 2]]").unwrap();
        let mat2 = MatPolyOverZ::from_str("[[1  2,1  6,1  5],[1  4,2  17 42,1  3]]").unwrap();
        let mat3 = MatPolyOverZ::from_str("[[1  84],[0],[2  2 4]]").unwrap();
        let mat4 = MatPolyOverZ::from_str("[[1  4,1  12,1  10],[1  8,2  34 84,1  6]]").unwrap();
        let integer = Z::from(2);

        assert_eq!(mat3, &integer * mat1);
        assert_eq!(mat4, integer * mat2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat1 = MatPolyOverZ::from_str(&format!("[[1  1],[1  {}],[1  4]]", i64::MAX)).unwrap();
        let mat2 = MatPolyOverZ::from_str("[[1  3]]").unwrap();
        let mat3 =
            MatPolyOverZ::from_str(&format!("[[1  3],[1  {}],[1  12]]", 3 * i64::MAX as i128))
                .unwrap();
        let mat4 = MatPolyOverZ::from_str(&format!("[[1  {}]]", 3 * i64::MAX as i128)).unwrap();
        let integer1 = Z::from(3);
        let integer2 = Z::from(i64::MAX);

        assert_eq!(mat3, integer1 * mat1);
        assert_eq!(mat4, integer2 * mat2);
    }
}

#[cfg(test)]
mod test_mul_poly_over_z {
    use crate::integer::MatPolyOverZ;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat1 = MatPolyOverZ::from_str("[[2  1 42,1  17],[1  8,2  1 2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatPolyOverZ::from_str("[[2  2 84,1  34],[1  16,2  2 4]]").unwrap();
        let scalar = PolyOverZ::from_str("1  2").unwrap();

        let mat1 = &mat1 * &scalar;
        let mat2 = &scalar * &mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat1 = MatPolyOverZ::from_str("[[2  1 42,1  17],[1  8,2  1 2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatPolyOverZ::from_str("[[2  2 84,1  34],[1  16,2  2 4]]").unwrap();
        let scalar1 = PolyOverZ::from_str("1  2").unwrap();
        let scalar2 = PolyOverZ::from_str("1  2").unwrap();

        let mat1 = mat1 * scalar1;
        let mat2 = scalar2 * mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat1 = MatPolyOverZ::from_str("[[2  1 42,1  17],[1  8,2  1 2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = mat1.clone();
        let mat4 = mat1.clone();
        let mat5 = MatPolyOverZ::from_str("[[2  2 84,1  34],[1  16,2  2 4]]").unwrap();
        let scalar1 = PolyOverZ::from_str("1  2").unwrap();
        let scalar2 = PolyOverZ::from_str("1  2").unwrap();

        let mat1 = mat1 * &scalar1;
        let mat2 = &scalar2 * mat2;
        let mat3 = &mat3 * scalar1;
        let mat4 = scalar2 * &mat4;

        assert_eq!(mat5, mat1);
        assert_eq!(mat5, mat2);
        assert_eq!(mat5, mat3);
        assert_eq!(mat5, mat4);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatPolyOverZ::from_str("[[1  42],[0],[2  1 2]]").unwrap();
        let mat2 = MatPolyOverZ::from_str("[[1  2,1  6,1  5],[1  4,2  17 42,1  3]]").unwrap();
        let mat3 = MatPolyOverZ::from_str("[[1  84],[0],[2  2 4]]").unwrap();
        let mat4 = MatPolyOverZ::from_str("[[1  4,1  12,1  10],[1  8,2  34 84,1  6]]").unwrap();
        let scalar = PolyOverZ::from_str("1  2").unwrap();

        assert_eq!(mat3, &scalar * mat1);
        assert_eq!(mat4, scalar * mat2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat1 = MatPolyOverZ::from_str(&format!("[[1  1],[1  {}],[1  4]]", i64::MAX)).unwrap();
        let mat2 = MatPolyOverZ::from_str("[[1  3]]").unwrap();
        let mat3 =
            MatPolyOverZ::from_str(&format!("[[1  3],[1  {}],[1  12]]", 3 * i64::MAX as i128))
                .unwrap();
        let mat4 = MatPolyOverZ::from_str(&format!("[[1  {}]]", 3 * i64::MAX as i128)).unwrap();
        let scalar1 = PolyOverZ::from_str("1  3").unwrap();
        let scalar2 = PolyOverZ::from_str(&format!("1  {}", i64::MAX)).unwrap();

        assert_eq!(mat3, scalar1 * mat1);
        assert_eq!(mat4, scalar2 * mat2);
    }
}
