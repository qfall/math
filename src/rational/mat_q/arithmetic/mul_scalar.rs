// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`MatQ`] matrices.

use super::super::MatQ;
use crate::integer::Z;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::rational::Q;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpq_mat::{fmpq_mat_scalar_mul_fmpq, fmpq_mat_scalar_mul_fmpz};
use std::ops::Mul;

impl Mul<&Z> for &MatQ {
    type Output = MatQ;
    /// Implements multiplication for a [`MatQ`] matrix with a [`Z`] integer.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `other` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mat1 = MatQ::from_str("[[2/3,1],[1/2,2]]").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat2 = &mat1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        unsafe {
            fmpq_mat_scalar_mul_fmpz(&mut out.matrix, &self.matrix, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Q, MatQ, MatQ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatQ, Q, MatQ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Q, MatQ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatQ, Q, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Q, MatQ, MatQ);

implement_for_others!(Z, MatQ, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Mul<&Q> for &MatQ {
    type Output = MatQ;
    /// Implements multiplication for a [`MatQ`] matrix with a [`Q`] rational.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `other` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let mat1 = MatQ::from_str("[[2/3,1],[1/2,2]]").unwrap();
    /// let rational = Q::from(3/7);
    ///
    /// let mat2 = &mat1 * &rational;
    /// ```
    fn mul(self, scalar: &Q) -> Self::Output {
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        unsafe {
            fmpq_mat_scalar_mul_fmpq(&mut out.matrix, &self.matrix, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Z, MatQ, MatQ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatQ, Z, MatQ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, MatQ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatQ, Z, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, MatQ, MatQ);

implement_for_others!(Q, MatQ, Mul Scalar for f32 f64);

#[cfg(test)]
mod test_mul_z {

    use super::MatQ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat1 = MatQ::from_str("[[2/3,1],[1/2,2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatQ::from_str("[[2,3],[3/2,6]]").unwrap();
        let integer = Z::from(3);

        let mat1 = &mat1 * &integer;
        let mat2 = &integer * &mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat1 = MatQ::from_str("[[2/3,1],[1/2,2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatQ::from_str("[[2,3],[3/2,6]]").unwrap();
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
        let mat1 = MatQ::from_str("[[2/3,1],[1/2,2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = mat1.clone();
        let mat4 = mat1.clone();
        let mat5 = MatQ::from_str("[[2,3],[3/2,6]]").unwrap();
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
        let mat1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat2 = MatQ::from_str("[[2,5,6],[1,3,1]]").unwrap();
        let mat3 = MatQ::from_str("[[1],[0],[8]]").unwrap();
        let mat4 = MatQ::from_str("[[0],[0],[0]]").unwrap();
        let mat5 = MatQ::from_str("[[-1/2],[0],[-4]]").unwrap();
        let mat6 = MatQ::from_str("[[6,15,18],[3,9,3]]").unwrap();

        assert_eq!(mat3, 2u8 * &mat1);
        assert_eq!(mat3, 2i8 * &mat1);
        assert_eq!(mat3, 2u16 * &mat1);
        assert_eq!(mat3, 2i16 * &mat1);
        assert_eq!(mat3, 2u32 * &mat1);
        assert_eq!(mat3, 2i32 * &mat1);
        assert_eq!(mat3, 2u64 * &mat1);
        assert_eq!(mat3, 2i64 * &mat1);
        assert_eq!(mat4, 0 * &mat1);
        assert_eq!(mat5, -1 * mat1);
        assert_eq!(mat6, mat2 * 3);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat2 = MatQ::from_str("[[2,5/8,6],[1,3,1/7]]").unwrap();
        let mat3 = MatQ::from_str("[[3/2],[0],[12]]").unwrap();
        let mat4 = MatQ::from_str("[[6,15/8,18],[3,9,3/7]]").unwrap();
        let integer = Z::from(3);

        assert_eq!(mat3, &integer * mat1);
        assert_eq!(mat4, integer * mat2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat1 = MatQ::from_str(&format!("[[1],[{}],[1/{}]]", i64::MAX, i64::MAX)).unwrap();
        let mat2 = MatQ::from_str("[[3]]").unwrap();
        let mat3 = MatQ::from_str(&format!(
            "[[3],[{}],[3/{}]]",
            3 * i64::MAX as i128,
            i64::MAX
        ))
        .unwrap();
        let mat4 = MatQ::from_str(&format!("[[{}]]", 3 * i64::MAX as i128)).unwrap();
        let integer1 = Z::from(3);
        let integer2 = Z::from(i64::MAX);

        assert_eq!(mat3, integer1 * mat1);
        assert_eq!(mat4, integer2 * mat2);
    }
}

#[cfg(test)]
mod test_mul_q {

    use super::MatQ;
    use crate::rational::Q;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat1 = MatQ::from_str("[[2/3,1],[1/2,2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatQ::from_str("[[1,3/2],[3/4,3]]").unwrap();
        let rational = Q::try_from((&3, &2)).unwrap();

        let mat1 = &mat1 * &rational;
        let mat2 = &mat2 * &rational;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat1 = MatQ::from_str("[[2/3,1],[1/2,2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatQ::from_str("[[1,3/2],[3/4,3]]").unwrap();
        let rational1 = Q::try_from((&3, &2)).unwrap();
        let rational2 = Q::try_from((&3, &2)).unwrap();

        let mat1 = mat1 * rational1;
        let mat2 = rational2 * mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat1 = MatQ::from_str("[[2/3,1],[1/2,2]]").unwrap();
        let mat2 = mat1.clone();
        let mat3 = mat1.clone();
        let mat4 = mat1.clone();
        let mat5 = MatQ::from_str("[[1,3/2],[3/4,3]]").unwrap();
        let rational1 = Q::try_from((&3, &2)).unwrap();
        let rational2 = Q::try_from((&3, &2)).unwrap();

        let mat1 = mat1 * &rational1;
        let mat2 = &rational2 * mat2;
        let mat3 = &mat3 * rational1;
        let mat4 = rational2 * &mat4;

        assert_eq!(mat5, mat1);
        assert_eq!(mat5, mat2);
        assert_eq!(mat5, mat3);
        assert_eq!(mat5, mat4);
    }

    /// Checks if scalar multiplication works fine for different scalar types
    #[test]
    #[allow(clippy::erasing_op)]
    fn different_types() {
        let mat1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat2 = MatQ::from_str("[[2,5,6],[1,3,1]]").unwrap();
        let mat3 = MatQ::from_str("[[5/4],[0],[10]]").unwrap();
        let mat4 = MatQ::from_str("[[-1999/20],[0],[-3998/5]]").unwrap();
        let mat5 = MatQ::from_str("[[357/5, 357/2, 1071/5],[357/10, 1071/10, 357/10]]").unwrap();

        assert_eq!(mat3, 2.5f32 * &mat1);
        assert_eq!(mat4, -199.9f64 * mat1);
        assert_eq!(mat5, mat2 * 35.7);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat2 = MatQ::from_str("[[2,5/8,6],[1,3,1/7]]").unwrap();
        let mat3 = MatQ::from_str("[[3/4],[0],[6]]").unwrap();
        let mat4 = MatQ::from_str("[[3,15/16,9],[3/2,9/2,3/14]]").unwrap();
        let rational = Q::try_from((&3, &2)).unwrap();

        assert_eq!(mat3, &rational * mat1);
        assert_eq!(mat4, rational * mat2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat1 = MatQ::from_str(&format!("[[1],[{}],[1/{}]]", i64::MAX, i64::MAX)).unwrap();
        let mat2 = MatQ::from_str("[[3]]").unwrap();
        let mat3 = MatQ::from_str(&format!(
            "[[3/2],[{}/2],[3/{}]]",
            3 * i64::MAX as i128,
            2 * i64::MAX as i128
        ))
        .unwrap();
        let mat4 = MatQ::from_str(&format!("[[{}/2]]", 3 * i64::MAX as i128)).unwrap();
        let mat5 = MatQ::from_str(&format!("[[6/{}]]", i64::MAX)).unwrap();
        let rational1 = Q::try_from((&3, &2)).unwrap();
        let rational2 = Q::try_from((&i64::MAX, &2)).unwrap();
        let rational3 = Q::try_from((&2, &i64::MAX)).unwrap();

        assert_eq!(mat3, rational1 * mat1);
        assert_eq!(mat4, rational2 * &mat2);
        assert_eq!(mat5, rational3 * mat2);
    }
}
