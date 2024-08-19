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
    /// Implements the [`Mul`] trait for a [`MatQ`] matrix with a [`Z`] integer.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat_2 = &mat_1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns());
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
    /// Implements the [`Mul`] trait for a [`MatQ`] matrix with a [`Q`] rational.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
    /// let rational = Q::from(3/7);
    ///
    /// let mat_2 = &mat_1 * &rational;
    /// ```
    fn mul(self, scalar: &Q) -> Self::Output {
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns());
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
        let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatQ::from_str("[[2, 3],[3/2, 6]]").unwrap();
        let integer = Z::from(3);

        let mat_1 = &mat_1 * &integer;
        let mat_2 = &integer * &mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatQ::from_str("[[2, 3],[3/2, 6]]").unwrap();
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
        let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = mat_1.clone();
        let mat_4 = mat_1.clone();
        let mat_5 = MatQ::from_str("[[2, 3],[3/2, 6]]").unwrap();
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
        let mat_1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat_2 = MatQ::from_str("[[2, 5, 6],[1, 3, 1]]").unwrap();
        let mat_3 = MatQ::from_str("[[1],[0],[8]]").unwrap();
        let mat_4 = MatQ::from_str("[[0],[0],[0]]").unwrap();
        let mat_5 = MatQ::from_str("[[-1/2],[0],[-4]]").unwrap();
        let mat_6 = MatQ::from_str("[[6, 15, 18],[3, 9, 3]]").unwrap();

        assert_eq!(mat_3, 2u8 * &mat_1);
        assert_eq!(mat_3, 2i8 * &mat_1);
        assert_eq!(mat_3, 2u16 * &mat_1);
        assert_eq!(mat_3, 2i16 * &mat_1);
        assert_eq!(mat_3, 2u32 * &mat_1);
        assert_eq!(mat_3, 2i32 * &mat_1);
        assert_eq!(mat_3, 2u64 * &mat_1);
        assert_eq!(mat_3, 2i64 * &mat_1);
        assert_eq!(mat_4, 0 * &mat_1);
        assert_eq!(mat_5, -1 * mat_1);
        assert_eq!(mat_6, mat_2 * 3);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat_1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat_2 = MatQ::from_str("[[2, 5/8, 6],[1, 3, 1/7]]").unwrap();
        let mat_3 = MatQ::from_str("[[3/2],[0],[12]]").unwrap();
        let mat_4 = MatQ::from_str("[[6, 15/8, 18],[3, 9, 3/7]]").unwrap();
        let integer = Z::from(3);

        assert_eq!(mat_3, &integer * mat_1);
        assert_eq!(mat_4, integer * mat_2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat_1 = MatQ::from_str(&format!("[[1],[{}],[1/{}]]", i64::MAX, i64::MAX)).unwrap();
        let mat_2 = MatQ::from_str("[[3]]").unwrap();
        let mat_3 = MatQ::from_str(&format!(
            "[[3],[{}],[3/{}]]",
            3 * i64::MAX as i128,
            i64::MAX
        ))
        .unwrap();
        let mat_4 = MatQ::from_str(&format!("[[{}]]", 3 * i64::MAX as i128)).unwrap();
        let integer_1 = Z::from(3);
        let integer_2 = Z::from(i64::MAX);

        assert_eq!(mat_3, integer_1 * mat_1);
        assert_eq!(mat_4, integer_2 * mat_2);
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
        let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatQ::from_str("[[1, 3/2],[3/4, 3]]").unwrap();
        let rational = Q::from((3, 2));

        let mat_1 = &mat_1 * &rational;
        let mat_2 = &mat_2 * &rational;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatQ::from_str("[[1, 3/2],[3/4, 3]]").unwrap();
        let rational_1 = Q::from((3, 2));
        let rational_2 = Q::from((3, 2));

        let mat_1 = mat_1 * rational_1;
        let mat_2 = rational_2 * mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = mat_1.clone();
        let mat_4 = mat_1.clone();
        let mat_5 = MatQ::from_str("[[1, 3/2],[3/4, 3]]").unwrap();
        let rational_1 = Q::from((3, 2));
        let rational_2 = Q::from((3, 2));

        let mat_1 = mat_1 * &rational_1;
        let mat_2 = &rational_2 * mat_2;
        let mat_3 = &mat_3 * rational_1;
        let mat_4 = rational_2 * &mat_4;

        assert_eq!(mat_5, mat_1);
        assert_eq!(mat_5, mat_2);
        assert_eq!(mat_5, mat_3);
        assert_eq!(mat_5, mat_4);
    }

    /// Checks if scalar multiplication works fine for different scalar types
    #[test]
    #[allow(clippy::erasing_op)]
    fn different_types() {
        let mat_1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat_2 = MatQ::from_str("[[2, 5, 6],[1, 3, 1]]").unwrap();
        let mat_3 = MatQ::from_str("[[5/4],[0],[10]]").unwrap();
        let mat_4 = MatQ::from_str("[[-799/8],[0],[-799]]").unwrap();
        let mat_5 = MatQ::from_str("[[285/4, 1425/8, 855/4],[285/8, 855/8, 285/8]]").unwrap();

        assert_eq!(mat_3, 2.5f32 * &mat_1);
        assert_eq!(mat_4, -199.75f64 * mat_1);
        assert_eq!(mat_5, mat_2 * 35.625);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat_1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat_2 = MatQ::from_str("[[2, 5/8, 6],[1, 3, 1/7]]").unwrap();
        let mat_3 = MatQ::from_str("[[3/4],[0],[6]]").unwrap();
        let mat_4 = MatQ::from_str("[[3, 15/16, 9],[3/2, 9/2, 3/14]]").unwrap();
        let rational = Q::from((3, 2));

        assert_eq!(mat_3, &rational * mat_1);
        assert_eq!(mat_4, rational * mat_2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat_1 = MatQ::from_str(&format!("[[1],[{}],[1/{}]]", i64::MAX, i64::MAX)).unwrap();
        let mat_2 = MatQ::from_str("[[3]]").unwrap();
        let mat_3 = MatQ::from_str(&format!(
            "[[3/2],[{}/2],[3/{}]]",
            3 * i64::MAX as i128,
            2 * i64::MAX as i128
        ))
        .unwrap();
        let mat_4 = MatQ::from_str(&format!("[[{}/2]]", 3 * i64::MAX as i128)).unwrap();
        let mat_5 = MatQ::from_str(&format!("[[6/{}]]", i64::MAX)).unwrap();
        let rational_1 = Q::from((3, 2));
        let rational_2 = Q::from((i64::MAX, 2));
        let rational_3 = Q::from((2, i64::MAX));

        assert_eq!(mat_3, rational_1 * mat_1);
        assert_eq!(mat_4, rational_2 * &mat_2);
        assert_eq!(mat_5, rational_3 * mat_2);
    }
}
