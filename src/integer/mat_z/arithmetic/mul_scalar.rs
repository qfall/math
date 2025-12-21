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
    arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::rational::{MatQ, Q};
use crate::traits::MatrixDimensions;
use flint_sys::fmpz_mat::{
    fmpz_mat_scalar_mul_fmpz, fmpz_mat_scalar_mul_si, fmpz_mat_scalar_mul_ui,
};
use std::ops::{Mul, MulAssign};

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

implement_for_others!(Z, MatZ, MatZ, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Mul<&Q> for &MatZ {
    type Output = MatQ;
    /// Implements the [`Mul`] trait for a [`MatZ`] matrix with a [`Q`] rational.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::rational::{MatQ, Q};
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
    /// let rational = Q::from((1,3));
    ///
    /// let mat_2 = &mat_1 * &rational;
    /// ```
    fn mul(self, scalar: &Q) -> Self::Output {
        let out = MatQ::from(self);
        out * scalar
    }
}

arithmetic_trait_reverse!(Mul, mul, Q, MatZ, MatQ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZ, Q, MatQ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Q, MatZ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZ, Q, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Q, MatZ, MatQ);

implement_for_others!(Q, MatZ, MatQ, Mul Scalar for f32 f64);

impl MulAssign<&Z> for MatZ {
    /// Computes the scalar multiplication of `self` and `scalar` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `scalar`: specifies the value to multiply to `self`
    ///
    /// Returns the scalar of the matrix as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{Z,MatZ};
    /// use std::str::FromStr;
    ///
    /// let mut a = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
    /// let b = Z::from(2);
    ///
    /// a *= &b;
    /// a *= b;
    /// a *= 2;
    /// a *= -2;
    /// ```
    fn mul_assign(&mut self, scalar: &Z) {
        unsafe { fmpz_mat_scalar_mul_fmpz(&mut self.matrix, &self.matrix, &scalar.value) };
    }
}

impl MulAssign<i64> for MatZ {
    /// Documentation at [`MatZ::mul_assign`].
    fn mul_assign(&mut self, scalar: i64) {
        unsafe { fmpz_mat_scalar_mul_si(&mut self.matrix, &self.matrix, scalar) };
    }
}

impl MulAssign<u64> for MatZ {
    /// Documentation at [`MatZ::mul_assign`].
    fn mul_assign(&mut self, scalar: u64) {
        unsafe { fmpz_mat_scalar_mul_ui(&mut self.matrix, &self.matrix, scalar) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, MatZ, Z);
arithmetic_assign_between_types!(MulAssign, mul_assign, MatZ, i64, i32 i16 i8);
arithmetic_assign_between_types!(MulAssign, mul_assign, MatZ, u64, u32 u16 u8);

#[cfg(test)]
mod test_mul {
    use super::MatZ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if scalar multiplication works fine for both borrowed
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

    /// Checks if scalar multiplication works fine for large values
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

    /// Checks if scalar multiplication is available for any integer type
    #[test]
    fn availability() {
        let mat = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let integer = Z::from(3);

        let _ = &mat * 1u8;
        let _ = &mat * 1u16;
        let _ = &mat * 1u32;
        let _ = &mat * 1u64;
        let _ = &mat * 1i8;
        let _ = &mat * 1i16;
        let _ = &mat * 1i32;
        let _ = &mat * 1i64;
        let _ = &mat * &integer;
        let _ = &mat * integer;
    }
}

#[cfg(test)]
mod test_mul_q {
    use super::MatZ;
    use crate::rational::{MatQ, Q};
    use std::str::FromStr;

    /// Checks if scalar multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatQ::from_str("[[2/3, 1/3],[1/3, 2/3]]").unwrap();
        let rational = Q::from((1, 3));

        let mat_1 = &mat_1 * &rational;
        let mat_2 = &rational * &mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatQ::from_str("[[2/3, 1/3],[1/3, 2/3]]").unwrap();
        let rational = Q::from((1, 3));

        let mat_1 = mat_1 * rational.clone();
        let mat_2 = rational * mat_2;

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
        let mat_5 = MatQ::from_str("[[2/3, 1/3],[1/3, 2/3]]").unwrap();
        let rational = Q::from((1, 3));

        let mat_1 = mat_1 * &rational;
        let mat_2 = &rational * mat_2;
        let mat_3 = &mat_3 * rational.clone();
        let mat_4 = rational * &mat_4;

        assert_eq!(mat_5, mat_1);
        assert_eq!(mat_5, mat_2);
        assert_eq!(mat_5, mat_3);
        assert_eq!(mat_5, mat_4);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat_1 = MatZ::from_str("[[1],[0],[4]]").unwrap();
        let mat_2 = MatZ::from_str("[[2, 5, 6],[1, 3, 1]]").unwrap();
        let mat_3 = MatQ::from_str("[[1/3],[0],[4/3]]").unwrap();
        let mat_4 = MatQ::from_str("[[2/3, 5/3, 6/3],[1/3, 1, 1/3]]").unwrap();
        let integer = Q::from((1, 3));

        assert_eq!(mat_3, &integer * mat_1);
        assert_eq!(mat_4, integer * mat_2);
    }

    /// Checks if scalar multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat_1 = MatZ::from_str(&format!("[[1],[{}],[4]]", i64::MAX)).unwrap();
        let mat_2 = MatZ::from_str("[[3]]").unwrap();
        let mat_3 = MatQ::from_str(&format!("[[1/3],[{}/3],[4/3]]", i64::MAX)).unwrap();
        let mat_4 = MatQ::from_str(&format!("[[3/{}]]", i64::MAX)).unwrap();
        let rational_1 = Q::from((1, 3));
        let rational_2 = Q::from((1, i64::MAX));

        assert_eq!(mat_3, rational_1 * mat_1);
        assert_eq!(mat_4, rational_2 * mat_2);
    }

    /// Checks if scalar multiplication is available for any rational type
    #[test]
    fn availability() {
        let mat = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let rational = Q::from(3);

        let _ = &mat * 1.0f32;
        let _ = &mat * 1.0f64;
        let _ = &mat * &rational;
        let _ = &mat * rational;
    }
}

#[cfg(test)]
mod test_mul_assign {
    use crate::integer::{MatZ, Z};
    use std::str::FromStr;

    /// Ensure that `mul_assign` produces same output as normal multiplication.
    #[test]
    fn consistency() {
        let mut a = MatZ::from_str("[[2, 1],[-1, 0]]").unwrap();
        let b = i32::MAX;
        let cmp = &a * b;

        a *= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `mul_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let b = Z::from(2);

        a *= &b;
        a *= b;
        a *= 1_u8;
        a *= 1_u16;
        a *= 1_u32;
        a *= 1_u64;
        a *= 1_i8;
        a *= 1_i16;
        a *= 1_i32;
        a *= 1_i64;
    }
}
