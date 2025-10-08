// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar division for [`MatQ`] matrices.

use crate::{
    integer::Z,
    macros::{
        arithmetics::{
            arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
            arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
        },
        for_others::implement_for_others,
    },
    rational::{MatQ, Q},
    traits::MatrixDimensions,
};
use flint_sys::fmpq_mat::fmpq_mat_scalar_div_fmpz;
use std::ops::{Div, DivAssign, MulAssign};

impl Div<&Z> for &MatQ {
    type Output = MatQ;

    /// Implements the [`Div`] trait for a [`MatQ`] by a [`Z`] integer.
    /// [`Div`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is divided
    ///
    /// Returns the division of `self` by `scalar` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{MatQ, Q};
    /// use std::str::FromStr;
    ///
    /// let matq_1 = MatQ::from_str("[[1, 2, 3],[4, 5/4, -1]]").unwrap();
    /// let rational = Q::from((2,3));
    ///
    /// let matq_2 = &matq_1 / &rational;
    /// ```
    fn div(self, scalar: &Z) -> Self::Output {
        assert!(!scalar.is_zero(), "Tried to divide {self} by zero.");

        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpq_mat_scalar_div_fmpz(&mut out.matrix, &self.matrix, &scalar.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, MatQ, Q, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Div, div, MatQ, Q, MatQ);

implement_for_others!(Z, MatQ, Div Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Div<&Q> for &MatQ {
    type Output = MatQ;
    /// Implements the [`Div`] trait for a [`MatQ`] by a [`Q`] rational.
    /// [`Div`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is divided
    ///
    /// Returns the division of `self` by `scalar` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{MatQ, Q};
    /// use std::str::FromStr;
    ///
    /// let matq_1 = MatQ::from_str("[[1, 2, 3],[4, 5/4, -1]]").unwrap();
    /// let rational = Q::from((2,3));
    ///
    /// let matq_2 = &matq_1 / &rational;
    /// ```
    ///
    /// # Panics ...
    /// - if the `scalar` is `0`.
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, scalar: &Q) -> Self::Output {
        assert!(!scalar.is_zero(), "Tried to divide {self} by zero.");

        let scalar = scalar.inverse().unwrap();
        self * scalar
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, MatQ, Z, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Div, div, MatQ, Z, MatQ);

implement_for_others!(Q, MatQ, Div Scalar for f32 f64);

impl DivAssign<&Q> for MatQ {
    /// Computes the scalar multiplication of `self` and `other` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply to `self`
    ///
    /// Returns the scalar of the matrix as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{Q, MatQ};
    /// use qfall_math::integer::{Z};
    /// use std::str::FromStr;
    ///
    /// let mut matq = MatQ::from_str(&format!("[[1, 2, 3],[4, 5/4, -1]]")).unwrap();
    /// let q = Q::from((3, 4));
    /// let z = Z::from(5);
    ///
    /// matq *= &q;
    /// matq *= q;
    /// matq *= &z;
    /// matq *= z;
    /// matq *= -1;
    /// matq *= 2;
    /// ```
    ///
    /// # Panics ...
    /// - if the `scalar` is `0`.
    fn div_assign(&mut self, scalar: &Q) {
        assert!(!scalar.is_zero(), "Tried to divide {self} by zero.");

        let scalar = scalar.inverse().unwrap();
        self.mul_assign(scalar);
    }
}

impl DivAssign<&Z> for MatQ {
    /// Documentation at [`MatQ::div_assign`].
    fn div_assign(&mut self, scalar: &Z) {
        assert!(!scalar.is_zero(), "Tried to divide {self} by zero.");

        unsafe { fmpq_mat_scalar_div_fmpz(&mut self.matrix, &self.matrix, &scalar.value) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(DivAssign, div_assign, MatQ, Q);
arithmetic_assign_trait_borrowed_to_owned!(DivAssign, div_assign, MatQ, Z);
arithmetic_assign_between_types!(DivAssign, div_assign, MatQ, Z, u64 u32 u16 u8 i64 i32 i16 i8);
arithmetic_assign_between_types!(DivAssign, div_assign, MatQ, Q, f32 f64);

#[cfg(test)]
mod test_div_z {
    use super::MatQ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if scalar division works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let cmp = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat = MatQ::from_str("[[2, 3],[3/2, 6]]").unwrap();
        let integer = Z::from(3);

        assert_eq!(cmp, &mat / &integer);
    }

    /// Checks if scalar division works fine for both owned
    #[test]
    fn owned_correctness() {
        let cmp = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat = MatQ::from_str("[[2, 3],[3/2, 6]]").unwrap();
        let integer = Z::from(3);

        assert_eq!(cmp, mat / integer);
    }

    /// Checks if scalar division works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let cmp = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat = MatQ::from_str("[[2, 3],[3/2, 6]]").unwrap();
        let integer = Z::from(3);

        assert_eq!(cmp, &mat / integer.clone());
        assert_eq!(cmp, mat / &integer);
    }

    /// Checks if scalar division works fine for different scalar types
    #[test]
    #[allow(clippy::erasing_op)]
    fn different_types() {
        let mat_1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat_2 = MatQ::from_str("[[2, 5, 6],[1, 3, 1]]").unwrap();
        let mat_3 = MatQ::from_str("[[1],[0],[8]]").unwrap();
        let mat_5 = MatQ::from_str("[[-1/2],[0],[-4]]").unwrap();
        let mat_6 = MatQ::from_str("[[6, 15, 18],[3, 9, 3]]").unwrap();

        assert_eq!(&mat_3 / 2u8, mat_1);
        assert_eq!(&mat_3 / 2i8, mat_1);
        assert_eq!(&mat_3 / 2u16, mat_1);
        assert_eq!(&mat_3 / 2i16, mat_1);
        assert_eq!(&mat_3 / 2u32, mat_1);
        assert_eq!(&mat_3 / 2i32, mat_1);
        assert_eq!(&mat_3 / 2u64, mat_1);
        assert_eq!(&mat_3 / 2i64, mat_1);
        assert_eq!(mat_5, &mat_1 / -1);
        assert_eq!(&mat_6 / 3, mat_2);
    }

    /// Checks if scalar division works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat_1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat_2 = MatQ::from_str("[[2, 5/8, 6],[1, 3, 1/7]]").unwrap();
        let mat_3 = MatQ::from_str("[[3/2],[0],[12]]").unwrap();
        let mat_4 = MatQ::from_str("[[6, 15/8, 18],[3, 9, 3/7]]").unwrap();
        let integer = Z::from(3);

        assert_eq!(mat_1, mat_3 / &integer);
        assert_eq!(mat_2, mat_4 / integer);
    }

    /// Checks if matrix division works fine for large values
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

        assert_eq!(mat_3 / integer_1, mat_1);
        assert_eq!(mat_4 / integer_2, mat_2);
    }

    /// Ensure that `div` panics if a division by `0` occurs
    #[test]
    #[should_panic]
    fn div_0() {
        let mat = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let integer = Z::from(0);

        let _ = &mat / &integer;
    }
}

#[cfg(test)]
mod test_mul_q {

    use super::MatQ;
    use crate::rational::Q;
    use std::str::FromStr;

    /// Checks if matrix division works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat = MatQ::from_str("[[1, 3/2],[3/4, 3]]").unwrap();
        let rational = Q::from((3, 2));
        let cmp = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();

        assert_eq!(&mat / &rational, cmp);
    }

    /// Checks if scalar division works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat = MatQ::from_str("[[1, 3/2],[3/4, 3]]").unwrap();
        let rational = Q::from((3, 2));
        let cmp = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();

        assert_eq!(mat / rational, cmp);
    }

    /// Checks if scalar division works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat = MatQ::from_str("[[1, 3/2],[3/4, 3]]").unwrap();
        let rational = Q::from((3, 2));
        let cmp = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();

        assert_eq!(&mat / rational.clone(), cmp);
        assert_eq!(mat / &rational, cmp);
    }

    /// Checks if scalar division works fine for different scalar types
    #[test]
    #[allow(clippy::erasing_op)]
    fn different_types() {
        let mat_1 = MatQ::from_str("[[1/2],[0],[4]]").unwrap();
        let mat_2 = MatQ::from_str("[[2, 5, 6],[1, 3, 1]]").unwrap();
        let mat_3 = MatQ::from_str("[[5/4],[0],[10]]").unwrap();
        let mat_4 = MatQ::from_str("[[-799/8],[0],[-799]]").unwrap();
        let mat_5 = MatQ::from_str("[[285/4, 1425/8, 855/4],[285/8, 855/8, 285/8]]").unwrap();

        assert_eq!(mat_3 / 2.5f32, mat_1);
        assert_eq!(mat_4 / -199.75f64, mat_1);
        assert_eq!(mat_5 / 35.625, mat_2);
    }

    /// Checks if scalar division works fine for matrices of different dimensions
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

    /// Checks if matrix division works fine for large values
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

        assert_eq!(mat_3 / rational_1, mat_1);
        assert_eq!(mat_4 / rational_2, mat_2);
        assert_eq!(mat_5 / rational_3, mat_2);
    }

    /// Ensure that `div` panics if a division by `0` occurs
    #[test]
    #[should_panic]
    fn div_0() {
        let mat = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let rational = Q::from(0);

        let _ = &mat / &rational;
    }
}

#[cfg(test)]
mod test_div_assign {
    use crate::integer::Z;
    use crate::rational::{MatQ, Q};
    use std::str::FromStr;

    /// Ensure that `div_assign` produces same output as normal division.
    #[test]
    fn consistency() {
        let mut a = MatQ::from_str("[[2, 1],[-1, 0]]").unwrap();
        let b = Q::from((1, i32::MAX));
        let cmp = &a / &b;

        a /= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `div_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = MatQ::from_str("[[2, 1],[1, 2]]").unwrap();
        let b = Z::from(2);
        let c = Q::from((2, 3));

        a /= &b;
        a /= b;
        a /= &c;
        a /= c;
        a /= 1_u8;
        a /= 1_u16;
        a /= 1_u32;
        a /= 1_u64;
        a /= 1_i8;
        a /= 1_i16;
        a /= 1_i32;
        a /= 1_i64;
        a /= 1_f32;
        a /= 1_f64;
    }

    /// Ensure that `div_assign` panics if a division by 0 would occur.
    #[test]
    #[should_panic]
    fn div_0() {
        let mut a = MatQ::from_str("[[2, 1],[-1, 0]]").unwrap();
        let b = Q::from((0, i32::MAX));

        a /= b;
    }
}
