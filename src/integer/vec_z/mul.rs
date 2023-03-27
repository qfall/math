// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`VecZ`] values.

use super::{MatZ, VecZ};
use crate::macros::arithmetics::{
    arithmetic_trait_cross_types_borrowed_to_owned,
    arithmetic_trait_cross_types_mixed_borrowed_owned,
};
use std::ops::Mul;

impl Mul for &VecZ {
    type Output = MatZ;

    /// Implements the [`Mul`] trait for two [`VecZ`] values.
    /// [`Mul`] is implemented for any combination of owned and borrowed [`MatZ`] and any kind of [`VecZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatZ`].
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    /// use std::str::FromStr;
    ///
    /// let a = VecZ::from_str("[2,1,1,2]").unwrap();
    /// let b = VecZ::from_str("[1,0,0,1]").unwrap();
    ///
    /// let _ = &a.transpose() * &b;
    /// let _ = a.transpose() * b.clone();
    /// let _ = &a.transpose() * b.clone();
    /// let _ = a.transpose() * &b;
    /// ```
    fn mul(self, other: Self) -> Self::Output {
        (&self.matrix).mul(other)
    }
}

arithmetic_trait_cross_types_borrowed_to_owned!(Mul, mul, VecZ, VecZ, MatZ);
arithmetic_trait_cross_types_mixed_borrowed_owned!(Mul, mul, VecZ, VecZ, MatZ);

impl Mul<&MatZ> for &VecZ {
    type Output = MatZ;

    /// Implements the [`Mul`] trait for a [`VecZ`] multiplied with a [`MatZ`] vector.
    /// [`Mul`] is implemented for any combination of owned and borrowed [`MatZ`] and any kind of [`VecZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the [`MatZ`] value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatZ`].
    ///
    /// # Example
    /// ```
    /// use math::integer::{MatZ, VecZ};
    /// use std::str::FromStr;
    ///
    /// let a = VecZ::from_str("[1,0]").unwrap();
    /// let b = MatZ::from_str("[[2,1]]").unwrap();
    ///
    /// let c = &a * &b;
    /// let d = a.clone() * b.clone();
    /// let e = &a * b.clone();
    /// let f = a.clone() * &b;
    /// ```
    fn mul(self, other: &MatZ) -> Self::Output {
        (&self.matrix).mul(other)
    }
}

arithmetic_trait_cross_types_borrowed_to_owned!(Mul, mul, VecZ, MatZ, MatZ);
arithmetic_trait_cross_types_mixed_borrowed_owned!(Mul, mul, VecZ, MatZ, MatZ);

#[cfg(test)]
mod test_mul {

    use super::{MatZ, VecZ};
    use std::str::FromStr;

    /// Checks if vector multiplication works fine for vectors of same length
    #[test]
    fn vector_mul_vector_correctness() {
        let vec_1 = VecZ::from_str("[2,1,1,2]").unwrap();
        let vec_2 = VecZ::from_str("[1,2,2,1]").unwrap();
        let cmp = MatZ::from_str("[[8]]").unwrap();

        assert_eq!(cmp, vec_1.transpose() * vec_2);
    }

    /// Checks if vector multiplication with incompatible vector length
    /// results in panic
    #[test]
    #[should_panic]
    fn vector_mul_vector_incompatible_length() {
        let mat_1 = MatZ::from_str("[2,1,1,2]").unwrap();
        let mat_2 = MatZ::from_str("[1,0,0,1,0]").unwrap();

        let _ = mat_1 * mat_2;
    }

    /// Checks if cross-type multiplications works fine for [`VecZ`] * [`MatZ`]
    #[test]
    fn vector_mul_matrix_correctness() {
        let mat = MatZ::from_str("[[2,1]]").unwrap();
        let vec = VecZ::from_str("[1,0]").unwrap();
        let cmp = MatZ::from_str("[[2,1],[0,0]]").unwrap();

        assert_eq!(cmp, &vec * &mat);
    }

    /// Checks if multiplication of [`VecZ`] * [`MatZ`]` with incompatible dimensions
    /// results in panic
    #[test]
    #[should_panic]
    fn vector_mul_matrix_incompatible_dimensions() {
        let mat = MatZ::from_str("[[2,1],[1,2]]").unwrap();
        let vec = VecZ::from_str("[1,0,1]").unwrap();

        let _ = vec * mat;
    }
}
