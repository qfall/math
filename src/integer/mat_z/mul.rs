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
    integer::VecZ,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_cross_types_borrowed_to_owned,
        arithmetic_trait_cross_types_mixed_borrowed_owned, arithmetic_trait_mixed_borrowed_owned,
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
    fn mul(self, other: Self) -> Self::Output {
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
