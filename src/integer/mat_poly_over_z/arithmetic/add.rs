// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`MatPolyOverZ`] values.

use super::super::MatPolyOverZ;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_add;
use std::ops::Add;

impl Add for &MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Implements the [`Add`] trait for two [`MatPolyOverZ`] values.
    /// [`Add`] is implemented for any combination of [`MatPolyOverZ`] and borrowed [`MatPolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`MatPolyOverZ`].
    ///
    /// # Example
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str(&String::from("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]")).unwrap();
    /// let b: MatPolyOverZ = MatPolyOverZ::from_str(&String::from("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]")).unwrap();
    ///
    /// let c: MatPolyOverZ = &a + &b;
    /// let d: MatPolyOverZ = a + b;
    /// let e: MatPolyOverZ = &c + d;
    /// let f: MatPolyOverZ = c + &e;
    /// ```
    ///
    /// # Panics
    /// - Panics if the dimensions of both matrices mismatch
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

impl MatPolyOverZ {
    /// Implements addition for two [`MatPolyOverZ`] matrixes.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both matrixes as a [`MatPolyOverZ`] or an
    /// error if the matrix dimensions do mismatch.
    ///
    /// # Example
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str(&String::from("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]")).unwrap();
    /// let b: MatPolyOverZ = MatPolyOverZ::from_str(&String::from("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]")).unwrap();
    ///
    /// let c: MatPolyOverZ = a.add_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// Returns a [`MathError`] of type
    /// [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    /// do mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<MatPolyOverZ, MathError> {
        if self.get_num_rows() != other.get_num_rows()
            || self.get_num_columns() != other.get_num_columns()
        {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to add a '{}x{}' matrix and a '{}x{}' matrix.", //todo display?
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            )));
        }
        let mut out = MatPolyOverZ::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        unsafe {
            fmpz_poly_mat_add(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatPolyOverZ);

#[cfg(test)]
mod test_add {

    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// testing addition for two [`MatPolyOverZ`]
    #[test]
    fn add() {
        let a: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
        ))
        .unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]",
        ))
        .unwrap();

        let c: MatPolyOverZ = a + b;
        assert!(
            c == MatPolyOverZ::from_str(&String::from(
                "[[1  -42, 1  42, 2  66 66],[3  18 36 46, 1  16, 1  59]]"
            ))
            .unwrap()
        );
    }

    /// testing addition for two borrowed [`MatPolyOverZ`]
    #[test]
    fn add_borrow() {
        let a: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
        ))
        .unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]",
        ))
        .unwrap();

        let c: MatPolyOverZ = &a + &b;
        assert!(
            c == MatPolyOverZ::from_str(&String::from(
                "[[1  -42, 1  42, 2  66 66],[3  18 36 46, 1  16, 1  59]]"
            ))
            .unwrap()
        );
    }

    /// testing addition for borrowed [`MatPolyOverZ`] and [`MatPolyOverZ`]
    #[test]
    fn add_first_borrowed() {
        let a: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
        ))
        .unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]",
        ))
        .unwrap();

        let c: MatPolyOverZ = &a + b;
        assert!(
            c == MatPolyOverZ::from_str(&String::from(
                "[[1  -42, 1  42, 2  66 66],[3  18 36 46, 1  16, 1  59]]"
            ))
            .unwrap()
        );
    }

    /// testing addition for [`MatPolyOverZ`] and borrowed [`MatPolyOverZ`]
    #[test]
    fn add_second_borrowed() {
        let a: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
        ))
        .unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]",
        ))
        .unwrap();

        let c: MatPolyOverZ = a + &b;
        assert!(
            c == MatPolyOverZ::from_str(&String::from(
                "[[1  -42, 1  42, 2  66 66],[3  18 36 46, 1  16, 1  59]]"
            ))
            .unwrap()
        );
    }

    /// testing addition for big numbers
    #[test]
    fn add_large_numbers() {
        let a: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(format!(
            "[[1  {},2  1 {}],[2  -{} 7, 0]]",
            i32::MAX,
            i32::MIN,
            u32::MAX
        )))
        .unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(format!(
            "[[1  {},2  1 {}],[2  {} 7, 0]]",
            i32::MAX,
            i32::MIN + 1,
            i32::MAX
        )))
        .unwrap();
        let c: MatPolyOverZ = a + &b;
        assert!(
            c == MatPolyOverZ::from_str(&String::from(format!(
                "[[1  {},2  2 -{}],[2  -{} 14, 0]]",
                u32::MAX - 1,
                u32::MAX,
                (u32::MAX - 1) / 2 + 1
            )))
            .unwrap()
        );
    }

    /// testing add_safe
    #[test]
    fn add_safe() {
        let a: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
        ))
        .unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]",
        ))
        .unwrap();

        let c: MatPolyOverZ = a.add_safe(&b).unwrap();
        assert!(
            c == MatPolyOverZ::from_str(&String::from(
                "[[1  -42, 1  42, 2  66 66],[3  18 36 46, 1  16, 1  59]]"
            ))
            .unwrap()
        );
    }

    /// testing add_safe throws error
    #[test]
    fn add_safe_is_err() {
        let a: MatPolyOverZ = MatPolyOverZ::from_str(&String::from(
            "[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]",
        ))
        .unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str(&String::from("[[1  -42, 0],[3  1 12 4, 1  17]]")).unwrap();
        let c: MatPolyOverZ =
            MatPolyOverZ::from_str(&String::from("[[0, 1  42, 2  42 24]]")).unwrap();
        assert!(a.add_safe(&b).is_err());
        assert!(c.add_safe(&b).is_err());
    }
}
