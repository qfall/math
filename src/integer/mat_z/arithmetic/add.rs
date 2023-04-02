// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`MatZ`] values.

use super::super::MatZ;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_mat::fmpz_mat_add;
use std::ops::Add;

impl Add for &MatZ {
    type Output = MatZ;
    /// Implements the [`Add`] trait for two [`MatZ`] values.
    /// [`Add`] is implemented for any combination of [`MatZ`] and borrowed [`MatZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`MatZ`].
    ///
    /// # Example
    /// ```
    /// use math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, 4, 5]]")).unwrap();
    /// let b: MatZ = MatZ::from_str(&String::from("[[1, 9, 3],[1, 0, 5]]")).unwrap();
    ///
    /// let c: MatZ = &a + &b;
    /// let d: MatZ = a + b;
    /// let e: MatZ = &c + d;
    /// let f: MatZ = c + &e;
    /// ```
    ///
    /// # Panics
    /// - Panics if the dimensions of both matrices mismatch
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

impl MatZ {
    /// Implements addition for two [`MatZ`] matrixes.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both matrixes as a [`MatZ`] or an
    /// error if the matrix dimensions do mismatch.
    ///
    /// # Example
    /// ```
    /// use math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, 4, 5]]")).unwrap();
    /// let b: MatZ = MatZ::from_str(&String::from("[[1, 9, 3],[1, 0, 5]]")).unwrap();
    ///
    /// let c: MatZ = a.add_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// Returns a [`MathError`] of type
    /// [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    /// do mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<MatZ, MathError> {
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
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        unsafe {
            fmpz_mat_add(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatZ);

#[cfg(test)]
mod test_add {

    use super::MatZ;
    use std::str::FromStr;

    /// testing addition for two [`MatZ`]
    #[test]
    fn add() {
        let a: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, 4, 5]]")).unwrap();
        let b: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, -4, 5]]")).unwrap();
        let c: MatZ = a + b;
        assert!(c == MatZ::from_str(&String::from("[[2, 4, 6],[6, 0, 10]]")).unwrap());
    }

    /// testing addition for two borrowed [`MatZ`]
    #[test]
    fn add_borrow() {
        let a: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, 4, 5]]")).unwrap();
        let b: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, -4, 5]]")).unwrap();
        let c: MatZ = &a + &b;
        assert!(c == MatZ::from_str(&String::from("[[2, 4, 6],[6, 0, 10]]")).unwrap());
    }

    /// testing addition for borrowed [`MatZ`] and [`MatZ`]
    #[test]
    fn add_first_borrowed() {
        let a: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, 4, 5]]")).unwrap();
        let b: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, -4, 5]]")).unwrap();
        let c: MatZ = &a + b;
        assert!(c == MatZ::from_str(&String::from("[[2, 4, 6],[6, 0, 10]]")).unwrap());
    }

    /// testing addition for [`MatZ`] and borrowed [`MatZ`]
    #[test]
    fn add_second_borrowed() {
        let a: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, 4, 5]]")).unwrap();
        let b: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, -4, 5]]")).unwrap();
        let c: MatZ = a + &b;
        assert!(c == MatZ::from_str(&String::from("[[2, 4, 6],[6, 0, 10]]")).unwrap());
    }

    /// testing addition for big numbers
    #[test]
    fn add_large_numbers() {
        let a: MatZ = MatZ::from_str(&String::from(format!(
            "[[1, 2, {}],[3, -4, {}]]",
            i32::MIN,
            i32::MAX
        )))
        .unwrap();
        let b: MatZ = MatZ::from_str(&String::from(format!(
            "[[1, 2, {}],[3, 9, {}]]",
            i32::MIN + 1,
            i32::MAX
        )))
        .unwrap();
        let c: MatZ = a + &b;
        assert!(
            c == MatZ::from_str(&String::from(format!(
                "[[2, 4, -{}],[6, 5, {}]]",
                u32::MAX,
                u32::MAX - 1
            )))
            .unwrap()
        );
    }

    /// testing add_safe
    #[test]
    fn add_safe() {
        let a: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, 4, 5]]")).unwrap();
        let b: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, -4, 5]]")).unwrap();
        let c = a.add_safe(&b);
        assert!(c.unwrap() == MatZ::from_str(&String::from("[[2, 4, 6],[6, 0, 10]]")).unwrap());
    }

    /// testing add_safe throws error
    #[test]
    fn add_safe_is_err() {
        let a: MatZ = MatZ::from_str(&String::from("[[1, 2],[3, 4]]")).unwrap();
        let b: MatZ = MatZ::from_str(&String::from("[[1, 2, 3],[3, -4, 5]]")).unwrap();
        let c: MatZ = MatZ::from_str(&String::from("[[1, 2, 3]]")).unwrap();
        assert!(a.add_safe(&b).is_err());
        assert!(c.add_safe(&b).is_err());
    }
}
