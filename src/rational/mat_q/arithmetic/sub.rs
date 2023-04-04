// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`MatQ`] values.

use super::super::MatQ;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpq_mat::fmpq_mat_sub;
use std::ops::Sub;

impl Sub for &MatQ {
    type Output = MatQ;
    /// Implements the [`Sub`] trait for two [`MatQ`] values.
    /// [`Sub`] is implemented for any combination of [`MatQ`] and borrowed [`MatQ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract to `self`
    ///
    /// Returns the result of the subtraction as a [`MatQ`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a: MatQ = MatQ::from_str(&String::from("[[1/2, 2/3, 3/4],[3/4, 4/5, 5/7]]")).unwrap();
    /// let b: MatQ = MatQ::from_str(&String::from("[[1/4, 9/7, 3/7],[1, 0, 5]]")).unwrap();
    ///
    /// let c: MatQ = &a - &b;
    /// let d: MatQ = a - b;
    /// let e: MatQ = &c - d;
    /// let f: MatQ = c - &e;
    /// ```
    ///
    /// # Panics
    /// - Panics if the dimensions of both matrices mismatch
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
    }
}

impl MatQ {
    /// Implements subtraction for two [`MatQ`] matrixes.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract to `self`
    ///
    /// Returns the result of the subtraction as a [`MatQ`] or an
    /// error if the matrix dimensions do mismatch.
    ///
    /// # Example
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a: MatQ = MatQ::from_str(&String::from("[[1/2, 2/3, 3/4],[3/4, 4/5, 5/7]]")).unwrap();
    /// let b: MatQ = MatQ::from_str(&String::from("[[1/4, 9/7, 3/7],[1, 0, 5]]")).unwrap();
    ///
    /// let c: MatQ = a.sub_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// Returns a [`MathError`] of type
    /// [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    /// mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<MatQ, MathError> {
        if self.get_num_rows() != other.get_num_rows()
            || self.get_num_columns() != other.get_num_columns()
        {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to subtract a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            )));
        }
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        unsafe {
            fmpq_mat_sub(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, MatQ, MatQ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, MatQ, MatQ, MatQ);

#[cfg(test)]
mod test_sub {

    use super::MatQ;
    use crate::rational::Q;
    use std::str::FromStr;

    /// testing subtraction for two [`MatQ`]
    #[test]
    fn sub() {
        let a: MatQ = MatQ::from_str(&String::from("[[1/2, 1, 2],[3/7, 4/7, -5]]")).unwrap();
        let b: MatQ = MatQ::from_str(&String::from("[[1/2, 2, 3/4],[3/7, -4/9, 5]]")).unwrap();
        let c: MatQ = a - b;
        assert_eq!(
            c,
            MatQ::from_str(&String::from("[[0, -1, 5/4],[0, 64/63, -10]]")).unwrap()
        );
    }

    /// testing subtraction for two borrowed [`MatQ`]
    #[test]
    fn sub_borrow() {
        let a: MatQ = MatQ::from_str(&String::from("[[1/2, 1, 2],[3/7, 4/7, -5]]")).unwrap();
        let b: MatQ = MatQ::from_str(&String::from("[[1/2, 2, 3/4],[3/7, -4/9, 5]]")).unwrap();
        let c: MatQ = &a - &b;
        assert_eq!(
            c,
            MatQ::from_str(&String::from("[[0, -1, 5/4],[0, 64/63, -10]]")).unwrap()
        );
    }

    /// testing subtraction for borrowed [`MatQ`] and [`MatQ`]
    #[test]
    fn sub_first_borrowed() {
        let a: MatQ = MatQ::from_str(&String::from("[[1/2, 1, 2],[3/7, 4/7, -5]]")).unwrap();
        let b: MatQ = MatQ::from_str(&String::from("[[1/2, 2, 3/4],[3/7, -4/9, 5]]")).unwrap();
        let c: MatQ = &a - b;
        assert_eq!(
            c,
            MatQ::from_str(&String::from("[[0, -1, 5/4],[0, 64/63, -10]]")).unwrap()
        );
    }

    /// testing subtraction for [`MatQ`] and borrowed [`MatQ`]
    #[test]
    fn sub_second_borrowed() {
        let a: MatQ = MatQ::from_str(&String::from("[[1/2, 1, 2],[3/7, 4/7, -5]]")).unwrap();
        let b: MatQ = MatQ::from_str(&String::from("[[1/2, 2, 3/4],[3/7, -4/9, 5]]")).unwrap();
        let c: MatQ = a - &b;
        assert_eq!(
            c,
            MatQ::from_str(&String::from("[[0, -1, 5/4],[0, 64/63, -10]]")).unwrap()
        );
    }

    /// testing subtraction for big numbers
    #[test]
    fn sub_large_numbers() {
        let a: MatQ = MatQ::from_str(&String::from(format!(
            "[[1, 2, {}],[3, -4, {}]]",
            i64::MIN,
            u64::MAX
        )))
        .unwrap();
        let b: MatQ = MatQ::from_str(&String::from(format!(
            "[[1, 1, {}],[3, 9, 1/{}]]",
            i64::MAX,
            i64::MAX
        )))
        .unwrap();
        let c: MatQ = a - &b;
        assert_eq!(
            c,
            MatQ::from_str(&String::from(format!(
                "[[0, 1, -{}],[0, -13, {}]]",
                u64::MAX,
                Q::from_str(format!("{}", u64::MAX).as_str()).unwrap()
                    - Q::from_str(format!("1/{}", i64::MAX).as_str()).unwrap()
            )))
            .unwrap()
        );
    }

    /// testing sub_safe
    #[test]
    fn sub_safe() {
        let a: MatQ = MatQ::from_str(&String::from("[[1/2, 1, 2],[3/7, 4/7, -5]]")).unwrap();
        let b: MatQ = MatQ::from_str(&String::from("[[1/2, 2, 3/4],[3/7, -4/9, 5]]")).unwrap();
        let c: MatQ = a.sub_safe(&b).unwrap();
        assert_eq!(
            c,
            MatQ::from_str(&String::from("[[0, -1, 5/4],[0, 64/63, -10]]")).unwrap()
        );
    }

    /// testing sub_safe throws error
    #[test]
    fn sub_safe_is_err() {
        let a: MatQ = MatQ::from_str(&String::from("[[1, 2],[3, 4]]")).unwrap();
        let b: MatQ = MatQ::from_str(&String::from("[[1, 2, 3],[3, -4, 5]]")).unwrap();
        let c: MatQ = MatQ::from_str(&String::from("[[1, 2, 3]]")).unwrap();
        assert!(a.sub_safe(&b).is_err());
        assert!(c.sub_safe(&b).is_err());
    }
}
