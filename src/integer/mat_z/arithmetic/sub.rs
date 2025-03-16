// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`MatZ`] values.

use super::super::MatZ;
use crate::error::MathError;
use crate::integer_mod_q::MatZq;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::MatrixDimensions;
use flint_sys::fmpz_mat::fmpz_mat_sub;
use flint_sys::fmpz_mod_mat::_fmpz_mod_mat_reduce;
use std::ops::Sub;

impl Sub for &MatZ {
    type Output = MatZ;
    /// Implements the [`Sub`] trait for two [`MatZ`] values.
    /// [`Sub`] is implemented for any combination of [`MatZ`] and borrowed [`MatZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from`self`
    ///
    /// Returns the result of the subtraction as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatZ = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
    /// let b: MatZ = MatZ::from_str("[[1, 9, 3],[1, 0, 5]]").unwrap();
    ///
    /// let c: MatZ = &a - &b;
    /// let d: MatZ = a - b;
    /// let e: MatZ = &c - d;
    /// let f: MatZ = c - &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
    }
}

impl Sub<&MatZq> for &MatZ {
    type Output = MatZq;

    /// Implements the [`Sub`] trait for a [`MatZ`] and a [`MatZq`] matrix.
    /// [`Sub`] is implemented for any combination of [`MatZ`] and [`MatZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from `self`.
    ///
    /// Returns the difference from `self` and `other` as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::MatZ, integer_mod_q::MatZq};
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
    /// let b = MatZq::from_str("[[1, 9, 3],[1, 0, 5]] mod 7").unwrap();
    ///
    /// let c = &a - &b;
    /// let d = a - b;
    /// let e = &c - d;
    /// let f = c - &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn sub(self, other: &MatZq) -> Self::Output {
        if self.get_num_rows() != other.get_num_rows()
            || self.get_num_columns() != other.get_num_columns()
        {
            panic!(
                "Tried to subtract a '{}x{}' matrix from a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            );
        }

        let mut out = MatZq::new(self.get_num_rows(), self.get_num_columns(), other.get_mod());
        unsafe {
            fmpz_mat_sub(&mut out.matrix.mat[0], &self.matrix, &other.matrix.mat[0]);
            _fmpz_mod_mat_reduce(&mut out.matrix);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, MatZ, MatZq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, MatZ, MatZq, MatZq);

impl MatZ {
    /// Implements subtraction for two [`MatZ`] matrices.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from`self`
    ///
    /// Returns the result of the subtraction as a [`MatZ`] or an
    /// error if the matrix dimensions mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatZ = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
    /// let b: MatZ = MatZ::from_str("[[1, 9, 3],[1, 0, 5]]").unwrap();
    ///
    /// let c: MatZ = a.sub_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// - Returns a [`MathError`] of type
    ///     [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    ///     mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<MatZ, MathError> {
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
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpz_mat_sub(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, MatZ, MatZ, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, MatZ, MatZ, MatZ);

#[cfg(test)]
mod test_sub {
    use super::MatZ;
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Testing subtraction for two [`MatZ`]
    #[test]
    fn sub() {
        let a: MatZ = MatZ::from_str("[[1, 1, 2],[3, 4, -5]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = a - b;
        assert_eq!(c, MatZ::from_str("[[0, -1, -1],[0, 8, -10]]").unwrap());
    }

    /// Testing subtraction for two borrowed [`MatZ`]
    #[test]
    fn sub_borrow() {
        let a: MatZ = MatZ::from_str("[[1, 1, 2],[3, 4, -5]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = &a - &b;
        assert_eq!(c, MatZ::from_str("[[0, -1, -1],[0, 8, -10]]").unwrap());
    }

    /// Testing subtraction for borrowed [`MatZ`] and [`MatZ`]
    #[test]
    fn sub_first_borrowed() {
        let a: MatZ = MatZ::from_str("[[1, 1, 2],[3, 4, -5]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = &a - b;
        assert_eq!(c, MatZ::from_str("[[0, -1, -1],[0, 8, -10]]").unwrap());
    }

    /// Testing subtraction for [`MatZ`] and borrowed [`MatZ`]
    #[test]
    fn sub_second_borrowed() {
        let a: MatZ = MatZ::from_str("[[1, 1, 2],[3, 4, -5]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = a - &b;
        assert_eq!(c, MatZ::from_str("[[0, -1, -1],[0, 8, -10]]").unwrap());
    }

    /// Testing subtraction for large numbers
    #[test]
    fn sub_large_numbers() {
        let a: MatZ =
            MatZ::from_str(&format!("[[1, 2, {}],[3, -4, {}]]", i64::MIN, u64::MAX)).unwrap();
        let b: MatZ =
            MatZ::from_str(&format!("[[1, 1, {}],[3, 9, {}]]", i64::MAX, i64::MAX)).unwrap();
        let c: MatZ = a - &b;
        assert_eq!(
            c,
            MatZ::from_str(&format!(
                "[[0, 1, -{}],[0, -13, {}]]",
                u64::MAX,
                (u64::MAX - 1) / 2 + 1
            ))
            .unwrap()
        );
    }

    /// Testing sub_safe
    #[test]
    fn sub_safe() {
        let a: MatZ = MatZ::from_str("[[1, 1, 2],[3, 4, -5]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = a.sub_safe(&b).unwrap();
        assert_eq!(c, MatZ::from_str("[[0, -1, -1],[0, 8, -10]]").unwrap());
    }

    /// Testing sub_safe throws error
    #[test]
    fn sub_safe_is_err() {
        let a: MatZ = MatZ::from_str("[[1, 2],[3, 4]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = MatZ::from_str("[[1, 2, 3]]").unwrap();
        assert!(a.sub_safe(&b).is_err());
        assert!(c.sub_safe(&b).is_err());
    }

    /// Ensures that subtraction between [`MatZ`] and [`MatZq`] works properly incl. reduction mod q
    /// and is available for any combination.
    #[test]
    fn sub_matzq() {
        let a = MatZ::from_str("[[1, 2],[3, 4]]").unwrap();
        let b = MatZq::from_str("[[5, 6],[2, 10]] mod 11").unwrap();
        let cmp = MatZq::from_str("[[7, 7],[1, 5]] mod 11").unwrap();

        let _ = &b - &a;
        let _ = &b - a.clone();
        let _ = b.clone() - &a;
        let _ = b.clone() - a.clone();
        let _ = &a - &b;
        let _ = &a - b.clone();
        let _ = a.clone() - &b;
        let res = a.clone() - b.clone();

        assert_eq!(cmp, res);
    }
}
