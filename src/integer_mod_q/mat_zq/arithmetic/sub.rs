// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`MatZq`] values.

use super::super::MatZq;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_sub;
use std::ops::Sub;

impl Sub for &MatZq {
    type Output = MatZq;
    /// Implements the [`Sub`] trait for two [`MatZq`] values.
    /// [`Sub`] is implemented for any combination of [`MatZq`] and borrowed [`MatZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract to `self`
    ///
    /// Returns the result of the subtraction as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
    /// let b: MatZq = MatZq::from_str("[[1, 9, 3],[1, 0, 5]] mod 7").unwrap();
    ///
    /// let c: MatZq = &a - &b;
    /// let d: MatZq = a - b;
    /// let e: MatZq = &c - d;
    /// let f: MatZq = c - &e;
    /// ```
    ///
    /// # Panics
    /// - ... if the dimensions of both matrices mismatch
    /// - ... if the moduli mismatch
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
    }
}

impl MatZq {
    /// Implements subtraction for two [`MatZq`] matrixes.
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract to `self`
    ///
    /// Returns the result of the subtraction as a [`MatZq`] or an
    /// error if the matrix dimensions mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
    /// let b: MatZq = MatZq::from_str("[[1, 9, 3],[1, 0, 5]] mod 7").unwrap();
    ///
    /// let c: MatZq = a.sub_safe(&b).unwrap();
    /// ```
    /// # Errors and Failures
    /// Returns a [`MathError`] of type
    /// [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    /// mismatch.
    /// Returns a [`MathError`] of type
    /// [`MathError::MismatchingModulus`] if the moduli mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<MatZq, MathError> {
        if self.get_mod() != other.get_mod() {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to add matrixes with moduli '{}' and '{}'.",
                self.get_mod(),
                other.get_mod()
            )));
        }
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
        let mut out =
            MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod()).unwrap();
        unsafe {
            fmpz_mod_mat_sub(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, MatZq, MatZq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, MatZq, MatZq, MatZq);

#[cfg(test)]
mod test_sub {

    use super::MatZq;
    use std::str::FromStr;

    /// testing subtraction for two [`MatZq`]
    #[test]
    fn sub() {
        let a: MatZq = MatZq::from_str("[[1, 1, 2],[3, 4, -5]] mod 3").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -4, 5]] mod 3").unwrap();
        let c: MatZq = a - b;
        assert_eq!(c, MatZq::from_str("[[0, -1, -1],[0, 8, 2]] mod 3").unwrap());
    }

    /// testing subtraction for two borrowed [`MatZq`]
    #[test]
    fn sub_borrow() {
        let a: MatZq = MatZq::from_str("[[1, 1, 2],[3, 4, -5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -4, 5]] mod 7").unwrap();
        let c: MatZq = &a - &b;
        assert_eq!(
            c,
            MatZq::from_str("[[0, -1, -1],[0, 8, -10]] mod 7").unwrap()
        );
    }

    /// testing subtraction for borrowed [`MatZq`] and [`MatZq`]
    #[test]
    fn sub_first_borrowed() {
        let a: MatZq = MatZq::from_str("[[1, 1, 2],[3, 4, -5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -4, 5]] mod 7").unwrap();
        let c: MatZq = &a - b;
        assert_eq!(
            c,
            MatZq::from_str("[[0, -1, -1],[0, 8, -10]] mod 7").unwrap()
        );
    }

    /// testing subtraction for [`MatZq`] and borrowed [`MatZq`]
    #[test]
    fn sub_second_borrowed() {
        let a: MatZq = MatZq::from_str("[[1, 1, 2],[3, 4, -5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -4, 5]] mod 7").unwrap();
        let c: MatZq = a - &b;
        assert_eq!(
            c,
            MatZq::from_str("[[0, -1, -1],[0, 8, -10]] mod 7").unwrap()
        );
    }

    /// testing subtraction for big numbers
    #[test]
    fn sub_large_numbers() {
        let a: MatZq = MatZq::from_str(&format!(
            "[[1, 2, {}],[3, -4, {}]] mod {}",
            i64::MIN,
            u64::MAX,
            u64::MAX - 58
        ))
        .unwrap();
        let b: MatZq = MatZq::from_str(&format!(
            "[[1, 1, {}],[3, 9, {}]] mod {}",
            i64::MAX,
            i64::MAX,
            u64::MAX - 58
        ))
        .unwrap();
        let c: MatZq = a - &b;
        assert_eq!(
            c,
            MatZq::from_str(&format!(
                "[[0, 1, -{}],[0, -13, {}]] mod {}",
                u64::MAX,
                (u64::MAX - 1) / 2 + 1,
                u64::MAX - 58
            ))
            .unwrap()
        );
    }

    /// testing sub_safe
    #[test]
    fn sub_safe() {
        let a: MatZq = MatZq::from_str("[[1, 1, 2],[3, 4, -5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -4, 5]] mod 7").unwrap();
        let c: MatZq = a.sub_safe(&b).unwrap();
        assert_eq!(c, MatZq::from_str("[[0, -1, -1],[0, 8, 4]] mod 7").unwrap());
    }

    /// testing sub_safe throws errors
    #[test]
    fn sub_safe_is_err() {
        let a: MatZq = MatZq::from_str("[[1, 2],[3, 4]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -4, 5]] mod 7").unwrap();
        let c: MatZq = MatZq::from_str("[[1, 2, 3]] mod 7").unwrap();
        let d: MatZq = MatZq::from_str("[[1, 2],[3, 4]] mod 3").unwrap();
        assert!(a.sub_safe(&b).is_err());
        assert!(c.sub_safe(&b).is_err());
        assert!(a.add_safe(&d).is_err())
    }
}
