// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`MatQ`] values.

use super::super::MatQ;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpq_mat::fmpq_mat_add;
use std::ops::Add;

impl Add for &MatQ {
    type Output = MatQ;
    /// Implements the [`Add`] trait for two [`MatQ`] values.
    /// [`Add`] is implemented for any combination of [`MatQ`] and borrowed [`MatQ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a: MatQ = MatQ::from_str("[[1/2, 2/3, 3/4],[3/4, 4/5, 5/7]]").unwrap();
    /// let b: MatQ = MatQ::from_str("[[1/4, 9/7, 3/7],[1, 0, 5]]").unwrap();
    ///
    /// let c: MatQ = &a + &b;
    /// let d: MatQ = a + b;
    /// let e: MatQ = &c + d;
    /// let f: MatQ = c + &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

impl MatQ {
    /// Implements addition for two [`MatQ`] matrices.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both matrices as a [`MatQ`] or an
    /// error if the matrix dimensions mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a: MatQ = MatQ::from_str("[[1/2, 2/3, 3/4],[3/4, 4/5, 5/7]]").unwrap();
    /// let b: MatQ = MatQ::from_str("[[1/4, 9/7, 3/7],[1, 0, 5]]").unwrap();
    ///
    /// let c: MatQ = a.add_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// Returns a [`MathError`] of type
    /// [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    /// mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<MatQ, MathError> {
        if self.get_num_rows() != other.get_num_rows()
            || self.get_num_columns() != other.get_num_columns()
        {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to add a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            )));
        }
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpq_mat_add(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, MatQ, MatQ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatQ, MatQ, MatQ);

#[cfg(test)]
mod test_add {
    use super::MatQ;
    use crate::rational::Q;
    use std::str::FromStr;

    /// Testing addition for two [`MatQ`]
    #[test]
    fn add() {
        let a: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, 4/7, 5/7]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, -4/7, 5/7]]").unwrap();
        let c: MatQ = a + b;
        assert_eq!(c, MatQ::from_str("[[1, 4, 3],[6/7, 0, 10/7]]").unwrap());
    }

    /// Testing addition for two borrowed [`MatQ`]
    #[test]
    fn add_borrow() {
        let a: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, 4/7, 5/7]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, -4/7, 5/7]]").unwrap();
        let c: MatQ = &a + &b;
        assert_eq!(c, MatQ::from_str("[[1, 4, 3],[6/7, 0, 10/7]]").unwrap());
    }

    /// Testing addition for borrowed [`MatQ`] and [`MatQ`]
    #[test]
    fn add_first_borrowed() {
        let a: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, 4/7, 5/7]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, -4/7, 5/7]]").unwrap();
        let c: MatQ = &a + b;
        assert_eq!(c, MatQ::from_str("[[1, 4, 3],[6/7, 0, 10/7]]").unwrap());
    }

    /// Testing addition for [`MatQ`] and borrowed [`MatQ`]
    #[test]
    fn add_second_borrowed() {
        let a: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, 4/7, 5/7]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, -4/7, 5/7]]").unwrap();
        let c: MatQ = a + &b;
        assert_eq!(c, MatQ::from_str("[[1, 4, 3],[6/7, 0, 10/7]]").unwrap());
    }

    /// Testing addition for large numbers
    #[test]
    fn add_large_numbers() {
        let a: MatQ =
            MatQ::from_str(&format!("[[1, 2, {}],[3, -4, {}]]", i64::MIN, i64::MAX)).unwrap();
        let b: MatQ = MatQ::from_str(&format!(
            "[[1, 2, {}],[3, 9, 1/{}]]",
            i64::MIN + 1,
            i64::MAX
        ))
        .unwrap();
        let c: MatQ = a + &b;
        assert_eq!(
            c,
            MatQ::from_str(&format!(
                "[[2, 4, -{}],[6, 5, {}]]",
                u64::MAX,
                Q::from(i64::MAX) + Q::from((1, i64::MAX))
            ))
            .unwrap()
        );
    }

    /// Testing add_safe
    #[test]
    fn add_safe() {
        let a: MatQ = MatQ::from_str("[[1/9, 2/8, 3/4],[3, 4, 5]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/9, 2/8, 3/4],[3, -4, 5]]").unwrap();
        let c = a.add_safe(&b);
        assert_eq!(
            c.unwrap(),
            MatQ::from_str("[[2/9, 4/8, 6/4],[6, 0, 10]]").unwrap()
        );
    }

    /// Testing add_safe throws error
    #[test]
    fn add_safe_is_err() {
        let a: MatQ = MatQ::from_str("[[1, 2/7],[3/1912, 4]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1, 5/2, 0],[3, -4/6, 7/5]]").unwrap();
        let c: MatQ = MatQ::from_str("[[1, -2/9, 3/7]]").unwrap();
        assert!(a.add_safe(&b).is_err());
        assert!(c.add_safe(&b).is_err());
    }
}
