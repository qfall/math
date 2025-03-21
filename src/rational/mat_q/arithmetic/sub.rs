// Copyright © 2023 Phil Milewski, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`MatQ`] values.

use super::super::MatQ;
use crate::error::MathError;
use crate::integer::MatZ;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::MatrixDimensions;
use flint_sys::fmpq_mat::fmpq_mat_sub;
use std::ops::Sub;

impl Sub for &MatQ {
    type Output = MatQ;
    /// Implements the [`Sub`] trait for two matrices.
    /// [`Sub`] is implemented for any combination of [`MatQ`] and borrowed [`MatQ`].
    /// Furthermore, it is available for any combination of [`MatZ`] and [`MatQ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the result of the subtraction as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{rational::MatQ, integer::MatZ};
    /// use std::str::FromStr;
    ///
    /// let a: MatQ = MatQ::from_str("[[1/2, 2/3, 3/4],[3/4, 4/5, 5/7]]").unwrap();
    /// let b: MatQ = MatQ::from_str("[[1/4, 9/7, 3/7],[1, 0, 5]]").unwrap();
    /// let c: MatZ = MatZ::identity(2, 3);
    ///
    /// let d: MatQ = &a - &b;
    /// let e: MatQ = a - b;
    /// let f: MatQ = &d - e;
    /// let g: MatQ = d - &f;
    /// let h: MatQ = &f - &c;
    /// let i: MatQ = f - c;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
    }
}

impl Sub<&MatZ> for &MatQ {
    type Output = MatQ;

    /// Implements the [`Sub`] trait for a [`MatQ`] and a [`MatZ`] matrix.
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the matrix to subtract from `self`.
    ///
    /// Returns the subtraction of `self` and `other` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::MatZ, rational::MatQ};
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
    /// let b = MatQ::from_str("[[1/2, 9, 3/8],[1/7, 0, 5]]").unwrap();
    ///
    /// let c = &b - &a;
    /// let d = b.clone() - a.clone();
    /// let e = &b - &a;
    /// let f = b - a;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn sub(self, other: &MatZ) -> Self::Output {
        let other = MatQ::from(other);

        self.sub_safe(&other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, MatQ, MatZ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, MatQ, MatZ, MatQ);

impl MatQ {
    /// Implements subtraction for two [`MatQ`] matrices.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from`self`
    ///
    /// Returns the result of the subtraction as a [`MatQ`] or an
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
    /// let c: MatQ = a.sub_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// - Returns a [`MathError`] of type
    ///   [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    ///   mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<MatQ, MathError> {
        if self.get_num_rows() != other.get_num_rows()
            || self.get_num_columns() != other.get_num_columns()
        {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to subtract a '{}x{}' matrix and a '{}x{}' matrix.",
                other.get_num_rows(),
                other.get_num_columns(),
                self.get_num_rows(),
                self.get_num_columns()
            )));
        }
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns());
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
    use crate::{integer::MatZ, rational::Q};
    use std::str::FromStr;

    /// Testing subtraction for two [`MatQ`]
    #[test]
    fn sub() {
        let a: MatQ = MatQ::from_str("[[1/2, 1, 2],[3/7, 4/7, -5]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/4],[3/7, -4/9, 5]]").unwrap();
        let c: MatQ = a - b;
        assert_eq!(c, MatQ::from_str("[[0, -1, 5/4],[0, 64/63, -10]]").unwrap());
    }

    /// Testing subtraction for two borrowed [`MatQ`]
    #[test]
    fn sub_borrow() {
        let a: MatQ = MatQ::from_str("[[1/2, 1, 2],[3/7, 4/7, -5]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/4],[3/7, -4/9, 5]]").unwrap();
        let c: MatQ = &a - &b;
        assert_eq!(c, MatQ::from_str("[[0, -1, 5/4],[0, 64/63, -10]]").unwrap());
    }

    /// Testing subtraction for borrowed [`MatQ`] and [`MatQ`]
    #[test]
    fn sub_first_borrowed() {
        let a: MatQ = MatQ::from_str("[[1/2, 1, 2],[3/7, 4/7, -5]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/4],[3/7, -4/9, 5]]").unwrap();
        let c: MatQ = &a - b;
        assert_eq!(c, MatQ::from_str("[[0, -1, 5/4],[0, 64/63, -10]]").unwrap());
    }

    /// Testing subtraction for [`MatQ`] and borrowed [`MatQ`]
    #[test]
    fn sub_second_borrowed() {
        let a: MatQ = MatQ::from_str("[[1/2, 1, 2],[3/7, 4/7, -5]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/4],[3/7, -4/9, 5]]").unwrap();
        let c: MatQ = a - &b;
        assert_eq!(c, MatQ::from_str("[[0, -1, 5/4],[0, 64/63, -10]]").unwrap());
    }

    /// Testing subtraction for large numbers
    #[test]
    fn sub_large_numbers() {
        let a: MatQ =
            MatQ::from_str(&format!("[[1, 2, {}],[3, -4, {}]]", i64::MIN, u64::MAX)).unwrap();
        let b: MatQ =
            MatQ::from_str(&format!("[[1, 1, {}],[3, 9, 1/{}]]", i64::MAX, i64::MAX)).unwrap();
        let c: MatQ = a - &b;
        assert_eq!(
            c,
            MatQ::from_str(&format!(
                "[[0, 1, -{}],[0, -13, {}]]",
                u64::MAX,
                Q::from(u64::MAX) - Q::from((1, i64::MAX))
            ))
            .unwrap()
        );
    }

    /// Testing sub_safe
    #[test]
    fn sub_safe() {
        let a: MatQ = MatQ::from_str("[[1/2, 1, 2],[3/7, 4/7, -5]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/4],[3/7, -4/9, 5]]").unwrap();
        let c: MatQ = a.sub_safe(&b).unwrap();
        assert_eq!(c, MatQ::from_str("[[0, -1, 5/4],[0, 64/63, -10]]").unwrap());
    }

    /// Testing sub_safe throws error
    #[test]
    fn sub_safe_is_err() {
        let a: MatQ = MatQ::from_str("[[1, 2],[3, 4]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatQ = MatQ::from_str("[[1, 2, 3]]").unwrap();
        assert!(a.sub_safe(&b).is_err());
        assert!(c.sub_safe(&b).is_err());
    }

    /// Ensure that `sub` is available for all types between [`MatZ`] and [`MatQ`].
    #[test]
    fn availability() {
        let a = MatQ::new(2, 2);
        let b = MatZ::new(2, 2);
        let c = MatQ::new(2, 2);

        let _ = &a - &b;
        let _ = &a - b.clone();
        let _ = a.clone() - &b;
        let _ = a.clone() - b.clone();
        let _ = &b - &a;
        let _ = &b - a.clone();
        let _ = b.clone() - &a;
        let _ = b.clone() - a.clone();

        let _ = &a - &c;
        let _ = &a - c.clone();
        let _ = a.clone() - &c;
        let _ = a.clone() - c.clone();
        let _ = &c - &a;
        let _ = &c - a.clone();
        let _ = c.clone() - &a;
        let _ = c.clone() - a.clone();
    }
}

#[cfg(test)]
mod test_sub_matz {
    use super::MatZ;
    use crate::rational::{MatQ, Q};
    use std::str::FromStr;

    /// Ensures that subtraction between [`MatZ`] and [`MatQ`] works properly incl..
    #[test]
    fn small_numbers() {
        let a = MatZ::from_str("[[1, 2],[3, 4]]").unwrap();
        let b = MatQ::from_str("[[5, 1/2],[2, 10]]").unwrap();
        let cmp = MatQ::from_str("[[4, -3/2],[-1, 6]]").unwrap();

        let res = &b - &a;

        assert_eq!(res, cmp);
    }

    /// Testing subtraction for large numbers.
    #[test]
    fn large_numbers() {
        let a: MatZ = MatZ::from_str(&format!("[[1, 1, {}],[3, 9, 4]]", i64::MIN)).unwrap();
        let b = MatQ::from_str(&format!("[[1, 2, 1/{}],[3, -4, 5]]", i64::MAX)).unwrap();

        let c = &b - a;

        assert_eq!(
            c,
            MatQ::from_str(&format!(
                "[[0, 1, {}],[0, -13, 1]]",
                Q::from((1, i64::MAX)) - Q::from((i64::MIN, 1))
            ))
            .unwrap()
        );
    }

    /// Ensures that subtraction between [`MatZ`] and [`MatQ`] is available for any combination.
    #[test]
    fn available() {
        let a = MatZ::new(2, 2);
        let b = MatQ::new(2, 2);

        let _ = &b - &a;
        let _ = &b - a.clone();
        let _ = b.clone() - &a;
        let _ = b.clone() - a.clone();
    }

    /// Ensures that mismatching rows results in a panic.
    #[test]
    #[should_panic]
    fn mismatching_rows() {
        let a = MatZ::new(3, 2);
        let b = MatQ::new(2, 2);

        let _ = &b - &a;
    }

    /// Ensures that mismatching columns results in a panic.
    #[test]
    #[should_panic]
    fn mismatching_column() {
        let a = MatZ::new(2, 3);
        let b = MatQ::new(2, 2);

        let _ = &b - &a;
    }
}
