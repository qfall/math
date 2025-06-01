// Copyright © 2023 Phil Milewski, Marcel Luca Schmidt
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
    arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
    arithmetic_trait_mixed_borrowed_owned,
};
use crate::rational::MatQ;
use crate::traits::MatrixDimensions;
use flint_sys::fmpz_mat::fmpz_mat_sub;
use flint_sys::fmpz_mod_mat::_fmpz_mod_mat_reduce;
use std::ops::{Sub, SubAssign};

impl SubAssign<&MatZ> for MatZ {
    /// Computes the subtraction of `self` and `other` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from `self`
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// let mut a = MatZ::identity(2, 2);
    /// let b = MatZ::new(2, 2);
    ///
    /// a -= &b;
    /// a -= b;
    /// ```
    ///
    /// # Panics ...
    /// - if the matrix dimensions mismatch.
    fn sub_assign(&mut self, other: &Self) {
        if self.get_num_rows() != other.get_num_rows()
            || self.get_num_columns() != other.get_num_columns()
        {
            panic!(
                "Tried to subtract a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            );
        }

        unsafe { fmpz_mat_sub(&mut self.matrix, &self.matrix, &other.matrix) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(SubAssign, sub_assign, MatZ, MatZ);

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

arithmetic_trait_borrowed_to_owned!(Sub, sub, MatZ, MatZ, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, MatZ, MatZ, MatZ);

impl Sub<&MatZq> for &MatZ {
    type Output = MatZq;

    /// Implements the [`Sub`] trait for a [`MatZ`] and a [`MatZq`] matrix.
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the matrix to subtract from `self`.
    ///
    /// Returns the subtraction of `self` and `other` as a [`MatZq`].
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
    /// let d = a.clone() - b.clone();
    /// let e = &a - &b;
    /// let f = a - b;
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
                other.get_num_rows(),
                other.get_num_columns(),
                self.get_num_rows(),
                self.get_num_columns()
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

impl Sub<&MatQ> for &MatZ {
    type Output = MatQ;

    /// Implements the [`Sub`] trait for a [`MatZ`] and a [`MatQ`] matrix.
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
    /// let a = MatQ::from_str("[[1/2, 9, 3/8],[1/7, 0, 5]]").unwrap();
    /// let b = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
    ///
    /// let c = &b - &a;
    /// let d = b.clone() - a.clone();
    /// let e = &b - &a;
    /// let f = b - a;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn sub(self, other: &MatQ) -> Self::Output {
        let new_self = MatQ::from(self);

        new_self.sub_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, MatZ, MatQ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, MatZ, MatQ, MatQ);

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
    ///   [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    ///   mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<MatZ, MathError> {
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
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpz_mat_sub(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_sub_assign {
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensure that `sub_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = MatZ::identity(2, 2);
        let b = MatZ::from_str("[[-4, -5],[6, 1]]").unwrap();
        let cmp = MatZ::from_str("[[5, 5],[-6, 0]]").unwrap();

        a -= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `sub_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = MatZ::from_str(&format!("[[{}, 5],[{}, -1]]", i64::MAX, i64::MIN)).unwrap();
        let b = MatZ::from_str(&format!("[[-{}, 6],[-6, 1]]", i64::MAX)).unwrap();
        let cmp = MatZ::from_str(&format!(
            "[[{}, -1],[{}, -2]]",
            2 * (i64::MAX as u64),
            i64::MIN + 6
        ))
        .unwrap();

        a -= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `sub_assign` works for different matrix dimensions.
    #[test]
    fn matrix_dimensions() {
        let dimensions = [(3, 3), (5, 1), (1, 4)];

        for (nr_rows, nr_cols) in dimensions {
            let mut a = MatZ::identity(nr_rows, nr_cols);
            let b = MatZ::new(nr_rows, nr_cols);

            a -= b;

            assert_eq!(MatZ::identity(nr_rows, nr_cols), a);
        }
    }

    /// Ensure that `sub_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = MatZ::new(2, 2);
        let b = MatZ::new(2, 2);

        a -= &b;
        a -= b;
    }
}

#[cfg(test)]
mod test_sub {
    use super::MatZ;
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
}

#[cfg(test)]
mod test_sub_matzq {
    use super::MatZ;
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Ensures that subtraction between [`MatZ`] and [`MatZq`] works properly incl. reduction mod q.
    #[test]
    fn small_numbers() {
        let a = MatZ::from_str("[[1, 2],[3, 4]]").unwrap();
        let b = MatZq::from_str("[[5, 6],[2, 10]] mod 11").unwrap();
        let cmp = MatZq::from_str("[[7, 7],[1, 5]] mod 11").unwrap();

        let res_0 = &a - &b;
        let res_1 = MatZq::from((a, 11)) - b.get_representative_least_nonnegative_residue();

        assert_eq!(res_0, res_1);
        assert_eq!(cmp, res_0);
    }

    /// Testing subtraction for large numbers
    #[test]
    fn large_numbers() {
        let a: MatZ =
            MatZ::from_str(&format!("[[1, 2, {}],[3, -4, {}]]", i64::MIN, u64::MAX)).unwrap();
        let b: MatZq = MatZq::from_str(&format!(
            "[[1, 1, {}],[3, 9, {}]] mod {}",
            i64::MAX,
            i64::MAX,
            u64::MAX - 58
        ))
        .unwrap();

        let c = a - &b;

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

    /// Ensures that subtraction between [`MatZ`] and [`MatZq`] is available for any combination.
    #[test]
    fn available() {
        let a = MatZ::new(2, 2);
        let b = MatZq::new(2, 2, 7);

        let _ = &a - &b;
        let _ = &a - b.clone();
        let _ = a.clone() - &b;
        let _ = a.clone() - b.clone();
    }

    /// Ensures that mismatching rows results in a panic.
    #[test]
    #[should_panic]
    fn mismatching_rows() {
        let a = MatZ::new(3, 2);
        let b = MatZq::new(2, 2, 7);

        let _ = &a - &b;
    }

    /// Ensures that mismatching columns results in a panic.
    #[test]
    #[should_panic]
    fn mismatching_column() {
        let a = MatZ::new(2, 3);
        let b = MatZq::new(2, 2, 7);

        let _ = &a - &b;
    }
}

#[cfg(test)]
mod test_sub_matq {
    use super::MatZ;
    use crate::rational::{MatQ, Q};
    use std::str::FromStr;

    /// Ensures that subtraction between [`MatZ`] and [`MatQ`] works properly.
    #[test]
    fn small_numbers() {
        let a = MatQ::from_str("[[5, 1/2],[2, 10]]").unwrap();
        let b = MatZ::from_str("[[1, 2],[3, 4]]").unwrap();
        let cmp = MatQ::from_str("[[-4, 3/2],[1, -6]]").unwrap();

        let res = &b - &a;

        assert_eq!(res, cmp);
    }

    /// Testing subtraction for large numbers.
    #[test]
    fn large_numbers() {
        let a = MatQ::from_str(&format!("[[1, 2, 1/{}],[3, -4, 5]]", i64::MAX)).unwrap();
        let b: MatZ = MatZ::from_str(&format!("[[1, 1, {}],[3, 9, 4]]", i64::MIN)).unwrap();

        let c = &b - a;

        assert_eq!(
            c,
            MatQ::from_str(&format!(
                "[[0, -1, -{}],[0, 13, -1]]",
                Q::from((1, i64::MAX)) - Q::from((i64::MIN, 1))
            ))
            .unwrap()
        );
    }

    /// Ensures that subtraction between [`MatZ`] and [`MatQ`] is available for any combination.
    #[test]
    fn available() {
        let a = MatQ::new(2, 2);
        let b = MatZ::new(2, 2);

        let _ = &b - &a;
        let _ = &b - a.clone();
        let _ = b.clone() - &a;
        let _ = b.clone() - a.clone();
    }

    /// Ensures that mismatching rows results in a panic.
    #[test]
    #[should_panic]
    fn mismatching_rows() {
        let a = MatQ::new(2, 2);
        let b = MatZ::new(3, 2);

        let _ = &b - &a;
    }

    /// Ensures that mismatching columns results in a panic.
    #[test]
    #[should_panic]
    fn mismatching_column() {
        let a = MatQ::new(2, 2);
        let b = MatZ::new(2, 3);

        let _ = &b - &a;
    }
}
