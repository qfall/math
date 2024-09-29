// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute several norms
//! defined on vectors.

use super::super::MatQ;
use crate::{
    error::MathError,
    rational::Q,
    traits::{GetNumColumns, GetNumRows},
};
use flint_sys::fmpq::{fmpq_abs, fmpq_addmul, fmpq_cmp};

impl MatQ {
    /// Returns the squared Euclidean norm or 2-norm of the given (row or column) vector
    /// or an error if the given [`MatQ`] instance is not a (row or column) vector.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{MatQ, Q};
    /// use std::str::FromStr;
    ///
    /// let vec = MatQ::from_str("[[1],[2/1],[6/2]]").unwrap();
    ///
    /// let sqrd_2_norm = vec.norm_eucl_sqrd().unwrap();
    ///
    /// // 1*1 + 2*2 + 3*3 = 14
    /// assert_eq!(Q::from(14), sqrd_2_norm);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    ///     the given [`MatQ`] instance is not a (row or column) vector.
    pub fn norm_eucl_sqrd(&self) -> Result<Q, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("norm_eucl_sqrd"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        }

        let entries = self.collect_entries();

        // sum squared entries in result
        let mut result = Q::default();
        for entry in entries {
            // sets result = result + entry * entry without cloned Q element
            unsafe { fmpq_addmul(&mut result.value, &entry, &entry) }
        }

        Ok(result)
    }

    /// Returns the infinity norm or ∞-norm of the given (row or column) vector.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{MatQ, Q};
    /// use std::str::FromStr;
    ///
    /// let vec = MatQ::from_str("[[1/1],[2],[6/2]]").unwrap();
    ///
    /// let infty_norm = vec.norm_infty().unwrap();
    ///
    /// // max { 1, 2, 3 } = 3
    /// assert_eq!(Q::from(3), infty_norm);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    ///     the given [`MatQ`] instance is not a (row or column) vector.
    pub fn norm_infty(&self) -> Result<Q, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("norm_infty"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        }

        let entries = self.collect_entries();

        // find maximum of absolute fmpq entries
        let mut max = Q::ZERO;
        for entry in entries {
            // compute absolute value of fmpq entry
            let mut abs_entry = Q::default();
            unsafe { fmpq_abs(&mut abs_entry.value, &entry) };
            // compare maximum to absolute value of entry and keep larger one
            if unsafe { fmpq_cmp(&max.value, &abs_entry.value) } < 0 {
                max = abs_entry;
            }
        }

        Ok(max)
    }
}

#[cfg(test)]
mod test_norm_eucl_sqrd {
    use super::{MatQ, Q};
    use std::str::FromStr;

    /// Check whether the squared euclidean norm for row vectors
    /// with small entries is calculated correctly
    #[test]
    fn row_vector_small_entries() {
        let vec_1 = MatQ::from_str("[[1]]").unwrap();
        let vec_2 = MatQ::from_str("[[1, 10/1, -1000/10]]").unwrap();
        let vec_3 = MatQ::from_str("[[1, 10, 100, 1000]]").unwrap();

        assert_eq!(vec_1.norm_eucl_sqrd().unwrap(), Q::ONE);
        assert_eq!(vec_2.norm_eucl_sqrd().unwrap(), Q::from(10101));
        assert_eq!(vec_3.norm_eucl_sqrd().unwrap(), Q::from(1010101));
    }

    /// Check whether the squared euclidean norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec = MatQ::from_str(&format!("[[{}/1, {}/-1, 2/1]]", i64::MAX, i64::MIN)).unwrap();
        let max = Q::from(i64::MAX);
        let min = Q::from(i64::MIN);
        let cmp = &min * &min + &max * &max + Q::from(4);

        assert_eq!(vec.norm_eucl_sqrd().unwrap(), cmp);
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatQ::from_str("[[1],[-100/10],[100]]").unwrap();
        let vec_2 = MatQ::from_str("[[1],[-10/-1],[100],[1000]]").unwrap();

        assert_eq!(vec_1.norm_eucl_sqrd().unwrap(), Q::from(10101));
        assert_eq!(vec_2.norm_eucl_sqrd().unwrap(), Q::from(1010101));
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec = MatQ::from_str(&format!("[[{}/-1],[-1/{}],[2]]", i64::MAX, i64::MIN)).unwrap();
        let max = Q::from(i64::MAX);
        let min = Q::from((1, i64::MIN));
        let cmp = &min * &min + &max * &max + Q::from(4);

        assert_eq!(vec.norm_eucl_sqrd().unwrap(), cmp);
    }

    /// Check whether euclidean norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatQ::from_str("[[1, 1/1],[10/-1, 2]]").unwrap();

        assert!(mat.norm_eucl_sqrd().is_err());
    }
}

#[cfg(test)]
mod test_norm_infty {
    use super::{MatQ, Q};
    use std::str::FromStr;

    /// Check whether the infinity norm for row vectors
    /// with small entries is calculated correctly
    #[test]
    fn row_vector_small_entries() {
        let vec_1 = MatQ::from_str("[[1]]").unwrap();
        let vec_2 = MatQ::from_str("[[1, 100/10, 1000/-10]]").unwrap();
        let vec_3 = MatQ::from_str("[[1, -10/-1, -100/1, 1000]]").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Q::ONE);
        assert_eq!(vec_2.norm_infty().unwrap(), Q::from(100));
        assert_eq!(vec_3.norm_infty().unwrap(), Q::from(1000));
    }

    /// Check whether the infinity norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec = MatQ::from_str(&format!("[[{}/-1, {}/1, 2]]", i64::MAX, i64::MIN)).unwrap();
        let cmp = -1 * Q::from(i64::MIN);

        assert_eq!(vec.norm_infty().unwrap(), cmp);
    }

    /// Check whether the infinity norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatQ::from_str("[[1],[100/10],[100]]").unwrap();
        let vec_2 = MatQ::from_str("[[-1/1],[10/-1],[-100/-1],[1000]]").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Q::from(100));
        assert_eq!(vec_2.norm_infty().unwrap(), Q::from(1000));
    }

    /// Check whether the infinity norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec = MatQ::from_str(&format!("[[{}/1],[{}],[2]]", i64::MAX, i64::MIN)).unwrap();
        let cmp = Q::from(-1) * Q::from(i64::MIN);

        assert_eq!(vec.norm_infty().unwrap(), cmp);
    }

    /// Check whether infinity norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatQ::from_str("[[1, 1],[10/1, 2]]").unwrap();

        assert!(mat.norm_infty().is_err());
    }
}
