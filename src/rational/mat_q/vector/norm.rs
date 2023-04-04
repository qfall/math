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
use flint_sys::{
    fmpq::{fmpq, fmpq_abs, fmpq_addmul, fmpq_cmp},
    fmpz::fmpz,
};

impl MatQ {
    /// Returns the squared Euclidean norm or 2-norm of the given (row or column) vector.
    ///
    /// # Example
    /// ```
    /// use math::rational::MatQ;
    /// use std::str::FromStr;
    /// # use math::rational::Q;
    ///
    /// let vec = MatQ::from_str("[[1],[2/1],[6/2]]").unwrap();
    ///
    /// let sqrd_2_norm = vec.norm_sqrd_eucl().unwrap();
    ///
    /// assert_eq!(Q::try_from((&14, &1)).unwrap(), sqrd_2_norm);
    /// ```
    ///
    /// Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    /// the given [`MatQ`] instance is not a (row or column) vector.
    pub fn norm_sqrd_eucl(&self) -> Result<Q, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("norm_sqrd_eucl"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        }

        // collect all entries in vector
        let entries = self.collect_entries();

        // sum squared entries in result
        let mut result = Q::default();
        for entry in entries {
            // sets result = result + entry * entry without cloned Q element
            unsafe { fmpq_addmul(&mut result.value, &entry, &entry) }
        }

        // TODO: Add sqrt function here
        Ok(result)
    }

    /// Returns the infinity norm or ∞-norm of the given (row or column) vector.
    ///
    /// # Example
    /// ```
    /// use math::rational::MatQ;
    /// use std::str::FromStr;
    /// # use math::rational::Q;
    ///
    /// let vec = MatQ::from_str("[[1/1],[2],[6/2]]").unwrap();
    ///
    /// let infty_norm = vec.norm_infty().unwrap();
    ///
    /// assert_eq!(Q::try_from((&3, &1)).unwrap(), infty_norm);
    /// ```
    ///
    /// Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    /// the given [`MatQ`] instance is not a (row or column) vector.
    pub fn norm_infty(&self) -> Result<Q, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("norm_infty"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        }

        // collect all entries in vector
        let entries = self.collect_entries();

        // find maximum of absolute fmpq entries
        let mut max = fmpq {
            num: fmpz(0),
            den: fmpz(1),
        };
        for entry in entries {
            // compute absolute value of fmpq entry
            let mut abs_entry = fmpq {
                num: fmpz(0),
                den: fmpz(1),
            };
            unsafe { fmpq_abs(&mut abs_entry, &entry) };
            // compare maximum to absolute value of entry and keep bigger one
            if unsafe { fmpq_cmp(&max, &abs_entry) } < 0 {
                max = abs_entry;
            }
        }

        // clone value and ensure that absolute maximum value is absolute
        let mut result = Q::default();
        unsafe { fmpq_abs(&mut result.value, &max) }

        Ok(result)
    }
}

#[cfg(test)]
mod test_norm_sqrd_eucl {
    use super::{MatQ, Q};
    use std::str::FromStr;

    /// Check whether the squared euclidean norm for row vectors
    /// with small entries is calculated correctly
    #[test]
    fn row_vector_small_entries() {
        let vec_1 = MatQ::from_str("[[1]]").unwrap();
        let vec_2 = MatQ::from_str("[[1,10/1,-1000/10]]").unwrap();
        let vec_3 = MatQ::from_str("[[1,10,100, 1000]]").unwrap();

        assert_eq!(
            vec_1.norm_sqrd_eucl().unwrap(),
            Q::try_from((&1, &1)).unwrap()
        );
        assert_eq!(
            vec_2.norm_sqrd_eucl().unwrap(),
            Q::try_from((&10101, &1)).unwrap()
        );
        assert_eq!(
            vec_3.norm_sqrd_eucl().unwrap(),
            Q::try_from((&1010101, &1)).unwrap()
        );
    }

    /// Check whether the squared euclidean norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec = MatQ::from_str(&format!("[[{}/1,{}/-1, 2/1]]", i64::MAX, i64::MIN)).unwrap();
        let max = Q::try_from((&i64::MAX, &1)).unwrap();
        let min = Q::try_from((&i64::MIN, &1)).unwrap();
        let cmp = &min * &min + &max * &max + Q::try_from((&4, &1)).unwrap();

        assert_eq!(vec.norm_sqrd_eucl().unwrap(), cmp);
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatQ::from_str("[[1],[-100/10],[100]]").unwrap();
        let vec_2 = MatQ::from_str("[[1],[-10/-1],[100],[1000]]").unwrap();

        assert_eq!(
            vec_1.norm_sqrd_eucl().unwrap(),
            Q::try_from((&10101, &1)).unwrap()
        );
        assert_eq!(
            vec_2.norm_sqrd_eucl().unwrap(),
            Q::try_from((&1010101, &1)).unwrap()
        );
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec = MatQ::from_str(&format!("[[{}/-1],[-1/{}],[2]]", i64::MAX, i64::MIN)).unwrap();
        let max = Q::try_from((&i64::MAX, &1)).unwrap();
        let min = Q::try_from((&1, &i64::MIN)).unwrap();
        let cmp = &min * &min + &max * &max + Q::try_from((&4, &1)).unwrap();

        assert_eq!(vec.norm_sqrd_eucl().unwrap(), cmp);
    }

    /// Check whether euclidean norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatQ::from_str("[[1,1/1],[10/-1,2]]").unwrap();

        assert!(mat.norm_sqrd_eucl().is_err());
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
        let vec_2 = MatQ::from_str("[[1,100/10,1000/-10]]").unwrap();
        let vec_3 = MatQ::from_str("[[1,-10/-1,-100/1, 1000]]").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Q::try_from((&1, &1)).unwrap());
        assert_eq!(
            vec_2.norm_infty().unwrap(),
            Q::try_from((&100, &1)).unwrap()
        );
        assert_eq!(
            vec_3.norm_infty().unwrap(),
            Q::try_from((&1000, &1)).unwrap()
        );
    }

    /// Check whether the infinity norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec = MatQ::from_str(&format!("[[{}/-1,{}/1, 2]]", i64::MAX, i64::MIN)).unwrap();
        let cmp = Q::try_from((&(-1), &1)).unwrap() * Q::try_from((&i64::MIN, &1)).unwrap();

        assert_eq!(vec.norm_infty().unwrap(), cmp);
    }

    /// Check whether the infinity norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatQ::from_str("[[1],[100/10],[100]]").unwrap();
        let vec_2 = MatQ::from_str("[[-1/1],[10/-1],[-100/-1],[1000]]").unwrap();

        assert_eq!(
            vec_1.norm_infty().unwrap(),
            Q::try_from((&100, &1)).unwrap()
        );
        assert_eq!(
            vec_2.norm_infty().unwrap(),
            Q::try_from((&1000, &1)).unwrap()
        );
    }

    /// Check whether the infinity norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec = MatQ::from_str(&format!("[[{}/1],[{}],[2]]", i64::MAX, i64::MIN)).unwrap();
        let cmp = Q::try_from((&-1, &1)).unwrap() * Q::try_from((&i64::MIN, &1)).unwrap();

        assert_eq!(vec.norm_infty().unwrap(), cmp);
    }

    /// Check whether infinity norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatQ::from_str("[[1,1],[10/1,2]]").unwrap();

        assert!(mat.norm_infty().is_err());
    }
}
