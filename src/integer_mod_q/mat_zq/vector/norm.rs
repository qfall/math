// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute several norms
//! defined on vectors.

use super::super::MatZq;
use crate::{
    error::MathError,
    integer::Z,
    integer_mod_q::fmpz_mod_helpers::length,
    traits::{GetNumColumns, GetNumRows},
};
use flint_sys::fmpz::fmpz_addmul;

impl MatZq {
    /// Returns the squared Euclidean norm or 2-norm of the given (row or column) vector.
    ///
    /// Each length of an entry is defined as the shortest distance
    /// to the next zero instance in the ring.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{
    ///     integer::Z,
    ///     integer_mod_q::MatZq,
    /// };
    /// use std::str::FromStr;
    ///
    /// let vec = MatZq::from_str("[[1],[2],[3]] mod 4").unwrap();
    ///
    /// let sqrd_2_norm = vec.norm_eucl_sqrd().unwrap();
    ///
    /// // 1*1 + 2*2 + 1*1 = 6
    /// assert_eq!(Z::from(6), sqrd_2_norm);
    /// ```
    ///
    /// Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    /// the given [`MatZq`] instance is not a (row or column) vector.
    pub fn norm_eucl_sqrd(&self) -> Result<Z, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("norm_eucl_sqrd"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        }

        // compute lengths of all entries in matrix with regards to modulus
        let entry_lengths = self.collect_lengths();

        // sum squared entries in result
        let mut result = Z::ZERO;
        for entry in entry_lengths {
            // sets result = result + entry * entry without cloned Z element
            unsafe { fmpz_addmul(&mut result.value, &entry.value, &entry.value) }
        }

        Ok(result)
    }

    /// Returns the infinity norm or ∞-norm of the given (row or column) vector.
    ///
    /// Each length of an entry is defined as the shortest distance
    /// to the next zero instance in the ring.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{
    ///     integer::Z,
    ///     integer_mod_q::MatZq,
    /// };
    /// use std::str::FromStr;
    ///
    /// let vec = MatZq::from_str("[[1],[2],[3]] mod 3").unwrap();
    ///
    /// let infty_norm = vec.norm_infty().unwrap();
    ///
    /// // max{1, 1, 0} = 1
    /// assert_eq!(Z::ONE, infty_norm);
    /// ```
    ///
    /// Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    /// the given [`MatZq`] instance is not a (row or column) vector.
    pub fn norm_infty(&self) -> Result<Z, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("norm_infty"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        }

        let fmpz_entries = self.collect_entries();

        // compute lengths of all entries in matrix with regards to modulus
        // and find maximum length
        let modulus = self.matrix.mod_[0];
        let mut max = Z::ZERO;
        for fmpz_entry in fmpz_entries {
            let length = length(&fmpz_entry, &modulus);
            if length > max {
                max = length;
            }
        }

        Ok(max)
    }
}

#[cfg(test)]
mod test_norm_eucl_sqrd {
    use super::{MatZq, Z};
    use std::str::FromStr;

    /// Check whether the squared euclidean norm for row vectors
    /// with small entries is calculated correctly
    #[test]
    fn row_vector_small_entries() {
        let vec_1 = MatZq::from_str("[[1]] mod 10").unwrap();
        let vec_2 = MatZq::from_str("[[1, 10, 100]] mod 10").unwrap();
        let vec_3 = MatZq::from_str("[[1, 10, 100, 1000]] mod 10000").unwrap();

        assert_eq!(vec_1.norm_eucl_sqrd().unwrap(), Z::ONE);
        assert_eq!(vec_2.norm_eucl_sqrd().unwrap(), Z::ONE);
        assert_eq!(vec_3.norm_eucl_sqrd().unwrap(), Z::from(1010101));
    }

    /// Check whether the squared euclidean norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec = MatZq::from_str(&format!(
            "[[{}, {}, 2]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let max = Z::from(i64::MAX);
        let cmp = Z::from(2) * &max * &max + Z::from(4);

        assert_eq!(vec.norm_eucl_sqrd().unwrap(), cmp);
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatZq::from_str("[[1],[10],[100]] mod 10").unwrap();
        let vec_2 = MatZq::from_str("[[1],[10],[100],[1000]] mod 10000").unwrap();

        assert_eq!(vec_1.norm_eucl_sqrd().unwrap(), Z::ONE);
        assert_eq!(vec_2.norm_eucl_sqrd().unwrap(), Z::from(1010101));
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec = MatZq::from_str(&format!(
            "[[{}],[{}],[2]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let max = Z::from(i64::MAX);
        let cmp = Z::from(2) * &max * &max + Z::from(4);

        assert_eq!(vec.norm_eucl_sqrd().unwrap(), cmp);
    }

    /// Check whether euclidean norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatZq::from_str("[[1, 1],[10, 2]] mod 3").unwrap();

        assert!(mat.norm_eucl_sqrd().is_err());
    }
}

#[cfg(test)]
mod test_norm_infty {
    use super::{MatZq, Z};
    use std::str::FromStr;

    /// Check whether the infinity norm for row vectors
    /// with small entries is calculated correctly
    #[test]
    fn row_vector_small_entries() {
        let vec_1 = MatZq::from_str("[[6]] mod 10").unwrap();
        let vec_2 = MatZq::from_str("[[1, 10, 100]] mod 1000").unwrap();
        let vec_3 = MatZq::from_str("[[1, 10, 100, 1000]] mod 1000").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Z::from(4));
        assert_eq!(vec_2.norm_infty().unwrap(), Z::from(100));
        assert_eq!(vec_3.norm_infty().unwrap(), Z::from(100));
    }

    /// Check whether the infinity norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec = MatZq::from_str(&format!(
            "[[{}, {}, 2]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let cmp = Z::from(i64::MAX);

        assert_eq!(vec.norm_infty().unwrap(), cmp);
    }

    /// Check whether the infinity norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatZq::from_str("[[1],[10],[100]] mod 50").unwrap();
        let vec_2 = MatZq::from_str("[[1],[10],[100],[1000]] mod 1999").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Z::from(10));
        assert_eq!(vec_2.norm_infty().unwrap(), Z::from(999));
    }

    /// Check whether the infinity norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec = MatZq::from_str(&format!(
            "[[{}],[{}],[2]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let cmp = Z::from(i64::MAX);

        assert_eq!(vec.norm_infty().unwrap(), cmp);
    }

    /// Check whether infinity norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatZq::from_str("[[1, 1],[10, 2]] mod 3").unwrap();

        assert!(mat.norm_infty().is_err());
    }
}
