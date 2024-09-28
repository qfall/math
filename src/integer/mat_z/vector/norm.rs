// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute several norms
//! defined on vectors.

use super::super::MatZ;
use crate::{
    error::MathError,
    integer::{fmpz_helpers::find_max_abs, Z},
    traits::{GetNumColumns, GetNumRows},
};
use flint_sys::fmpz::fmpz_addmul;

impl MatZ {
    /// Returns the squared Euclidean norm or 2-norm of the given (row or column) vector
    /// or an error if the given [`MatZ`] instance is not a (row or column) vector.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatZ, Z};
    /// use std::str::FromStr;
    ///
    /// let vec = MatZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// let sqrd_2_norm = vec.norm_eucl_sqrd().unwrap();
    ///
    /// // 1*1 + 2*2 + 3*3 = 14
    /// assert_eq!(Z::from(14), sqrd_2_norm);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    ///     the given [`MatZ`] instance is not a (row or column) vector.
    pub fn norm_eucl_sqrd(&self) -> Result<Z, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("norm_eucl_sqrd"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        }

        let entries = self.collect_entries();

        // sum squared entries in result
        let mut result = Z::ZERO;
        for entry in entries {
            // sets result = result + entry * entry without cloned Z element
            unsafe { fmpz_addmul(&mut result.value, &entry, &entry) }
        }

        Ok(result)
    }

    /// Returns the infinity norm or ∞-norm of the given (row or column) vector
    /// or an error if the given [`MatZ`] instance is not a (row or column) vector.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatZ, Z};
    /// use std::str::FromStr;
    ///
    /// let vec = MatZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// let infty_norm = vec.norm_infty().unwrap();
    ///
    /// // max{1, 2, 3} = 3
    /// assert_eq!(Z::from(3), infty_norm);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    ///     the given [`MatZ`] instance is not a (row or column) vector.
    pub fn norm_infty(&self) -> Result<Z, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("norm_infty"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        }

        // collect all entries in vector
        let entries = self.collect_entries();

        // find maximum of absolute fmpz entries and
        // return cloned absolute maximum [`Z`] value
        Ok(find_max_abs(&entries))
    }
}

#[cfg(test)]
mod test_norm_eucl_sqrd {
    use super::{MatZ, Z};
    use std::str::FromStr;

    /// Check whether the squared euclidean norm for row vectors
    /// with small entries is calculated correctly
    #[test]
    fn row_vector_small_entries() {
        let vec_1 = MatZ::from_str("[[1]]").unwrap();
        let vec_2 = MatZ::from_str("[[1, 10, 100]]").unwrap();
        let vec_3 = MatZ::from_str("[[1, 10, 100, 1000]]").unwrap();

        assert_eq!(vec_1.norm_eucl_sqrd().unwrap(), Z::ONE);
        assert_eq!(vec_2.norm_eucl_sqrd().unwrap(), Z::from(10101));
        assert_eq!(vec_3.norm_eucl_sqrd().unwrap(), Z::from(1010101));
    }

    /// Check whether the squared euclidean norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec = MatZ::from_str(&format!("[[{}, {}, 2]]", i64::MAX, i64::MIN)).unwrap();
        let max = Z::from(i64::MAX);
        let min = Z::from(i64::MIN);
        let cmp = &min * &min + &max * &max + Z::from(4);

        assert_eq!(vec.norm_eucl_sqrd().unwrap(), cmp);
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatZ::from_str("[[1],[10],[100]]").unwrap();
        let vec_2 = MatZ::from_str("[[1],[10],[100],[1000]]").unwrap();

        assert_eq!(vec_1.norm_eucl_sqrd().unwrap(), Z::from(10101));
        assert_eq!(vec_2.norm_eucl_sqrd().unwrap(), Z::from(1010101));
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec = MatZ::from_str(&format!("[[{}],[{}],[2]]", i64::MAX, i64::MIN)).unwrap();
        let max = Z::from(i64::MAX);
        let min = Z::from(i64::MIN);
        let cmp = &min * &min + &max * &max + Z::from(4);

        assert_eq!(vec.norm_eucl_sqrd().unwrap(), cmp);
    }

    /// Check whether euclidean norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatZ::from_str("[[1, 1],[10, 2]]").unwrap();

        assert!(mat.norm_eucl_sqrd().is_err());
    }
}

#[cfg(test)]
mod test_norm_infty {
    use super::{MatZ, Z};
    use std::str::FromStr;

    /// Check whether the infinity norm for row vectors
    /// with small entries is calculated correctly
    #[test]
    fn row_vector_small_entries() {
        let vec_1 = MatZ::from_str("[[1]]").unwrap();
        let vec_2 = MatZ::from_str("[[1, 10, 100]]").unwrap();
        let vec_3 = MatZ::from_str("[[1, 10, 100, 1000]]").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Z::ONE);
        assert_eq!(vec_2.norm_infty().unwrap(), Z::from(100));
        assert_eq!(vec_3.norm_infty().unwrap(), Z::from(1000));
    }

    /// Check whether the infinity norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec = MatZ::from_str(&format!("[[{}, {}, 2]]", i64::MAX, i64::MIN)).unwrap();
        let cmp = Z::from(-1) * Z::from(i64::MIN);

        assert_eq!(vec.norm_infty().unwrap(), cmp);
    }

    /// Check whether the infinity norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatZ::from_str("[[1],[10],[100]]").unwrap();
        let vec_2 = MatZ::from_str("[[1],[10],[100],[1000]]").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Z::from(100));
        assert_eq!(vec_2.norm_infty().unwrap(), Z::from(1000));
    }

    /// Check whether the infinity norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec = MatZ::from_str(&format!("[[{}],[{}],[2]]", i64::MAX, i64::MIN)).unwrap();
        let cmp = Z::from(-1) * Z::from(i64::MIN);

        assert_eq!(vec.norm_infty().unwrap(), cmp);
    }

    /// Check whether infinity norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatZ::from_str("[[1, 1],[10, 2]]").unwrap();

        assert!(mat.norm_infty().is_err());
    }
}
