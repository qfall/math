// Copyright © 2024 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute several norms
//! defined on vectors.

use super::super::MatPolyOverZ;
use crate::{
    error::MathError,
    integer::Z,
    traits::{MatrixDimensions, MatrixGetEntry},
};

impl MatPolyOverZ {
    /// Returns the squared Euclidean norm or 2-norm of the given (row or column) vector
    /// or an error if the given [`MatPolyOverZ`] instance is not a (row or column) vector.
    /// The squared Euclidean norm for a polynomial vector is obtained by
    /// computing the sum of the squared Euclidean norms of the individual polynomials.
    /// The squared Euclidean norm for a polynomial is obtained by treating the coefficients
    /// of the polynomial as a vector and then applying the standard squared Euclidean norm.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatPolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let vec = MatPolyOverZ::from_str("[[1  1],[2  2 2],[1  3]]").unwrap();
    ///
    /// let sqrd_2_norm = vec.norm_eucl_sqrd().unwrap();
    ///
    /// assert_eq!(Z::from(18), sqrd_2_norm);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    ///     the given [`MatPolyOverZ`] instance is not a (row or column) vector.
    pub fn norm_eucl_sqrd(&self) -> Result<Z, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("norm_eucl_sqrd"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        }

        let mut result = Z::ZERO;

        for row in 0..self.get_num_rows() {
            for column in 0..self.get_num_columns() {
                result += unsafe { self.get_entry_unchecked(row, column) }.norm_eucl_sqrd();
            }
        }

        Ok(result)
    }

    /// Returns the infinity norm or ∞-norm of the given (row or column) vector
    /// or an error if the given [`MatPolyOverZ`] instance is not a (row or column) vector.
    /// The infinity norm for a polynomial vector is obtained by computing the
    /// infinity norm on the vector consisting of the infinity norms of the individual polynomials.
    /// The infinity norm for a polynomial is obtained by treating the coefficients
    /// of the polynomial as a vector and then applying the standard infinity norm.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatPolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let vec = MatPolyOverZ::from_str("[[1  1],[2  2 4],[1  3]]").unwrap();
    ///
    /// let infty_norm = vec.norm_infty().unwrap();
    ///
    /// assert_eq!(Z::from(4), infty_norm);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    ///     the given [`MatPolyOverZ`] instance is not a (row or column) vector.
    pub fn norm_infty(&self) -> Result<Z, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("norm_infty"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        }

        let mut result = Z::ZERO;

        for row in 0..self.get_num_rows() {
            for column in 0..self.get_num_columns() {
                let entry_norm = unsafe { self.get_entry_unchecked(row, column) }
                    .norm_infty()
                    .abs();
                if result < entry_norm {
                    result = entry_norm;
                }
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test_norm_eucl_sqrd {
    use crate::integer::{MatPolyOverZ, Z};
    use std::str::FromStr;

    /// Check whether the squared euclidean norm for row vectors
    /// with small entries is calculated correctly
    #[test]
    fn row_vector_small_entries() {
        let vec_1 = MatPolyOverZ::from_str("[[1  1]]").unwrap();
        let vec_2 = MatPolyOverZ::from_str("[[1  1, 2  10 3, 3  1 2 100]]").unwrap();
        let vec_3 = MatPolyOverZ::from_str("[[2  1 3, 1  10, 3  1 2 100, 1  1000]]").unwrap();

        assert_eq!(vec_1.norm_eucl_sqrd().unwrap(), Z::ONE);
        assert_eq!(vec_2.norm_eucl_sqrd().unwrap(), Z::from(10115));
        assert_eq!(vec_3.norm_eucl_sqrd().unwrap(), Z::from(1010115));
    }

    /// Check whether the squared euclidean norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec =
            MatPolyOverZ::from_str(&format!("[[1  {}, 2  {} 2, 2  2 1]]", i64::MAX, i64::MIN))
                .unwrap();
        let max = Z::from(i64::MAX);
        let min = Z::from(i64::MIN);
        let cmp = &min * &min + &max * &max + Z::from(9);

        assert_eq!(vec.norm_eucl_sqrd().unwrap(), cmp);
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatPolyOverZ::from_str("[[1  1],[2  10 3],[3  1 2 100]]").unwrap();
        let vec_2 = MatPolyOverZ::from_str("[[2  1 3],[1  10],[3  1 2 100],[1  1000]]").unwrap();

        assert_eq!(vec_1.norm_eucl_sqrd().unwrap(), Z::from(10115));
        assert_eq!(vec_2.norm_eucl_sqrd().unwrap(), Z::from(1010115));
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec =
            MatPolyOverZ::from_str(&format!("[[2  2 {}],[1  {}],[1  2]]", i64::MAX, i64::MIN))
                .unwrap();
        let max = Z::from(i64::MAX);
        let min = Z::from(i64::MIN);
        let cmp = &min * &min + &max * &max + Z::from(8);

        assert_eq!(vec.norm_eucl_sqrd().unwrap(), cmp);
    }

    /// Check whether euclidean norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatPolyOverZ::from_str("[[2  1 20, 1  1],[1  10, 2  1 2]]").unwrap();

        assert!(mat.norm_eucl_sqrd().is_err());
    }
}

#[cfg(test)]
mod test_norm_infty {
    use crate::integer::{MatPolyOverZ, Z};
    use std::str::FromStr;

    /// Check whether the infinity norm for row vectors
    /// with small entries is calculated correctly
    #[test]
    fn row_vector_small_entries() {
        let vec_1 = MatPolyOverZ::from_str("[[1  1]]").unwrap();
        let vec_2 = MatPolyOverZ::from_str("[[1  1, 2  10 3, 3  1 2 100]]").unwrap();
        let vec_3 = MatPolyOverZ::from_str("[[2  1 3, 1  10, 3  1 2 100, 1  1000]]").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Z::ONE);
        assert_eq!(vec_2.norm_infty().unwrap(), Z::from(100));
        assert_eq!(vec_3.norm_infty().unwrap(), Z::from(1000));
    }

    /// Check whether the infinity norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec =
            MatPolyOverZ::from_str(&format!("[[1  {}, 2  {} 2, 2  2 1]]", i64::MAX, i64::MIN))
                .unwrap();

        assert_eq!(vec.norm_infty().unwrap(), Z::from(i64::MIN).abs());
    }

    /// Check whether the infinity norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatPolyOverZ::from_str("[[1  1],[2  10 3],[3  1 2 100]]").unwrap();
        let vec_2 = MatPolyOverZ::from_str("[[2  1 3],[1  10],[3  1 2 100],[1  1000]]").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Z::from(100));
        assert_eq!(vec_2.norm_infty().unwrap(), Z::from(1000));
    }

    /// Check whether the infinity norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec =
            MatPolyOverZ::from_str(&format!("[[2  2 {}],[1  {}],[1  2]]", i64::MAX, i64::MIN))
                .unwrap();

        assert_eq!(vec.norm_infty().unwrap(), Z::from(i64::MIN).abs());
    }

    /// Check whether infinity norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatPolyOverZ::from_str("[[2  1 20, 1  1],[1  10, 2  1 2]]").unwrap();

        assert!(mat.norm_infty().is_err());
    }
}
