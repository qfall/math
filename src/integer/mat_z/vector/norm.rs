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
    integer::Z,
    traits::{GetNumColumns, GetNumRows},
};
use flint_sys::fmpz::{fmpz, fmpz_abs, fmpz_addmul, fmpz_cmpabs, fmpz_set};

impl MatZ {
    /// Returns the squared Euclidean norm or 2-norm of the given (row or column) vector.
    ///
    /// WARNING: This function may be renamed and changed in the future,
    /// once we integrate a sqrt function for [`Z`] values.
    ///
    /// # Example
    /// ```
    /// use math::integer::MatZ;
    /// use std::str::FromStr;
    /// # use math::integer::Z;
    ///
    /// let vec = MatZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// let sqrd_2_norm = vec.norm_sqrd_eucl().unwrap();
    ///
    /// assert_eq!(Z::from_i64(14), sqrd_2_norm);
    /// ```
    ///
    /// Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    /// the given [`MatZ`] instance is not a (row or column) vector.
    pub fn norm_sqrd_eucl(&self) -> Result<Z, MathError> {
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
        let mut result = fmpz(0);
        for entry in entries {
            // sets result = result + entry * entry without cloned Z element
            unsafe { fmpz_addmul(&mut result, &entry, &entry) }
        }

        // TODO: Add sqrt function here
        Ok(Z { value: result })
    }

    /// Returns the infinity norm or ∞-norm of the given (row or column) vector.
    ///
    /// # Example
    /// ```
    /// use math::integer::MatZ;
    /// use std::str::FromStr;
    /// # use math::integer::Z;
    ///
    /// let vec = MatZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// let infty_norm = vec.norm_infty().unwrap();
    ///
    /// assert_eq!(Z::from_i64(3), infty_norm);
    /// ```
    ///
    /// Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    /// the given [`MatZ`] instance is not a (row or column) vector.
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

        // find maximum of absolute fmpz entries
        let mut max = fmpz(0);
        for entry in entries {
            if unsafe { fmpz_cmpabs(&max, &entry) } < 0 {
                max = entry;
            }
        }

        // clone value and ensure that absolute maximum value is absolute
        let mut clone_max = fmpz(0);
        unsafe { fmpz_set(&mut clone_max, &max) };
        unsafe { fmpz_abs(&mut clone_max, &clone_max) }

        Ok(Z { value: clone_max })
    }
}

#[cfg(test)]
mod test_norm_sqrd_eucl {
    use super::{MatZ, Z};
    use std::str::FromStr;

    /// Check whether the squared euclidean norm for row vectors
    /// with small entries is calculated correctly
    #[test]
    fn row_vector_small_entries() {
        let vec_1 = MatZ::from_str("[[1]]").unwrap();
        let vec_2 = MatZ::from_str("[[1,10,100]]").unwrap();
        let vec_3 = MatZ::from_str("[[1,10,100, 1000]]").unwrap();

        assert_eq!(vec_1.norm_sqrd_eucl().unwrap(), Z::ONE);
        assert_eq!(vec_2.norm_sqrd_eucl().unwrap(), Z::from_i64(10101));
        assert_eq!(vec_3.norm_sqrd_eucl().unwrap(), Z::from_i64(1010101));
    }

    /// Check whether the squared euclidean norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec = MatZ::from_str(&format!("[[{},{}, 2]]", i64::MAX, i64::MIN)).unwrap();
        let max = Z::from(i64::MAX);
        let min = Z::from(i64::MIN);
        let cmp = &min * &min + &max * &max + Z::from(4);

        assert_eq!(vec.norm_sqrd_eucl().unwrap(), cmp);
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatZ::from_str("[[1],[10],[100]]").unwrap();
        let vec_2 = MatZ::from_str("[[1],[10],[100],[1000]]").unwrap();

        assert_eq!(vec_1.norm_sqrd_eucl().unwrap(), Z::from_i64(10101));
        assert_eq!(vec_2.norm_sqrd_eucl().unwrap(), Z::from_i64(1010101));
    }

    /// Check whether the squared euclidean norm for column vectors
    /// with large entries is calculated correctly
    #[test]
    fn column_vector_large_entries() {
        let vec = MatZ::from_str(&format!("[[{}],[{}],[2]]", i64::MAX, i64::MIN)).unwrap();
        let max = Z::from(i64::MAX);
        let min = Z::from(i64::MIN);
        let cmp = &min * &min + &max * &max + Z::from(4);

        assert_eq!(vec.norm_sqrd_eucl().unwrap(), cmp);
    }

    /// Check whether euclidean norm calculations of non vectors yield an error
    #[test]
    fn non_vector_yield_error() {
        let mat = MatZ::from_str("[[1,1],[10,2]]").unwrap();

        assert!(mat.norm_sqrd_eucl().is_err());
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
        let vec_2 = MatZ::from_str("[[1,10,100]]").unwrap();
        let vec_3 = MatZ::from_str("[[1,10,100, 1000]]").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Z::ONE);
        assert_eq!(vec_2.norm_infty().unwrap(), Z::from_i64(100));
        assert_eq!(vec_3.norm_infty().unwrap(), Z::from_i64(1000));
    }

    /// Check whether the infinity norm for row vectors
    /// with large entries is calculated correctly
    #[test]
    fn row_vector_large_entries() {
        let vec = MatZ::from_str(&format!("[[{},{}, 2]]", i64::MAX, i64::MIN)).unwrap();
        let cmp = Z::from(-1) * Z::from(i64::MIN);

        assert_eq!(vec.norm_infty().unwrap(), cmp);
    }

    /// Check whether the infinity norm for column vectors
    /// with small entries is calculated correctly
    #[test]
    fn column_vector_small_entries() {
        let vec_1 = MatZ::from_str("[[1],[10],[100]]").unwrap();
        let vec_2 = MatZ::from_str("[[1],[10],[100],[1000]]").unwrap();

        assert_eq!(vec_1.norm_infty().unwrap(), Z::from_i64(100));
        assert_eq!(vec_2.norm_infty().unwrap(), Z::from_i64(1000));
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
        let mat = MatZ::from_str("[[1,1],[10,2]]").unwrap();

        assert!(mat.norm_infty().is_err());
    }
}
