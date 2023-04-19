// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute the dot product of two vectors.

use crate::error::MathError;
use crate::rational::{MatQ, Q};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpq::fmpq_addmul;

impl MatQ {
    /// Returns the dot product of two vectors of type [`MatQ`].
    ///
    /// Parameters:
    /// - `other`: specifies the other vector the dot product is calculated over
    ///
    /// Returns the resulting `dot_product` as a [`Q`] or an error,
    /// if the given [`MatQ`] instances aren't vectors or have different
    /// numbers of entries.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    /// # use qfall_math::rational::Q;
    ///
    /// let vec_1 = MatQ::from_str("[[1],[2],[3]]").unwrap();
    /// let vec_2 = MatQ::from_str("[[1,3,2]]").unwrap();
    ///
    /// let dot_prod = vec_1.dot_product(&vec_2).unwrap();
    ///
    /// assert_eq!(Q::from_str("13").unwrap(), dot_prod);
    /// ```
    ///
    /// Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    /// the given [`MatQ`] instance is not a (row or column) vector.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingVectorDimensions`] if
    /// the given vectors have different lengths.
    pub fn dot_product(&self, other: &Self) -> Result<Q, MathError> {
        if !self.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("dot_product"),
                self.get_num_rows(),
                self.get_num_columns(),
            ));
        } else if !other.is_vector() {
            return Err(MathError::VectorFunctionCalledOnNonVector(
                String::from("dot_product"),
                other.get_num_rows(),
                other.get_num_columns(),
            ));
        }

        let self_entries = self.collect_entries();
        let other_entries = other.collect_entries();

        if self_entries.len() != other_entries.len() {
            return Err(MathError::MismatchingVectorDimensions(format!(
                "You called the function 'dot_product' for vectors of different lengths: {} and {}",
                self_entries.len(),
                other_entries.len()
            )));
        }

        // calculate dot product of vectors
        let mut result = Q::default();
        for i in 0..self_entries.len() {
            // sets result = result + self.entry[i] * other.entry[i] without cloned Z element
            unsafe { fmpq_addmul(&mut result.value, &self_entries[i], &other_entries[i]) }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test_dot_product {

    use super::{MatQ, Q};
    use std::str::FromStr;

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: row vector, `other`: row vector
    #[test]
    fn row_with_row() {
        let vec_1 = MatQ::from_str("[[1/2,2/7,-3]]").unwrap();
        let vec_2 = MatQ::from_str("[[1,3,2/7]]").unwrap();

        let dot_prod = vec_1.dot_product(&vec_2).unwrap();

        assert_eq!(dot_prod, Q::from_str("1/2").unwrap());
    }

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: column vector, `other`: column vector
    #[test]
    fn column_with_column() {
        let vec_1 = MatQ::from_str("[[1/2],[2/7],[-3]]").unwrap();
        let vec_2 = MatQ::from_str("[[1],[3],[2/7]]").unwrap();

        let dot_prod = vec_1.dot_product(&vec_2).unwrap();

        assert_eq!(dot_prod, Q::from_str("1/2").unwrap());
    }

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: row vector, `other`: column vector
    #[test]
    fn row_with_column() {
        let vec_1 = MatQ::from_str("[[1/2,2/7,-3]]").unwrap();
        let vec_2 = MatQ::from_str("[[1],[3],[2/7]]").unwrap();

        let dot_prod = vec_1.dot_product(&vec_2).unwrap();

        assert_eq!(dot_prod, Q::from_str("1/2").unwrap());
    }

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: column vector, `other`: row vector
    #[test]
    fn column_with_row() {
        let vec_1 = MatQ::from_str("[[1/2],[2/7],[-3]]").unwrap();
        let vec_2 = MatQ::from_str("[[1,3,2/7]]").unwrap();

        let dot_prod = vec_1.dot_product(&vec_2).unwrap();

        assert_eq!(dot_prod, Q::from_str("1/2").unwrap());
    }

    /// Check whether the dot product is calculated correctly with large numbers
    #[test]
    fn large_numbers() {
        let vec_1 = MatQ::from_str(&format!("[[1,-1,{}]]", i64::MAX)).unwrap();
        let vec_2 = MatQ::from_str(&format!("[[1,{},1]]", i64::MIN)).unwrap();
        let cmp = Q::from_str("-1").unwrap() * Q::from_str(&format!("{}", i64::MIN)).unwrap()
            + Q::from_str(&format!("{}", i64::MAX)).unwrap()
            + Q::from_str("1").unwrap();

        let dot_prod = vec_1.dot_product(&vec_2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product calculation on
    /// non vector instances yield an error
    #[test]
    fn non_vector_yield_error() {
        let vec = MatQ::from_str("[[1/2,3,2/7]]").unwrap();
        let mat = MatQ::from_str("[[1,2],[2/7,3],[-3,4]]").unwrap();

        assert!(vec.dot_product(&mat).is_err());
        assert!(mat.dot_product(&vec).is_err());
        assert!(mat.dot_product(&mat).is_err());
        assert!(vec.dot_product(&vec).is_ok());
    }

    /// Check whether the dot product calculation on
    /// vectors of different lengths yield an error
    #[test]
    fn different_lengths_yield_error() {
        let vec_1 = MatQ::from_str("[[1,2,3]]").unwrap();
        let vec_2 = MatQ::from_str("[[1,2,3,4]]").unwrap();

        assert!(vec_1.dot_product(&vec_2).is_err());
        assert!(vec_2.dot_product(&vec_1).is_err());
    }
}
