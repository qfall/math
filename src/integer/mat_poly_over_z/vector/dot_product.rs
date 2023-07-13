// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute the dot product of two vectors.

use crate::error::MathError;
use crate::integer::{MatPolyOverZ, PolyOverZ};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_poly::{fmpz_poly_add, fmpz_poly_mul};

impl MatPolyOverZ {
    /// Returns the dot product of two vectors of type [`MatPolyOverZ`].
    /// Note that the dimensions of the two vectors are irrelevant for the dot product.
    ///
    /// Parameters:
    /// - `other`: specifies the other vector the dot product is calculated over
    ///
    /// Returns the resulting `dot_product` as a [`PolyOverZ`] or an error,
    /// if the given [`MatPolyOverZ`] instances aren't vectors or have different
    /// numbers of entries.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly_vec1 = MatPolyOverZ::from_str("[[4  -1 0 1 1],[2  1 2]]").unwrap();
    /// let poly_vec2 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42]]").unwrap();
    ///
    /// let dot_prod = poly_vec1.dot_product(&poly_vec2).unwrap();
    /// ```
    ///
    /// Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    /// the given [`MatPolyOverZ`] instance is not a (row or column) vector.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingVectorDimensions`] if
    /// the given vectors have different lengths.
    pub fn dot_product(&self, other: &Self) -> Result<PolyOverZ, MathError> {
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
        let mut result = PolyOverZ::default();
        let mut temp = PolyOverZ::default();
        for i in 0..self_entries.len() {
            // sets result = result + self.entry[i] * other.entry[i] without cloned PolyOverZ element
            unsafe {
                fmpz_poly_mul(&mut temp.poly, &self_entries[i], &other_entries[i]);

                fmpz_poly_add(&mut result.poly, &result.poly, &temp.poly)
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test_dot_product {
    use crate::integer::{MatPolyOverZ, PolyOverZ};
    use std::str::FromStr;

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: row vector, `other`: row vector.
    #[test]
    fn row_with_row() {
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1, 2  1 2]]").unwrap();
        let poly_vec2 = MatPolyOverZ::from_str("[[2  1 1, 1  19]]").unwrap();

        let cmp = PolyOverZ::from_str("3  20 40 1").unwrap();
        let dot_prod = poly_vec1.dot_product(&poly_vec2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: column vector, `other`: column vector.
    #[test]
    fn column_with_column() {
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1],[2  1 2],[1  42]]").unwrap();
        let poly_vec2 = MatPolyOverZ::from_str("[[2  1 1],[1  19],[1  3]]").unwrap();

        let cmp = PolyOverZ::from_str("3  146 40 1").unwrap();
        let dot_prod = poly_vec1.dot_product(&poly_vec2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: row vector, `other`: column vector.
    #[test]
    fn row_with_column() {
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1, 2  1 2]]").unwrap();
        let poly_vec2 = MatPolyOverZ::from_str("[[2  1 1],[1  19]]").unwrap();

        let cmp = PolyOverZ::from_str("3  20 40 1").unwrap();
        let dot_prod = poly_vec1.dot_product(&poly_vec2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: column vector, `other`: row vector.
    #[test]
    fn column_with_row() {
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1],[2  1 2],[1  42]]").unwrap();
        let poly_vec2 = MatPolyOverZ::from_str("[[2  1 1, 1  19, 1  3]]").unwrap();

        let cmp = PolyOverZ::from_str("3  146 40 1").unwrap();
        let dot_prod = poly_vec1.dot_product(&poly_vec2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product is calculated correctly with large numbers.
    #[test]
    fn large_numbers() {
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1, 1  2, 1  1]]").unwrap();
        let poly_vec2 =
            MatPolyOverZ::from_str(&format!("[[2  1 2, 1  {}, 1  {}]]", i64::MAX, i64::MIN))
                .unwrap();

        let cmp = PolyOverZ::from_str(&format!("3  {} 3 2", i64::MAX)).unwrap();
        let dot_prod = poly_vec1.dot_product(&poly_vec2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product calculation on
    /// non vector instances yield an error.
    #[test]
    fn non_vector_yield_error() {
        let poly_vec = MatPolyOverZ::from_str("[[2  1 1],[2  1 2],[1  42]]").unwrap();
        let poly_mat =
            MatPolyOverZ::from_str("[[2  1 1, 1  3],[1  19, 2  5 6],[3  1 2 3, 1  3]]").unwrap();

        assert!(poly_vec.dot_product(&poly_mat).is_err());
        assert!(poly_mat.dot_product(&poly_vec).is_err());
        assert!(poly_mat.dot_product(&poly_mat).is_err());
        assert!(poly_vec.dot_product(&poly_vec).is_ok());
    }

    /// Check whether the dot product calculation on
    /// vectors of different lengths yield an error.
    #[test]
    fn different_lengths_yield_error() {
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1],[2  1 2],[1  42]]").unwrap();
        let poly_vec2 = MatPolyOverZ::from_str("[[2  1 1, 1  19, 1  3, 2  13 90]]").unwrap();

        assert!(poly_vec1.dot_product(&poly_vec2).is_err());
        assert!(poly_vec2.dot_product(&poly_vec1).is_err());
    }
}
