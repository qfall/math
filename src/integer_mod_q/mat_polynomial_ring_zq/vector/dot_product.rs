// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute the dot product of two vectors.

use crate::error::MathError;
use crate::integer::PolyOverZ;
use crate::integer_mod_q::{MatPolynomialRingZq, PolynomialRingZq};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fq::{fq_add, fq_mul};

impl MatPolynomialRingZq {
    /// Returns the dot product of two vectors of type [`MatPolynomialRingZq`].
    /// Note that the dimensions of the two vectors are irrelevant for the dot product.
    ///
    /// Parameters:
    /// - `other`: specifies the other vector the dot product is calculated over
    ///
    /// Returns the resulting `dot_product` as a [`PolynomialRingZq`] or an error,
    /// if the given [`MatPolynomialRingZq`] instances aren't vectors or have different
    /// numbers of entries.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_vec1 = MatPolyOverZ::from_str("[[4  -1 0 1 1],[2  1 2]]").unwrap();
    /// let poly_ring_vec1 = MatPolynomialRingZq::from((&poly_vec1, &modulus));
    /// let poly_vec2 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42]]").unwrap();
    /// let poly_ring_vec2 = MatPolynomialRingZq::from((&poly_vec2, &modulus));
    ///
    /// let dot_prod = poly_ring_vec1.dot_product(&poly_ring_vec2).unwrap();
    /// ```
    ///
    /// Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::VectorFunctionCalledOnNonVector`] if
    /// the given [`MatPolynomialRingZq`] instance is not a (row or column) vector.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingVectorDimensions`] if
    /// the given vectors have different lengths.
    pub fn dot_product(&self, other: &Self) -> Result<PolynomialRingZq, MathError> {
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
        let mut result = PolynomialRingZq::from((&PolyOverZ::default(), &self.modulus));
        let mut temp = PolyOverZ::default();
        for i in 0..self_entries.len() {
            // sets result = result + self.entry[i] * other.entry[i] without cloned PolyOverZ element
            unsafe {
                fq_mul(
                    &mut temp.poly,
                    &self_entries[i],
                    &other_entries[i],
                    self.modulus.get_fq_ctx_struct(),
                );

                fq_add(
                    &mut result.poly.poly,
                    &result.poly.poly,
                    &temp.poly,
                    self.modulus.get_fq_ctx_struct(),
                )
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test_dot_product {
    use crate::{
        integer::{MatPolyOverZ, PolyOverZ},
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolynomialRingZq},
    };
    use std::str::FromStr;

    const BITPRIME64: u64 = u64::MAX - 58;

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: row vector, `other`: row vector.
    #[test]
    fn row_with_row() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1, 2  1 2]]").unwrap();
        let poly_ring_vec1 = MatPolynomialRingZq::from((&poly_vec1, &modulus));
        let poly_vec2 = MatPolyOverZ::from_str("[[2  1 1, 1  19]]").unwrap();
        let poly_ring_vec2 = MatPolynomialRingZq::from((&poly_vec2, &modulus));

        let cmp = PolyOverZ::from_str("3  3 6 1").unwrap();
        let dot_prod = poly_ring_vec1.dot_product(&poly_ring_vec2).unwrap();

        assert_eq!(dot_prod, PolynomialRingZq::from((&cmp, &modulus)));
    }

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: column vector, `other`: column vector.
    #[test]
    fn column_with_column() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1],[2  1 2],[1  42]]").unwrap();
        let poly_ring_vec1 = MatPolynomialRingZq::from((&poly_vec1, &modulus));
        let poly_vec2 = MatPolyOverZ::from_str("[[2  1 1],[1  19],[1  3]]").unwrap();
        let poly_ring_vec2 = MatPolynomialRingZq::from((&poly_vec2, &modulus));

        let cmp = PolyOverZ::from_str("3  10 6 1").unwrap();
        let dot_prod = poly_ring_vec1.dot_product(&poly_ring_vec2).unwrap();

        assert_eq!(dot_prod, PolynomialRingZq::from((&cmp, &modulus)));
    }

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: row vector, `other`: column vector.
    #[test]
    fn row_with_column() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1, 2  1 2]]").unwrap();
        let poly_ring_vec1 = MatPolynomialRingZq::from((&poly_vec1, &modulus));
        let poly_vec2 = MatPolyOverZ::from_str("[[2  1 1],[1  19]]").unwrap();
        let poly_ring_vec2 = MatPolynomialRingZq::from((&poly_vec2, &modulus));

        let cmp = PolyOverZ::from_str("3  3 6 1").unwrap();
        let dot_prod = poly_ring_vec1.dot_product(&poly_ring_vec2).unwrap();

        assert_eq!(dot_prod, PolynomialRingZq::from((&cmp, &modulus)));
    }

    /// Check whether the dot product is calculated correctly for the combination:
    /// `self`: column vector, `other`: row vector.
    #[test]
    fn column_with_row() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1],[2  1 2],[1  42]]").unwrap();
        let poly_ring_vec1 = MatPolynomialRingZq::from((&poly_vec1, &modulus));
        let poly_vec2 = MatPolyOverZ::from_str("[[2  1 1, 1  19, 1  3]]").unwrap();
        let poly_ring_vec2 = MatPolynomialRingZq::from((&poly_vec2, &modulus));

        let cmp = PolyOverZ::from_str("3  10 6 1").unwrap();
        let dot_prod = poly_ring_vec1.dot_product(&poly_ring_vec2).unwrap();

        assert_eq!(dot_prod, PolynomialRingZq::from((&cmp, &modulus)));
    }

    /// Check whether the dot product is calculated correctly with large numbers.
    #[test]
    fn large_numbers() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", BITPRIME64)).unwrap();
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1, 1  2, 1  1]]").unwrap();
        let poly_ring_vec1 = MatPolynomialRingZq::from((&poly_vec1, &modulus));
        let poly_vec2 =
            MatPolyOverZ::from_str(&format!("[[2  1 2, 1  {}, 1  {}]]", i64::MAX, i64::MIN))
                .unwrap();
        let poly_ring_vec2 = MatPolynomialRingZq::from((&poly_vec2, &modulus));

        let cmp = PolyOverZ::from_str(&format!("3  {} 3 2", i64::MAX)).unwrap();
        let dot_prod = poly_ring_vec1.dot_product(&poly_ring_vec2).unwrap();

        assert_eq!(dot_prod, PolynomialRingZq::from((&cmp, &modulus)));
    }

    /// Check whether the dot product calculation on
    /// non vector instances yield an error.
    #[test]
    fn non_vector_yield_error() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_vec = MatPolyOverZ::from_str("[[2  1 1],[2  1 2],[1  42]]").unwrap();
        let poly_ring_vec = MatPolynomialRingZq::from((&poly_vec, &modulus));
        let poly_mat =
            MatPolyOverZ::from_str("[[2  1 1, 1  3],[1  19, 2  5 6],[3  1 2 3, 1  3]]").unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));

        assert!(poly_ring_vec.dot_product(&poly_ring_mat).is_err());
        assert!(poly_ring_mat.dot_product(&poly_ring_vec).is_err());
        assert!(poly_ring_mat.dot_product(&poly_ring_mat).is_err());
        assert!(poly_ring_vec.dot_product(&poly_ring_vec).is_ok());
    }

    /// Check whether the dot product calculation on
    /// vectors of different lengths yield an error.
    #[test]
    fn different_lengths_yield_error() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_vec1 = MatPolyOverZ::from_str("[[2  1 1],[2  1 2],[1  42]]").unwrap();
        let poly_ring_vec1 = MatPolynomialRingZq::from((&poly_vec1, &modulus));
        let poly_vec2 = MatPolyOverZ::from_str("[[2  1 1, 1  19, 1  3, 2  13 90]]").unwrap();
        let poly_ring_vec2 = MatPolynomialRingZq::from((&poly_vec2, &modulus));

        assert!(poly_ring_vec1.dot_product(&poly_ring_vec2).is_err());
        assert!(poly_ring_vec2.dot_product(&poly_ring_vec1).is_err());
    }
}
