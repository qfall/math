// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to transform a [`PolyOverZ`]
//! into a [`MatZ`] and reverse by using the coefficient embedding.

use crate::{
    integer::{MatZ, PolyOverZ},
    traits::{
        FromCoefficientEmbedding, GetCoefficient, GetEntry, GetNumRows, IntoCoefficientEmbedding,
        SetCoefficient, SetEntry,
    },
};

impl IntoCoefficientEmbedding<MatZ> for &PolyOverZ {
    /// Computes the coefficient embedding of the polynomial
    /// in a [`MatZ`] as a column vector, where the i-th entry
    /// of the vector corresponds to the i-th coefficient.
    /// It inverts the operation of [`PolyOverZ::from_coefficient_embedding`].
    ///
    /// Parameters:
    /// - `size`: determines the number of rows of the embedding. It has to be larger
    /// than the degree of the polynomial.
    ///
    /// Returns a coefficient embedding as a column vector if `size` is large enough.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::{
    ///     integer::{MatZ, PolyOverZ},
    ///     traits::IntoCoefficientEmbedding,
    /// };
    ///
    /// let poly = PolyOverZ::from_str("3  17 3 -5").unwrap();
    /// let vector = poly.into_coefficient_embedding(4);
    /// let cmp_vector = MatZ::from_str("[[17],[3],[-5],[0]]").unwrap();
    /// assert_eq!(cmp_vector, vector);
    /// ```
    ///
    /// # Panics ...
    /// - if `size` is not larger than the degree of the polynomial, i.e.
    /// not all coefficients can be embedded.
    fn into_coefficient_embedding(self, size: impl Into<i64>) -> MatZ {
        let size = size.into();
        let length = self.get_degree() + 1;
        assert!(
            size >= length,
            "The polynomial can not be embedded in the vector, \
            as the length of the polynomial ({length}) is larger than \
            the provided size ({size})."
        );
        let mut out = MatZ::new(size, 1);
        for j in 0..size {
            match self.get_coeff(j) {
                Ok(value) => out.set_entry(j, 0, value).unwrap(),
                Err(_) => break,
            }
        }
        out
    }
}

impl FromCoefficientEmbedding<&MatZ> for PolyOverZ {
    /// Computes a polynomial from a vector.
    /// The first i-th entry of the column vector is taken
    /// as the coefficient of the polynomial.
    /// It inverts the operation of
    /// [`PolyOverZ::into_coefficient_embedding`](#method.into_coefficient_embedding).
    ///
    /// Parameters:
    /// - `embedding`: the column vector that encodes the embedding
    ///
    /// Returns a polynomial that corresponds to the embedding.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::{
    ///     integer::{MatZ, PolyOverZ},
    ///     traits::FromCoefficientEmbedding,
    /// };
    ///
    /// let vector = MatZ::from_str("[[17],[3],[-5]]").unwrap();
    /// let poly = PolyOverZ::from_coefficient_embedding(&vector);
    /// let cmp_poly = PolyOverZ::from_str("3  17 3 -5").unwrap();
    /// assert_eq!(cmp_poly, poly);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided embedding is not a column vector.
    fn from_coefficient_embedding(embedding: &MatZ) -> Self {
        assert!(embedding.is_column_vector());
        let mut out = PolyOverZ::default();
        for i in 0..embedding.get_num_rows() {
            out.set_coeff(i, embedding.get_entry(i, 0).unwrap())
                .unwrap()
        }
        out
    }
}

#[cfg(test)]
mod test_into_coefficient_embedding {
    use crate::{
        integer::{MatZ, PolyOverZ},
        traits::IntoCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let poly = PolyOverZ::from_str(&format!("3  17 {} {}", i64::MAX, i64::MIN)).unwrap();

        let vector = poly.into_coefficient_embedding(3);

        let cmp_vector = MatZ::from_str(&format!("[[17],[{}],[{}]]", i64::MAX, i64::MIN)).unwrap();
        assert_eq!(cmp_vector, vector);
    }

    /// Ensure that the function panics if the the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small() {
        let poly = PolyOverZ::from_str("3  17 12 -1").unwrap();

        let _ = poly.into_coefficient_embedding(2);
    }
}

#[cfg(test)]
mod test_from_coefficient_embedding {
    use crate::{
        integer::{MatZ, PolyOverZ},
        traits::FromCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let vector = MatZ::from_str(&format!("[[17],[{}],[{}]]", i64::MAX, i64::MIN)).unwrap();

        let poly = PolyOverZ::from_coefficient_embedding(&vector);

        let cmp_poly = PolyOverZ::from_str(&format!("3  17 {} {}", i64::MAX, i64::MIN)).unwrap();
        assert_eq!(cmp_poly, poly);
    }

    /// Ensure that the function panics if the provided matrix is not a column vector.
    #[test]
    #[should_panic]
    fn not_column_vector() {
        let vector = MatZ::from_str("[[17, 1],[-17, -1],[5, 9]]").unwrap();

        let _ = PolyOverZ::from_coefficient_embedding(&vector);
    }
}
