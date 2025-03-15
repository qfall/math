// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to transform a [`MatPolyOverZ`]
//! into a [`MatZ`] and reverse by using the coefficient embedding.

use super::MatPolyOverZ;
use crate::{
    integer::{MatZ, PolyOverZ, Z},
    traits::{
        FromCoefficientEmbedding, GetCoefficient, GetEntry, GetNumColumns, GetNumRows,
        IntoCoefficientEmbedding, SetCoefficient, SetEntry,
    },
};

impl IntoCoefficientEmbedding<MatZ> for &MatPolyOverZ {
    /// Computes the coefficient embedding of the matrix of polynomials
    /// in a [`MatZ`]. Each column vector of polynomials is embedded into
    /// `size` many row vectors of coefficients. The first one containing their
    /// coefficients of degree 0, and the last one their coefficients
    /// of degree `size - 1`.
    /// It inverts the operation of [`MatPolyOverZ::from_coefficient_embedding`].
    ///
    /// Parameters:
    /// - `size`: determines the number of rows of the embedding. It has to be larger
    ///     than the degree of the polynomial.
    ///
    /// Returns a coefficient embedding as a matrix if `size` is large enough.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::{
    ///     integer::{MatZ, MatPolyOverZ},
    ///     traits::IntoCoefficientEmbedding,
    /// };
    ///
    /// let poly = MatPolyOverZ::from_str("[[1  1, 2  1 2],[1  -1, 2  -1 -2]]").unwrap();
    /// let embedding = poly.into_coefficient_embedding(2);
    /// let cmp_mat = MatZ::from_str("[[1, 1],[0, 2],[-1, -1],[0, -2]]").unwrap();
    /// assert_eq!(cmp_mat, embedding);
    /// ```
    ///
    /// # Panics ...
    /// - if `size` is not larger than the degree of the polynomial, i.e.
    ///     not all coefficients can be embedded.
    fn into_coefficient_embedding(self, size: impl Into<i64>) -> MatZ {
        let size = size.into();

        let num_rows = self.get_num_rows();
        let num_columns = self.get_num_columns();

        let mut out = MatZ::new(num_rows * size, num_columns);

        for column in 0..num_columns {
            for row in 0..num_rows {
                let entry: PolyOverZ = self.get_entry(row, column).unwrap();
                let length = entry.get_degree() + 1;
                assert!(
                    size >= length,
                    "The matrix can not be embedded, as the length \
                    of a polynomial ({length}) is larger than \
                    the provided size ({size})."
                );

                for index in 0..size {
                    let coeff: Z = entry.get_coeff(index).unwrap();
                    out.set_entry(row * size + index, column, coeff).unwrap()
                }
            }
        }

        out
    }
}

impl FromCoefficientEmbedding<(&MatZ, i64)> for MatPolyOverZ {
    /// Computes a [`MatPolyOverZ`] from a coefficient embedding.
    /// Interprets the first `degree + 1` many rows of the matrix as the
    /// coefficients of the first row of polynomials. The first one containing
    /// their coefficients of degree 0, and the last one their coefficients
    /// of degree `degree`.
    /// It inverts the operation of
    /// [`MatPolyOverZ::into_coefficient_embedding`](#method.into_coefficient_embedding).
    ///
    /// Parameters:
    /// - `embedding`: the coefficient matrix and the maximal
    ///   degree of the polynomials (defines how the matrix is split)
    ///
    /// Returns a matrix of polynomials that corresponds to the embedding.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::{
    ///     integer::{MatZ, MatPolyOverZ},
    ///     traits::FromCoefficientEmbedding,
    /// };
    ///
    /// let matrix = MatZ::from_str("[[17, 1],[3, 2],[-5, 3]]").unwrap();
    /// let poly = MatPolyOverZ::from_coefficient_embedding((&matrix, 2));
    /// let cmp_poly = MatPolyOverZ::from_str("[[3  17 3 -5, 3  1 2 3]]").unwrap();
    /// assert_eq!(cmp_poly, poly);
    /// ```
    fn from_coefficient_embedding(embedding: (&MatZ, i64)) -> Self {
        let degree = embedding.1;
        let num_rows = embedding.0.get_num_rows();
        let num_columns = embedding.0.get_num_columns();

        assert_eq!(
            num_rows % (degree+1),
            0,
            "The provided degree of polynomials ({degree}) +1 must divide the number of rows of the embedding ({}).",
            num_rows
        );

        let mut out = MatPolyOverZ::new(num_rows / (degree + 1), num_columns);

        for row in 0..out.get_num_rows() {
            for column in 0..num_columns {
                let mut poly = PolyOverZ::default();
                for index in 0..(degree + 1) {
                    let coeff: Z = embedding
                        .0
                        .get_entry(row * (degree + 1) + index, column)
                        .unwrap();
                    poly.set_coeff(index, coeff).unwrap();
                }
                out.set_entry(row, column, poly).unwrap();
            }
        }

        out
    }
}

#[cfg(test)]
mod test_into_coefficient_embedding {
    use crate::{
        integer::{MatPolyOverZ, MatZ},
        traits::{Concatenate, IntoCoefficientEmbedding},
    };
    use std::str::FromStr;

    /// Ensure that the initialization of the identity matrix works.
    #[test]
    fn standard_basis() {
        let standard_basis =
            MatPolyOverZ::from_str("[[1  1, 2  0 1, 3  0 0 1],[1  1, 2  0 1, 3  0 0 1]]").unwrap();

        let basis = standard_basis.into_coefficient_embedding(3);

        assert_eq!(
            MatZ::identity(3, 3)
                .concat_vertical(&MatZ::identity(3, 3))
                .unwrap(),
            basis
        )
    }

    /// Ensure that the initialization of the identity matrix works.
    #[test]
    fn standard_basis_vector() {
        let standard_basis = MatPolyOverZ::from_str("[[1  1, 2  0 1]]").unwrap();

        let basis = standard_basis.into_coefficient_embedding(3);

        assert_eq!(MatZ::identity(3, 2), basis);
    }

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let poly = MatPolyOverZ::from_str(&format!(
            "[[3  17 {} {}, 1  1],[1  1, 2  0 1]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();

        let matrix = poly.into_coefficient_embedding(3);

        let cmp_matrix = MatZ::from_str(&format!("[[17, 1],[{}, 0],[{}, 0]]", i64::MAX, i64::MIN))
            .unwrap()
            .concat_vertical(&MatZ::identity(3, 2))
            .unwrap();
        assert_eq!(cmp_matrix, matrix);
    }

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries_vector() {
        let poly =
            MatPolyOverZ::from_str(&format!("[[3  17 {} {}, 1  1]]", i64::MAX, i64::MIN)).unwrap();

        let matrix = poly.into_coefficient_embedding(3);

        let cmp_matrix =
            MatZ::from_str(&format!("[[17, 1],[{}, 0],[{}, 0]]", i64::MAX, i64::MIN)).unwrap();
        assert_eq!(cmp_matrix, matrix);
    }

    /// Ensure that the function panics if the the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small() {
        let poly = MatPolyOverZ::from_str("[[3  17 5 7, 2  0 1],[1  1, 1  1]]").unwrap();

        let _ = poly.into_coefficient_embedding(2);
    }

    /// Ensure that the function panics if the the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small_vector() {
        let poly = MatPolyOverZ::from_str("[[3  17 5 7, 2  0 1]]").unwrap();

        let _ = poly.into_coefficient_embedding(2);
    }
}

#[cfg(test)]
mod test_from_coefficient_embedding {
    use crate::{
        integer::{MatPolyOverZ, MatZ},
        traits::FromCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let matrix =
            MatZ::from_str(&format!("[[17, 0],[{}, -1],[{}, 0]]", i64::MAX, i64::MIN)).unwrap();

        let poly = MatPolyOverZ::from_coefficient_embedding((&matrix, 0));

        let cmp_poly = MatPolyOverZ::from_str(&format!(
            "[[1  17, 0],[1  {}, 1  -1],[1  {}, 0]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        assert_eq!(cmp_poly, poly);
    }

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries_vector() {
        let matrix =
            MatZ::from_str(&format!("[[17, 0],[{}, -1],[{}, 0]]", i64::MAX, i64::MIN)).unwrap();

        let poly = MatPolyOverZ::from_coefficient_embedding((&matrix, 2));

        let cmp_poly =
            MatPolyOverZ::from_str(&format!("[[3  17 {} {}, 2  0 -1]]", i64::MAX, i64::MIN))
                .unwrap();
        assert_eq!(cmp_poly, poly);
    }

    /// Ensure that the function panics if the provided degree does not divide
    /// the number of rows of the embedding.
    #[test]
    #[should_panic]
    fn degree_not_dividing() {
        let matrix =
            MatZ::from_str(&format!("[[17, 0],[{}, -1],[{}, 0]]", i64::MAX, i64::MIN)).unwrap();

        let _ = MatPolyOverZ::from_coefficient_embedding((&matrix, 1));
    }
}
