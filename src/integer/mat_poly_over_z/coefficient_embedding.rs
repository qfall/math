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
    integer::{MatZ, PolyOverZ},
    traits::{
        Concatenate, FromCoefficientEmbedding, GetCoefficient, GetEntry, GetNumColumns, GetNumRows,
        IntoCoefficientEmbedding, SetEntry,
    },
};

impl MatPolyOverZ {
    /// Computes the coefficient embedding of a matrix of polynomials.
    /// All rows are independently embedded using the coefficient embedding
    /// and then vertically concatenated to an embedding.
    /// It inverts the operation of
    /// [`MatPolyOverZ::from_coefficient_embedding_to_matrix`].
    ///
    /// Parameters:
    /// - `size`: determines the number of rows each polynomial is embedded in.
    /// It has to be larger than the degree of all polynomials.
    ///
    /// Returns a coefficient embedding as a matrix if `size` is large enough.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::{
    ///     integer::{MatZ, MatPolyOverZ},
    /// };
    ///
    /// let poly = MatPolyOverZ::from_str("[[1  1, 2  1 2],[1  -1, 2  -1 -2]]").unwrap();
    /// let mat = poly.into_coefficient_embedding_from_matrix(2);
    /// let cmp_mat = MatZ::from_str("[[1, 1],[0, 2],[-1, -1],[0, -2]]").unwrap();
    /// assert_eq!(cmp_mat, mat);
    /// ```
    ///
    /// # Panics ...
    /// - if `size` is not larger than the degree of the polynomial, i.e.
    /// not all coefficients can be embedded.
    pub fn into_coefficient_embedding_from_matrix(&self, size: impl Into<i64>) -> MatZ {
        let size = size.into();
        let mut embedded = self.get_row(0).unwrap().into_coefficient_embedding(size);
        for i in 1..self.get_num_rows() {
            let self_i = self.get_row(i).unwrap().into_coefficient_embedding(size);
            embedded = embedded.concat_vertical(&self_i).unwrap();
        }
        embedded
    }

    /// Computes a matrix of polynomials from a matrix.
    /// The embedding is split into submatrices with `degree` number of rows.
    /// All submatrices are independently turned into a row vector of polynomials
    /// and then vertically concatenated to a matrix of polynomials.
    /// It inverts the operation of
    /// [`MatPolyOverZ::into_coefficient_embedding_from_matrix`].
    ///
    /// Parameters:
    /// - `degree`: the maximal degree of the polynomials by which the matrix is split
    ///
    /// Returns a matrix of polynomials that corresponds to the embedding.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::{
    ///     integer::{MatZ, MatPolyOverZ},
    /// };
    ///
    /// let matrix = MatZ::from_str("[[17, 1],[3, 2],[-5, 3],[1, 2]]").unwrap();
    /// let poly = MatPolyOverZ::from_coefficient_embedding_to_matrix(&matrix, 2);
    /// let cmp_poly = MatPolyOverZ::from_str("[[2  17 3, 2  1 2],[2  -5 1,2  3 2]]").unwrap();
    /// assert_eq!(cmp_poly, poly);
    /// ```
    ///
    /// # Panics...
    /// - if `degree` does not divide the number of rows of the embedding.
    pub fn from_coefficient_embedding_to_matrix(embedding: &MatZ, degree: impl Into<i64>) -> Self {
        let degree = degree.into();
        assert_eq!(
            embedding.get_num_rows() % degree,
            0,
            "The provided degree of polynomials ({degree}) must divide the number of rows of the embedding ({}).",
            embedding.get_num_rows()
        );

        let nr_sub_mat = embedding.get_num_rows() / degree;
        let mut row_poly_mat = Vec::new();
        for i in 0..nr_sub_mat {
            let sub_mat_i = embedding
                .get_submatrix(
                    i * degree,
                    (i + 1) * degree - 1,
                    0,
                    embedding.get_num_columns() - 1,
                )
                .unwrap();
            row_poly_mat.push(MatPolyOverZ::from_coefficient_embedding(&sub_mat_i));
        }

        let mut out = row_poly_mat.first().unwrap().clone();
        for poly_vec in row_poly_mat.iter().skip(1) {
            out = out.concat_vertical(poly_vec).unwrap();
        }
        out
    }
}

impl IntoCoefficientEmbedding<MatZ> for &MatPolyOverZ {
    /// Computes the coefficient embedding of the row vector of polynomials
    /// in a [`MatZ`]. The (i,j) th entry corresponds to the i-th coefficient
    /// of the j-th polynomial provided.
    /// It inverts the operation of [`MatPolyOverZ::from_coefficient_embedding`].
    ///
    /// Parameters:
    /// - `size`: determines the number of rows of the embedding. It has to be larger
    /// than the degree of the polynomial.
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
    /// let poly = MatPolyOverZ::from_str("[[3  17 3 -5, 4  1 2 3 4]]").unwrap();
    /// let mat = poly.into_coefficient_embedding(4);
    /// let cmp_mat = MatZ::from_str("[[17, 1],[3, 2],[-5, 3],[0, 4]]").unwrap();
    /// assert_eq!(cmp_mat, mat);
    /// ```
    ///
    /// # Panics ...
    /// - if `size` is not larger than the degree of the polynomial, i.e.
    /// not all coefficients can be embedded.
    /// - if `self` is not a row vector
    fn into_coefficient_embedding(self, size: impl Into<i64>) -> MatZ {
        assert!(self.is_row_vector());
        let size = size.into();

        let mut poly: Vec<PolyOverZ> = Vec::new();
        for i in 0..self.get_num_columns() {
            let entry = self.get_entry(0, i).unwrap();
            let length = entry.get_degree() + 1;
            assert!(
                size >= length,
                "The polynomial can not be embedded in the vector, \
                as the length of the polynomial ({length}) is larger than \
                the provided size ({size})."
            );
            poly.push(entry);
        }
        let mut out = MatZ::new(size, poly.len());

        for (i, entry) in poly.iter().enumerate() {
            for j in 0..size {
                match entry.get_coeff(j) {
                    Ok(value) => out.set_entry(j, i, value).unwrap(),
                    Err(_) => break,
                }
            }
        }

        out
    }
}

impl FromCoefficientEmbedding<&MatZ> for MatPolyOverZ {
    /// Computes a row vector of polynomials from a matrix.
    /// The j-th entry of the i-th column vector is taken
    /// as the coefficient of the polynomial of the i-th polynomial.
    /// It inverts the operation of
    /// [`MatPolyOverZ::into_coefficient_embedding`](#method.into_coefficient_embedding).
    ///
    /// Parameters:
    /// - `embedding`: the column vector that encodes the embedding
    ///
    /// Returns a row vector of polynomials that corresponds to the embedding.
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
    /// let poly = MatPolyOverZ::from_coefficient_embedding(&matrix);
    /// let cmp_poly = MatPolyOverZ::from_str("[[3  17 3 -5, 3  1 2 3]]").unwrap();
    /// assert_eq!(cmp_poly, poly);
    /// ```
    fn from_coefficient_embedding(embedding: &MatZ) -> Self {
        let mut out = MatPolyOverZ::new(1, embedding.get_num_columns());

        for i in 0..embedding.get_num_columns() {
            let col_vec = embedding.get_column(i).unwrap();
            let entry = PolyOverZ::from_coefficient_embedding(&col_vec);
            out.set_entry(0, i, entry).unwrap();
        }
        out
    }
}

#[cfg(test)]
mod test_into_coefficient_embedding_from_matrix {
    use crate::{
        integer::{MatPolyOverZ, MatZ},
        traits::Concatenate,
    };
    use std::str::FromStr;

    /// Ensure that the initialization of the identity matrix works.
    #[test]
    fn standard_basis() {
        let standard_basis =
            MatPolyOverZ::from_str("[[1  1, 2  0 1, 3  0 0 1],[1  1, 2  0 1, 3  0 0 1]]").unwrap();

        let basis = standard_basis.into_coefficient_embedding_from_matrix(3);

        assert_eq!(
            MatZ::identity(3, 3)
                .concat_vertical(&MatZ::identity(3, 3))
                .unwrap(),
            basis
        )
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

        let matrix = poly.into_coefficient_embedding_from_matrix(3);

        let cmp_matrix = MatZ::from_str(&format!("[[17, 1],[{}, 0],[{}, 0]]", i64::MAX, i64::MIN))
            .unwrap()
            .concat_vertical(&MatZ::identity(3, 2))
            .unwrap();
        assert_eq!(cmp_matrix, matrix);
    }

    /// Ensure that the function panics if the the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small() {
        let poly = MatPolyOverZ::from_str("[[3  17 5 7, 2  0 1],[1  1, 1  1]]").unwrap();

        let _ = poly.into_coefficient_embedding_from_matrix(2);
    }
}

#[cfg(test)]
mod test_from_coefficient_embedding_to_matrix {
    use crate::integer::{MatPolyOverZ, MatZ};
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let matrix =
            MatZ::from_str(&format!("[[17, 0],[{}, -1],[{}, 0]]", i64::MAX, i64::MIN)).unwrap();

        let poly = MatPolyOverZ::from_coefficient_embedding_to_matrix(&matrix, 1);

        let cmp_poly = MatPolyOverZ::from_str(&format!(
            "[[1  17, 0],[1  {},1  -1],[1  {}, 0]]",
            i64::MAX,
            i64::MIN
        ))
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

        let _ = MatPolyOverZ::from_coefficient_embedding_to_matrix(&matrix, 2);
    }
}

#[cfg(test)]
mod test_into_coefficient_embedding {
    use crate::{
        integer::{MatPolyOverZ, MatZ},
        traits::IntoCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the initialization of the identity matrix works.
    #[test]
    fn standard_basis() {
        let standard_basis = MatPolyOverZ::from_str("[[1  1, 2  0 1]]").unwrap();

        let basis = standard_basis.into_coefficient_embedding(3);

        assert_eq!(MatZ::identity(3, 2), basis);
    }

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
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

        let poly = MatPolyOverZ::from_coefficient_embedding(&matrix);

        let cmp_poly =
            MatPolyOverZ::from_str(&format!("[[3  17 {} {}, 2  0 -1]]", i64::MAX, i64::MIN))
                .unwrap();
        assert_eq!(cmp_poly, poly);
    }
}
