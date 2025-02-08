// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to transform a [`MatPolynomialRingZq`]
//! into a [`MatZq`] and a [`ModulusPolynomialRingZq`] and reverse by using the coefficient embedding.

use super::MatPolynomialRingZq;
use crate::{
    integer::Z,
    integer_mod_q::{MatZq, ModulusPolynomialRingZq, PolynomialRingZq, Zq},
    traits::{
        Concatenate, FromCoefficientEmbedding, GetCoefficient, GetEntry, GetNumColumns, GetNumRows,
        IntoCoefficientEmbedding, SetEntry,
    },
};

impl MatPolynomialRingZq {
    /// Computes the coefficient embedding of a matrix of polynomials.
    /// All rows are independently embedded using the coefficient embedding
    /// and then vertically concatenated to an embedding.
    /// It inverts the operation of
    /// [`MatPolynomialRingZq::from_coefficient_embedding_to_matrix`].
    ///
    /// Parameters:
    /// - `size`: determines the number of rows each polynomial is embedded in.
    ///     It has to be larger than the degree of all polynomials.
    ///
    /// Returns a coefficient embedding as a matrix if `size` is large enough.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::{
    ///     integer_mod_q::{MatZq, MatPolynomialRingZq},
    /// };
    ///
    /// let poly = MatPolynomialRingZq::from_str("[[1  1, 2  1 2],[1  -1, 2  -1 -2]] / 3  1 2 3 mod 17").unwrap();
    /// let embedding = poly.into_coefficient_embedding_from_matrix(2);
    /// let cmp_mat = MatZq::from_str("[[1, 1],[0, 2],[-1, -1],[0, -2]] mod 17").unwrap();
    /// assert_eq!((cmp_mat, poly.get_mod()), embedding);
    /// ```
    ///
    /// # Panics ...
    /// - if `size` is not larger than the degree of the polynomial, i.e.
    ///     not all coefficients can be embedded.
    pub fn into_coefficient_embedding_from_matrix(
        &self,
        size: impl Into<i64>,
    ) -> (MatZq, ModulusPolynomialRingZq) {
        let size = size.into();
        let mut embedded = self.get_row(0).unwrap().into_coefficient_embedding(size);
        for i in 1..self.get_num_rows() {
            let self_i = self.get_row(i).unwrap().into_coefficient_embedding(size);
            embedded.0 = embedded.0.concat_vertical(&self_i.0).unwrap();
        }
        embedded
    }

    /// Computes a matrix of polynomials from a matrix.
    /// The embedding is split into submatrices with `degree` number of rows.
    /// All submatrices are independently turned into a row vector of polynomials
    /// and then vertically concatenated to a matrix of polynomials.
    /// It inverts the operation of
    /// [`MatPolynomialRingZq::into_coefficient_embedding_from_matrix`].
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
    ///     integer_mod_q::{MatZq, MatPolynomialRingZq, ModulusPolynomialRingZq},
    /// };
    ///
    /// let matrix = MatZq::from_str("[[17, 1],[3, 2],[-5, 3],[1, 2]] mod 19").unwrap();
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 2 3 4 mod 19").unwrap();
    /// let mat = MatPolynomialRingZq::from_coefficient_embedding_to_matrix((&matrix, &modulus), 2);
    /// let cmp_mat = MatPolynomialRingZq::from_str("[[2  17 3, 2  1 2],[2  -5 1, 2  3 2]] / 4  1 2 3 4 mod 19").unwrap();
    /// assert_eq!(cmp_mat, mat);
    /// ```
    ///
    /// # Panics...
    /// - if `degree` does not divide the number of rows of the embedding.
    /// - if the moduli mismatch.
    pub fn from_coefficient_embedding_to_matrix(
        embedding: (&MatZq, &ModulusPolynomialRingZq),
        degree: impl Into<i64>,
    ) -> Self {
        let degree = degree.into();
        assert_eq!(
            embedding.0.get_num_rows() % degree,
            0,
            "The provided degree of polynomials ({degree}) must divide the number of rows of the embedding ({}).",
            embedding.0.get_num_rows()
        );
        assert_eq!(
            Z::from(embedding.0.get_mod()),
            embedding.1.get_q(),
            "This is no valid embedding, since the integer moduli of matrix and modulus mismatch."
        );

        let nr_sub_mat = embedding.0.get_num_rows() / degree;
        let mut row_poly_mat = Vec::new();
        for i in 0..nr_sub_mat {
            let sub_mat_i = embedding
                .0
                .get_submatrix(
                    i * degree,
                    (i + 1) * degree - 1,
                    0,
                    embedding.0.get_num_columns() - 1,
                )
                .unwrap();
            row_poly_mat.push(MatPolynomialRingZq::from_coefficient_embedding((
                &sub_mat_i,
                embedding.1,
            )));
        }

        let mut out = row_poly_mat.first().unwrap().clone();
        for poly_vec in row_poly_mat.iter().skip(1) {
            out = out.concat_vertical(poly_vec).unwrap();
        }
        out
    }
}

impl IntoCoefficientEmbedding<(MatZq, ModulusPolynomialRingZq)> for &MatPolynomialRingZq {
    /// Computes the coefficient embedding of the row vector of polynomials
    /// in a [`MatZq`] and a [`ModulusPolynomialRingZq`]. The (i, j) th entry
    /// of the matrix corresponds to the i-th coefficient
    /// of the j-th polynomial provided.
    /// It inverts the operation of [`MatPolynomialRingZq::from_coefficient_embedding`].
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
    ///     integer_mod_q::{MatZq, MatPolynomialRingZq},
    ///     traits::IntoCoefficientEmbedding,
    /// };
    ///
    /// let poly = MatPolynomialRingZq::from_str("[[3  17 3 -5, 2  1 2]] / 4  1 2 3 4 mod 19").unwrap();
    /// let embedding = poly.into_coefficient_embedding(3);
    /// let cmp_mat = MatZq::from_str("[[17, 1],[3, 2],[-5, 0]] mod 19").unwrap();
    /// assert_eq!((cmp_mat, poly.get_mod()), embedding);
    /// ```
    ///
    /// # Panics ...
    /// - if `size` is not larger than the degree of the polynomial, i.e.
    ///     not all coefficients can be embedded.
    /// - if `self` is not a row vector
    fn into_coefficient_embedding(self, size: impl Into<i64>) -> (MatZq, ModulusPolynomialRingZq) {
        assert!(
            self.is_row_vector(),
            "This is no valid input, since the matrix is no row vector."
        );
        let size = size.into();

        let mut poly: Vec<PolynomialRingZq> = Vec::new();
        for i in 0..self.get_num_columns() {
            let entry: PolynomialRingZq = self.get_entry(0, i).unwrap();
            let length = entry.get_degree() + 1;
            assert!(
                size >= length,
                "The polynomial can not be embedded in the vector, \
                as the length of the polynomial ({length}) is larger than \
                the provided size ({size})."
            );
            poly.push(entry);
        }
        let mut out = MatZq::new(size, poly.len(), self.get_mod().get_q());

        for (i, entry) in poly.iter().enumerate() {
            for j in 0..size {
                match GetCoefficient::<Zq>::get_coeff(entry, j) {
                    Ok(value) => out.set_entry(j, i, value).unwrap(),
                    Err(_) => break,
                }
            }
        }

        (out, self.get_mod())
    }
}

impl FromCoefficientEmbedding<(&MatZq, &ModulusPolynomialRingZq)> for MatPolynomialRingZq {
    /// Computes a row vector of polynomials from a matrix and a modulus.
    /// The j-th entry of the i-th column vector is taken
    /// as the coefficient of the polynomial of the i-th polynomial.
    /// It inverts the operation of
    /// [`MatPolynomialRingZq::into_coefficient_embedding`](#method.into_coefficient_embedding).
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
    ///     integer_mod_q::{MatZq, MatPolynomialRingZq, ModulusPolynomialRingZq},
    ///     traits::FromCoefficientEmbedding,
    /// };
    ///
    /// let matrix = MatZq::from_str("[[17, 1],[3, 2],[-5, 3]] mod 19").unwrap();
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 2 3 4 mod 19").unwrap();
    /// let mat = MatPolynomialRingZq::from_coefficient_embedding((&matrix, &modulus));
    /// let cmp_mat = MatPolynomialRingZq::from_str("[[3  17 3 -5, 3  1 2 3]] / 4  1 2 3 4 mod 19").unwrap();
    /// assert_eq!(cmp_mat, mat);
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli mismatch.
    fn from_coefficient_embedding(embedding: (&MatZq, &ModulusPolynomialRingZq)) -> Self {
        assert_eq!(
            Z::from(embedding.0.get_mod()),
            embedding.1.get_q(),
            "This is no valid embedding, since the integer moduli of matrix and modulus mismatch."
        );
        let mut out = MatPolynomialRingZq::new(1, embedding.0.get_num_columns(), embedding.1);

        for i in 0..embedding.0.get_num_columns() {
            let col_vec = embedding.0.get_column(i).unwrap();
            let entry = PolynomialRingZq::from_coefficient_embedding((&col_vec, embedding.1));
            out.set_entry(0, i, entry).unwrap();
        }
        out
    }
}

#[cfg(test)]
mod test_into_coefficient_embedding_from_matrix {
    use crate::{
        integer_mod_q::{MatPolynomialRingZq, MatZq},
        traits::Concatenate,
    };
    use std::str::FromStr;

    /// Ensure that the initialization of the identity matrix works.
    #[test]
    fn standard_basis() {
        let standard_basis = MatPolynomialRingZq::from_str(
            "[[1  1, 2  0 1, 3  0 0 1],[1  1, 2  0 1, 3  0 0 1]] / 4  1 2 3 4 mod 17",
        )
        .unwrap();

        let basis = standard_basis.into_coefficient_embedding_from_matrix(3);

        assert_eq!(
            MatZq::identity(3, 3, 17)
                .concat_vertical(&MatZq::identity(3, 3, 17))
                .unwrap(),
            basis.0
        );

        assert_eq!(standard_basis.get_mod(), basis.1);
    }

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let poly = MatPolynomialRingZq::from_str(&format!(
            "[[3  17 {} {}, 1  1],[1  1, 2  0 1]] / 4  1 2 3 4 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        let matrix = poly.into_coefficient_embedding_from_matrix(3);

        let cmp_matrix = MatZq::from_str(&format!(
            "[[17, 1],[{}, 0],[{}, 0]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap()
        .concat_vertical(&MatZq::identity(3, 2, u64::MAX))
        .unwrap();
        assert_eq!((cmp_matrix, poly.get_mod()), matrix);
    }

    /// Ensure that the function panics if the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small() {
        let poly =
            MatPolynomialRingZq::from_str("[[3  17 5 7, 2  0 1],[1  1, 1  1]] / 4  1 2 3 4 mod 19")
                .unwrap();

        let _ = poly.into_coefficient_embedding_from_matrix(2);
    }
}

#[cfg(test)]
mod test_from_coefficient_embedding_to_matrix {
    use crate::integer_mod_q::{MatPolynomialRingZq, MatZq, ModulusPolynomialRingZq};
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let matrix = MatZq::from_str(&format!(
            "[[17, 0],[{}, -1],[{}, 0]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 2 3 4 mod {}", u64::MAX)).unwrap();

        let poly =
            MatPolynomialRingZq::from_coefficient_embedding_to_matrix((&matrix, &modulus), 1);

        let cmp_poly = MatPolynomialRingZq::from_str(&format!(
            "[[1  17, 0],[1  {}, 1  -1],[1  {}, 0]] / 4  1 2 3 4 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_poly, poly);
    }

    /// Ensure that the function panics if the provided degree does not divide
    /// the number of rows of the embedding.
    #[test]
    #[should_panic]
    fn degree_not_dividing() {
        let matrix = MatZq::from_str(&format!(
            "[[17, 0],[{}, -1],[{}, 0]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 2 3 4 mod {}", u64::MAX)).unwrap();

        let _ = MatPolynomialRingZq::from_coefficient_embedding_to_matrix((&matrix, &modulus), 2);
    }

    /// Ensure that the function panics if the moduli mismatch.
    #[test]
    #[should_panic]
    fn mismatching_moduli() {
        let matrix = MatZq::from_str(&format!(
            "[[17, 0],[{}, -1],[{}, 0]] mod 17",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 2 3 4 mod {}", u64::MAX)).unwrap();

        let _ = MatPolynomialRingZq::from_coefficient_embedding_to_matrix((&matrix, &modulus), 3);
    }
}

#[cfg(test)]
mod test_into_coefficient_embedding {
    use crate::{
        integer_mod_q::{MatPolynomialRingZq, MatZq},
        traits::IntoCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the doc test works.
    #[test]
    fn doc_test() {
        let poly =
            MatPolynomialRingZq::from_str("[[3  17 3 -5, 2  1 2]] / 4  1 2 3 4 mod 19").unwrap();
        let embedding = poly.into_coefficient_embedding(3);
        let cmp_mat = MatZq::from_str("[[17, 1],[3, 2],[-5, 0]] mod 19").unwrap();
        assert_eq!((cmp_mat, poly.get_mod()), embedding);
    }

    /// Ensure that the initialization of the identity matrix works.
    #[test]
    fn standard_basis() {
        let standard_basis =
            MatPolynomialRingZq::from_str("[[1  1, 2  0 1]] / 3  1 2 3 mod 17").unwrap();

        let basis = standard_basis.into_coefficient_embedding(3);

        assert_eq!((MatZq::identity(3, 2, 17), standard_basis.get_mod()), basis);
    }

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let poly = MatPolynomialRingZq::from_str(&format!(
            "[[3  17 {} {}, 1  1]] / 4  1 2 3 4 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        let matrix = poly.into_coefficient_embedding(3);

        let cmp_matrix = MatZq::from_str(&format!(
            "[[17, 1],[{}, 0],[{}, 0]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!((cmp_matrix, poly.get_mod()), matrix);
    }

    /// Ensure that the function panics if the the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small() {
        let poly =
            MatPolynomialRingZq::from_str("[[3  17 5 7, 2  0 1]] / 4  1 2 3 4 mod 19").unwrap();

        let _ = poly.into_coefficient_embedding(2);
    }

    /// Ensure that the function panics if the the provided vector is not a row vector.
    #[test]
    #[should_panic]
    fn not_row_vector() {
        let poly = MatPolynomialRingZq::from_str(
            "[[3  17 5 7, 2  0 1], [3  17 5 7, 2  0 1]] / 4  1 2 3 4 mod 19",
        )
        .unwrap();

        let _ = poly.into_coefficient_embedding(3);
    }
}

#[cfg(test)]
mod test_from_coefficient_embedding {
    use crate::{
        integer_mod_q::{MatPolynomialRingZq, MatZq, ModulusPolynomialRingZq},
        traits::FromCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let matrix = MatZq::from_str(&format!(
            "[[17, 0],[{}, -1],[{}, 0]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 2 3 4 mod {}", u64::MAX)).unwrap();

        let poly = MatPolynomialRingZq::from_coefficient_embedding((&matrix, &modulus));

        let cmp_poly = MatPolynomialRingZq::from_str(&format!(
            "[[3  17 {} {}, 2  0 -1]] / 4  1 2 3 4 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_poly, poly);
    }

    /// Ensure that the function panics if the moduli mismatch.
    #[test]
    #[should_panic]
    fn mismatching_moduli() {
        let matrix = MatZq::from_str(&format!(
            "[[17, 0],[{}, -1],[{}, 0]] mod 17",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 2 3 4 mod {}", u64::MAX)).unwrap();

        let _ = MatPolynomialRingZq::from_coefficient_embedding((&matrix, &modulus));
    }
}
