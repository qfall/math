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
    integer::{PolyOverZ, Z},
    integer_mod_q::{MatZq, ModulusPolynomialRingZq},
    traits::{
        FromCoefficientEmbedding, GetCoefficient, GetEntry, GetNumColumns, GetNumRows,
        IntoCoefficientEmbedding, SetCoefficient, SetEntry,
    },
};

impl IntoCoefficientEmbedding<(MatZq, ModulusPolynomialRingZq)> for &MatPolynomialRingZq {
    /// Computes the coefficient embedding of a matrix of polynomials
    /// in a [`MatZq`] and a [`ModulusPolynomialRingZq`].
    /// Each column vector of polynomials is embedded into `size` many
    /// row vectors of coefficients. The first one containing their
    /// coefficients of degree 0, and the last one their coefficients
    /// of degree `size - 1`.
    /// It inverts the operation of [`MatPolynomialRingZq::from_coefficient_embedding`].
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
    ///     traits::IntoCoefficientEmbedding,
    /// };
    ///
    /// let poly = MatPolynomialRingZq::from_str("[[1  1, 2  1 2],[1  -1, 2  -1 -2]] / 3  1 2 3 mod 17").unwrap();
    /// let embedding = poly.into_coefficient_embedding(2);
    /// let cmp_mat = MatZq::from_str("[[1, 1],[0, 2],[-1, -1],[0, -2]] mod 17").unwrap();
    /// assert_eq!((cmp_mat, poly.get_mod()), embedding);
    /// ```
    ///
    /// # Panics ...
    /// - if `size` is not larger than the degree of the polynomial, i.e.
    ///     not all coefficients can be embedded.
    fn into_coefficient_embedding(self, size: impl Into<i64>) -> (MatZq, ModulusPolynomialRingZq) {
        let size = size.into();
        let num_rows = self.get_num_rows();
        let num_columns = self.get_num_columns();

        let mut out = MatZq::new(num_rows * size, num_columns, self.modulus.get_q());

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
        println!("{}", out);
        (out, self.get_mod())
    }
}

impl FromCoefficientEmbedding<(&MatZq, &ModulusPolynomialRingZq, i64)> for MatPolynomialRingZq {
    /// Computes a [`MatPolynomialRingZq`] from a coefficient embedding.
    /// Interprets the first `degree + 1` many rows of the matrix as the
    /// coefficients of the first row of polynomials. The first one containing
    /// their coefficients of degree 0, and the last one their coefficients
    /// of degree `degree`. It inverts the operation of
    /// [`MatPolynomialRingZq::into_coefficient_embedding`](#method.into_coefficient_embedding).
    ///
    /// Parameters:
    /// - `embedding`: the coefficient matrix, the modulus, and the maximal
    ///   degree of the polynomials (defines how the matrix is split)
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
    /// let matrix = MatZq::from_str("[[17, 1],[3, 2],[-5, 3],[1, 2]] mod 19").unwrap();
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 2 3 4 mod 19").unwrap();
    /// let mat = MatPolynomialRingZq::from_coefficient_embedding((&matrix, &modulus, 1));
    /// let cmp_mat = MatPolynomialRingZq::from_str("[[2  17 3, 2  1 2],[2  -5 1, 2  3 2]] / 4  1 2 3 4 mod 19").unwrap();
    /// assert_eq!(cmp_mat, mat);
    /// ```
    ///
    /// # Panics ...
    /// - if `degree`+1 does not divide the number of rows of the embedding.
    /// - if the moduli mismatch.
    fn from_coefficient_embedding(embedding: (&MatZq, &ModulusPolynomialRingZq, i64)) -> Self {
        let degree = embedding.2;
        let num_rows = embedding.0.get_num_rows();
        let num_columns = embedding.0.get_num_columns();

        assert_eq!(
            num_rows % (degree+1),
            0,
            "The provided degree of polynomials ({degree}) +1 must divide the number of rows of the embedding ({}).",
            num_rows
        );
        assert_eq!(
            Z::from(embedding.0.get_mod()),
            embedding.1.get_q(),
            "This is no valid embedding, since the integer moduli of matrix and modulus mismatch."
        );

        let mut out = MatPolynomialRingZq::new(num_rows / (degree + 1), num_columns, embedding.1);

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

        out.reduce();
        out
    }
}

#[cfg(test)]
mod test_into_coefficient_embedding {
    use crate::{
        integer_mod_q::{MatPolynomialRingZq, MatZq},
        traits::{Concatenate, IntoCoefficientEmbedding},
    };
    use std::str::FromStr;

    /// Ensure that the initialization of the identity matrix works.
    #[test]
    fn standard_basis() {
        let standard_basis = MatPolynomialRingZq::from_str(
            "[[1  1, 2  0 1, 3  0 0 1],[1  1, 2  0 1, 3  0 0 1]] / 4  1 2 3 4 mod 17",
        )
        .unwrap();

        let basis = standard_basis.into_coefficient_embedding(3);

        assert_eq!(
            MatZq::identity(3, 3, 17)
                .concat_vertical(&MatZq::identity(3, 3, 17))
                .unwrap(),
            basis.0
        );

        assert_eq!(standard_basis.get_mod(), basis.1);
    }

    /// Ensure that the initialization of the identity matrix works.
    #[test]
    fn standard_basis_vector() {
        let standard_basis =
            MatPolynomialRingZq::from_str("[[1  1, 2  0 1]] / 3  1 2 3 mod 17").unwrap();

        let basis = standard_basis.into_coefficient_embedding(3);

        assert_eq!((MatZq::identity(3, 2, 17), standard_basis.get_mod()), basis);
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

        let matrix = poly.into_coefficient_embedding(3);

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

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries_vector() {
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

    /// Ensure that the function panics if the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small() {
        let poly =
            MatPolynomialRingZq::from_str("[[3  17 5 7, 2  0 1],[1  1, 1  1]] / 4  1 2 3 4 mod 19")
                .unwrap();

        let _ = poly.into_coefficient_embedding(2);
    }

    /// Ensure that the function panics if the the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small_vector() {
        let poly =
            MatPolynomialRingZq::from_str("[[3  17 5 7, 2  0 1]] / 4  1 2 3 4 mod 19").unwrap();

        let _ = poly.into_coefficient_embedding(2);
    }
}

#[cfg(test)]
mod test_from_coefficient_embedding {
    use crate::integer_mod_q::{MatPolynomialRingZq, MatZq, ModulusPolynomialRingZq};
    use crate::traits::FromCoefficientEmbedding;
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

        let poly = MatPolynomialRingZq::from_coefficient_embedding((&matrix, &modulus, 0));

        let cmp_poly = MatPolynomialRingZq::from_str(&format!(
            "[[1  17, 0],[1  {}, 1  -1],[1  {}, 0]] / 4  1 2 3 4 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_poly, poly);
    }

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries_vector() {
        let matrix = MatZq::from_str(&format!(
            "[[17, 0],[{}, -1],[{}, 0]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 2 3 4 mod {}", u64::MAX)).unwrap();

        let poly = MatPolynomialRingZq::from_coefficient_embedding((&matrix, &modulus, 2));

        let cmp_poly = MatPolynomialRingZq::from_str(&format!(
            "[[3  17 {} {}, 2  0 -1]] / 4  1 2 3 4 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_poly, poly);
    }

    /// Ensure that the function panics if the provided degree +1 does not divide
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

        let _ = MatPolynomialRingZq::from_coefficient_embedding((&matrix, &modulus, 1));
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

        let _ = MatPolynomialRingZq::from_coefficient_embedding((&matrix, &modulus, 3));
    }
}
