// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to transform a [`PolynomialRingZq`]
//! into a [`MatZq`] and a [`ModulusPolynomialRingZq`] and reverse by using the coefficient embedding.

use crate::{
    integer::Z,
    integer_mod_q::{MatZq, ModulusPolynomialRingZq, PolynomialRingZq},
    traits::{
        FromCoefficientEmbedding, GetCoefficient, IntoCoefficientEmbedding, MatrixDimensions,
        MatrixGetEntry, MatrixSetEntry, SetCoefficient,
    },
};

impl IntoCoefficientEmbedding<(MatZq, ModulusPolynomialRingZq)> for &PolynomialRingZq {
    /// Computes the coefficient embedding of the polynomial
    /// in a [`MatZq`] as a column vector, where the i-th entry
    /// of the vector corresponds to the i-th coefficient, and a
    /// [`ModulusPolynomialRingZq`].
    /// It inverts the operation of [`PolynomialRingZq::from_coefficient_embedding`].
    ///
    /// The representation of the polynomials in the embedding is in the range `[0, modulus_polynomial)`.
    ///
    /// Parameters:
    /// - `size`: determines the number of rows of the embedding. It has to be larger
    ///   than the degree of the polynomial.
    ///
    /// Returns a coefficient embedding as a column vector if `size` is large enough.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::{
    ///     integer_mod_q::{MatZq, PolynomialRingZq},
    ///     traits::IntoCoefficientEmbedding,
    /// };
    ///
    /// let poly = PolynomialRingZq::from_str("2  1 -2 / 3  17 3 5 mod 19").unwrap();
    /// let embedding = poly.into_coefficient_embedding(3);
    /// let cmp_vector = MatZq::from_str("[[1],[-2],[0]] mod 19").unwrap();
    /// assert_eq!((cmp_vector, poly.get_mod()), embedding);
    /// ```
    ///
    /// # Panics ...
    /// - if `size` is not larger than the degree of the polynomial, i.e.
    ///   not all coefficients can be embedded.
    fn into_coefficient_embedding(self, size: impl Into<i64>) -> (MatZq, ModulusPolynomialRingZq) {
        let size = size.into();
        let length = self.get_degree() + 1;
        assert!(
            size >= length,
            "The polynomial can not be embedded in the vector, \
            as the length of the polynomial ({length}) is larger than \
            the provided size ({size})."
        );
        let mut out = MatZq::new(size, 1, self.modulus.get_q());
        for j in 0..size {
            let coeff: Z = unsafe { self.get_coeff_unchecked(j) };
            unsafe { out.set_entry_unchecked(j, 0, coeff) };
        }

        (out, self.modulus.clone())
    }
}

impl FromCoefficientEmbedding<(&MatZq, &ModulusPolynomialRingZq)> for PolynomialRingZq {
    /// Computes a polynomial of degree `n-1` from a column vector of size `n` and a modulus.
    /// The i-th entry of the column vector is taken
    /// as the i-th coefficient of the polynomial.
    /// It inverts the operation of
    /// [`PolynomialRingZq::into_coefficient_embedding`](#method.into_coefficient_embedding).
    ///
    /// Parameters:
    /// - `embedding`: the column vector that encodes the embedding and the modulus of the resulting polynomial
    ///
    /// Returns a polynomial that corresponds to the embedding.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::{
    ///     integer_mod_q::{MatZq, PolynomialRingZq, ModulusPolynomialRingZq},
    ///     traits::FromCoefficientEmbedding,
    /// };
    ///
    /// let vector = MatZq::from_str("[[17],[3],[-5]] mod 19").unwrap();
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 2 3 4 mod 19").unwrap();
    /// let poly = PolynomialRingZq::from_coefficient_embedding((&vector, &modulus));
    /// let cmp_poly = PolynomialRingZq::from_str("3  17 3 -5 / 4  1 2 3 4 mod 19").unwrap();
    /// assert_eq!(cmp_poly, poly);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided embedding is not a column vector.
    /// - if the moduli mismatch.
    fn from_coefficient_embedding(embedding: (&MatZq, &ModulusPolynomialRingZq)) -> Self {
        assert!(
            embedding.0.is_column_vector(),
            "This is no valid embedding, since the matrix is no column vector."
        );
        assert_eq!(
            Z::from(embedding.0.get_mod()),
            embedding.1.get_q(),
            "This is no valid embedding, since the integer moduli of matrix and modulus mismatch."
        );
        let mut out = PolynomialRingZq::from((0, embedding.1));
        for i in 0..embedding.0.get_num_rows() {
            let entry: Z = unsafe { embedding.0.get_entry_unchecked(i, 0) };
            out.set_coeff(i, &entry).unwrap()
        }
        out
    }
}

#[cfg(test)]
mod test_into_coefficient_embedding {
    use crate::{
        integer_mod_q::{MatZq, PolynomialRingZq},
        traits::IntoCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let poly = PolynomialRingZq::from_str(&format!(
            "3  17 {} {} / 4  1 2 3 4 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        let embedding = poly.into_coefficient_embedding(3);

        let cmp_vector = MatZq::from_str(&format!(
            "[[17],[{}],[{}]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!((cmp_vector, poly.modulus), embedding);
    }

    /// Ensure that zero is embedded correctly.
    #[test]
    fn test_zero() {
        let poly = PolynomialRingZq::from_str("0 / 3  17 3 5 mod 19").unwrap();
        let embedding = poly.into_coefficient_embedding(1);

        let cmp_vector = MatZq::from_str("[[0]] mod 19").unwrap();
        assert_eq!((cmp_vector, poly.get_mod()), embedding);
    }

    /// Ensure that the function panics if the the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small() {
        let poly = PolynomialRingZq::from_str("3  17 1 2 / 4  1 2 3 4 mod 19").unwrap();

        let _ = poly.into_coefficient_embedding(2);
    }
}

#[cfg(test)]
mod test_from_coefficient_embedding {
    use crate::{
        integer_mod_q::{MatZq, ModulusPolynomialRingZq, PolynomialRingZq},
        traits::FromCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let vector = MatZq::from_str(&format!(
            "[[17],[{}],[{}]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 2 3 4 mod {}", u64::MAX)).unwrap();

        let poly = PolynomialRingZq::from_coefficient_embedding((&vector, &modulus));

        let cmp_poly = PolynomialRingZq::from_str(&format!(
            "3  17 {} {} / 4  1 2 3 4 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_poly, poly);
    }

    /// Ensure that the function panics if the provided matrix is not a column vector.
    #[test]
    #[should_panic]
    fn not_column_vector() {
        let vector = MatZq::from_str("[[17, 1],[-17, -1],[5, 9]] mod 42").unwrap();
        let modulus = ModulusPolynomialRingZq::from_str("4  1 2 3 4 mod 42").unwrap();

        let _ = PolynomialRingZq::from_coefficient_embedding((&vector, &modulus));
    }

    /// Ensure that the function panics if the moduli mismatch.
    #[test]
    #[should_panic]
    fn mismatching_moduli() {
        let vector = MatZq::from_str("[[17],[-1],[9]] mod 42").unwrap();
        let modulus = ModulusPolynomialRingZq::from_str("4  1 2 3 4 mod 33").unwrap();

        let _ = PolynomialRingZq::from_coefficient_embedding((&vector, &modulus));
    }
}
