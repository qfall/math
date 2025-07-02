// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to transform a [`ModulusPolynomialRingZq`]
//! into a [`MatZq`] and reverse by using the coefficient embedding.

use crate::{
    integer::Z,
    integer_mod_q::{MatZq, ModulusPolynomialRingZq, PolyOverZq},
    traits::{FromCoefficientEmbedding, GetCoefficient, IntoCoefficientEmbedding, MatrixSetEntry},
};

impl IntoCoefficientEmbedding<MatZq> for &ModulusPolynomialRingZq {
    /// Computes the coefficient embedding of the polynomial
    /// in a [`MatZq`] as a column vector, where the i-th entry
    /// of the vector corresponds to the i-th coefficient.
    /// It inverts the operation of [`ModulusPolynomialRingZq::from_coefficient_embedding`].
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
    ///     integer_mod_q::{MatZq, ModulusPolynomialRingZq},
    ///     traits::IntoCoefficientEmbedding,
    /// };
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("3  17 3 -5 mod 19").unwrap();
    /// let vector = poly.into_coefficient_embedding(4);
    /// let cmp_vector = MatZq::from_str("[[17],[3],[-5],[0]] mod 19").unwrap();
    /// assert_eq!(cmp_vector, vector);
    /// ```
    ///
    /// # Panics ...
    /// - if `size` is not larger than the degree of the polynomial, i.e.
    ///   not all coefficients can be embedded.
    fn into_coefficient_embedding(self, size: impl Into<i64>) -> MatZq {
        let size = size.into();
        let length = self.get_degree() + 1;
        assert!(
            size >= length,
            "The polynomial can not be embedded in the vector, \
            as the length of the polynomial ({length}) is larger than \
            the provided size ({size})."
        );
        let mut out = MatZq::new(size, 1, self.get_q());
        for j in 0..size {
            let coeff: Z = unsafe { self.get_coeff_unchecked(j) };
            unsafe { out.set_entry_unchecked(j, 0, coeff) };
        }
        out
    }
}

impl FromCoefficientEmbedding<&MatZq> for ModulusPolynomialRingZq {
    /// Computes a polynomial from a vector.
    /// The first i-th entry of the column vector is taken
    /// as the coefficient of the polynomial.
    /// It inverts the operation of
    /// [`ModulusPolynomialRingZq::into_coefficient_embedding`](#method.into_coefficient_embedding).
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
    ///     integer_mod_q::{MatZq, ModulusPolynomialRingZq},
    ///     traits::FromCoefficientEmbedding,
    /// };
    ///
    /// let vector = MatZq::from_str("[[17],[3],[-5]] mod 19").unwrap();
    /// let poly = ModulusPolynomialRingZq::from_coefficient_embedding(&vector);
    /// let cmp_poly = ModulusPolynomialRingZq::from_str("3  17 3 -5 mod 19").unwrap();
    /// assert_eq!(cmp_poly, poly);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided embedding is not a column vector.
    fn from_coefficient_embedding(embedding: &MatZq) -> Self {
        ModulusPolynomialRingZq::from(PolyOverZq::from_coefficient_embedding(embedding))
    }
}

#[cfg(test)]
mod test_into_coefficient_embedding {
    use crate::{
        integer_mod_q::{MatZq, ModulusPolynomialRingZq},
        traits::IntoCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let poly = ModulusPolynomialRingZq::from_str(&format!(
            "3  17 {} {} mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        let vector = poly.into_coefficient_embedding(3);

        let cmp_vector = MatZq::from_str(&format!(
            "[[17],[{}],[{}]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_vector, vector);
    }

    /// Ensure that the function panics if the the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small() {
        let poly = ModulusPolynomialRingZq::from_str("3  17 1 2 mod 19").unwrap();

        let _ = poly.into_coefficient_embedding(2);
    }
}

#[cfg(test)]
mod test_from_coefficient_embedding {
    use crate::{
        integer_mod_q::{MatZq, ModulusPolynomialRingZq},
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

        let poly = ModulusPolynomialRingZq::from_coefficient_embedding(&vector);

        let cmp_poly = ModulusPolynomialRingZq::from_str(&format!(
            "3  17 {} {} mod {}",
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

        let _ = ModulusPolynomialRingZq::from_coefficient_embedding(&vector);
    }
}
