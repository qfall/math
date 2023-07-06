// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This modules contains implementations to transform a [`PolyOverQ`]
//! into a [`MatQ`] and reverse by using the coefficient embedding.

use crate::{
    rational::{MatQ, PolyOverQ},
    traits::{
        FromCoefficientEmbedding, GetCoefficient, GetEntry, GetNumRows, IntoCoefficientEmbedding,
        SetCoefficient, SetEntry,
    },
};

impl IntoCoefficientEmbedding<MatQ> for &PolyOverQ {
    fn into_coefficient_embedding(self, size: impl Into<i64>) -> MatQ {
        let size = size.into();
        let length = self.get_degree() + 1;
        assert!(
            size >= length,
            "The polynomial can not be embedded in the vector, \
            as the length of the polynomial ({length}) is larger than \
            the provided size ({size})."
        );
        let mut out = MatQ::new(size, 1);
        for j in 0..size {
            match self.get_coeff(j) {
                Ok(value) => out.set_entry(j, 0, value).unwrap(),
                Err(_) => break,
            }
        }
        out
    }
}

impl FromCoefficientEmbedding<&MatQ> for PolyOverQ {
    fn from_coefficient_embedding(embedding: &MatQ) -> Self {
        assert!(embedding.is_column_vector());
        let mut out = PolyOverQ::default();
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
        rational::{MatQ, PolyOverQ},
        traits::IntoCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let poly = PolyOverQ::from_str(&format!("3  17/3 {}/9 {}/2", i64::MAX, i64::MIN)).unwrap();

        let vector = poly.into_coefficient_embedding(3);

        let cmp_vector =
            MatQ::from_str(&format!("[[17/3],[{}/9],[{}/2]]", i64::MAX, i64::MIN)).unwrap();
        assert_eq!(cmp_vector, vector)
    }

    /// Ensure that the function panics if the the provided size is too small.
    #[test]
    #[should_panic]
    fn size_too_small() {
        let poly = PolyOverQ::from_str("3  17/3 5/9 1/2").unwrap();

        let _ = poly.into_coefficient_embedding(2);
    }
}

#[cfg(test)]
mod test_from_coefficient_embedding {
    use crate::{
        rational::{MatQ, PolyOverQ},
        traits::FromCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the embedding works with large entries.
    #[test]
    fn large_entries() {
        let vector = MatQ::from_str(&format!("[[17/3],[{}],[{}/2]]", i64::MAX, i64::MIN)).unwrap();

        let poly = PolyOverQ::from_coefficient_embedding(&vector);

        let cmp_poly =
            PolyOverQ::from_str(&format!("3  17/3 {} {}/2", i64::MAX, i64::MIN)).unwrap();
        assert_eq!(cmp_poly, poly)
    }

    /// Ensure that the function panics if the provided matrix is not a column vector.
    #[test]
    #[should_panic]
    fn not_column_vector() {
        let vector = MatQ::from_str("[[17/3, 1],[-17, -1],[5, 9/9]]").unwrap();

        let _ = PolyOverQ::from_coefficient_embedding(&vector);
    }
}
