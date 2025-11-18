// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatNTTPolynomialRingZq`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.

use super::MatNTTPolynomialRingZq;
use crate::{
    integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, NTTPolynomialRingZq},
    traits::{MatrixDimensions, MatrixGetEntry},
};

impl From<&MatPolynomialRingZq> for MatNTTPolynomialRingZq {
    /// Computes the NTT representation of `matrix`.
    ///
    /// Parameters:
    /// - `matrix`: the matrix that's going to be represented in NTT format.
    ///
    /// Returns the NTT representation as a [`MatNTTPolynomialRingZq`] of `matrix`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatNTTPolynomialRingZq, MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq};
    /// use crate::qfall_math::traits::SetCoefficient;
    ///
    /// let n = 4;
    /// let modulus = 7681;
    ///
    /// let mut mod_poly = PolyOverZq::from(modulus);
    /// mod_poly.set_coeff(0, 1).unwrap();
    /// mod_poly.set_coeff(n, 1).unwrap();
    ///
    /// let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);
    /// polynomial_modulus.set_ntt_unchecked(1925);
    ///
    /// let mat_poly_ring = MatPolynomialRingZq::sample_uniform(2, 3, &polynomial_modulus);
    ///
    /// let mat_ntt_poly_ring = MatNTTPolynomialRingZq::from(&mat_poly_ring);
    /// ```
    ///
    /// # Panics ...
    /// - if the [`NTTBasisPolynomialRingZq`](crate::integer_mod_q::NTTBasisPolynomialRingZq),
    ///   which is part of the [`ModulusPolynomialRingZq`] in `matrix` is not set.
    fn from(matrix: &MatPolynomialRingZq) -> Self {
        let degree = matrix.get_mod().get_degree();
        let nr_rows = matrix.get_num_rows();
        let nr_columns = matrix.get_num_columns();

        let mut res = Vec::with_capacity((degree * nr_rows * nr_columns) as usize);

        for col in 0..nr_columns {
            for row in 0..nr_rows {
                let entry = unsafe { matrix.get_entry_unchecked(row, col) };
                let mut ntt_poly = NTTPolynomialRingZq::from(&entry);
                res.append(&mut ntt_poly.poly);
            }
        }

        MatNTTPolynomialRingZq {
            matrix: res,
            d: degree as usize,
            nr_rows: nr_rows as usize,
            nr_columns: nr_columns as usize,
        }
    }
}

impl MatNTTPolynomialRingZq {
    /// Computes the inverse NTT of `self` with respect to the given `modulus`.
    ///
    /// Parameters:
    /// - `modulus`: the modulus that is applied to each polynomial.
    ///
    /// Returns a new [`MatPolynomialRingZq`] with the entries from `self`
    /// with respect to the modulus `modulus`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, MatNTTPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
    /// modulus.set_ntt_unchecked(64);
    /// let mut ntt_mat = MatNTTPolynomialRingZq::sample_uniform(1, 1, 4, 257);
    ///
    /// let poly_ring_mat = ntt_mat.inv_ntt(&modulus);
    /// ```
    ///
    /// # Panics ...
    /// - if the [`NTTBasisPolynomialRingZq`](crate::integer_mod_q::NTTBasisPolynomialRingZq) in `modulus`
    ///   is not set.
    /// - if the modulus differs from the modulus over which we view the polynomial.
    pub fn inv_ntt(&mut self, modulus: &ModulusPolynomialRingZq) -> MatPolynomialRingZq {
        MatPolynomialRingZq::from((self, modulus))
    }
}

#[cfg(test)]
mod test_from {
    use super::MatNTTPolynomialRingZq;
    use crate::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    use std::str::FromStr;

    /// Ensures that the transform to NTT representation and back works properly.
    #[test]
    fn round_trip() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);
        let matrix = MatPolynomialRingZq::sample_uniform(3, 5, &modulus);

        let mut ntt_matrix = MatNTTPolynomialRingZq::from(&matrix);

        let cmp_matrix = MatPolynomialRingZq::from((&mut ntt_matrix, &modulus));

        assert_eq!(matrix, cmp_matrix);
    }
}
