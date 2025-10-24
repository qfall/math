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
    integer_mod_q::{MatPolynomialRingZq, NTTPolynomialRingZq},
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
    /// use std::str::FromStr;
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
    /// - if the [`NTTBasisPolynomialRingZq`](crate::integer_mod_q::NTTBasisPolynomialRingZq)
    ///   is not set.
    fn from(matrix: &MatPolynomialRingZq) -> Self {
        let width = matrix.get_num_columns();
        let height = matrix.get_num_rows();

        let mut res = Vec::with_capacity(width as usize);

        for col in 0..width {
            let mut col_vec = Vec::with_capacity(height as usize);
            for row in 0..height {
                let entry = unsafe { matrix.get_entry_unchecked(row, col) };
                let ntt_poly = NTTPolynomialRingZq::from(&entry);
                col_vec.push(ntt_poly);
            }
            res.push(col_vec);
        }

        MatNTTPolynomialRingZq { matrix: res }
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

        let ntt_matrix = MatNTTPolynomialRingZq::from(&matrix);

        let cmp_matrix = MatPolynomialRingZq::from((ntt_matrix, &modulus));

        assert_eq!(matrix, cmp_matrix);
    }
}
