// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`MatNTTPolynomialRingZq`] containts the NTT representations of matrices over polynomials.

use crate::integer::Z;
use derive_more::Display;
use serde::{Deserialize, Serialize};
use std::fmt;

mod arithmetic;
mod from;
mod get;
mod sample;

/// [`MatNTTPolynomialRingZq`] contains the NTT representation of a matrix over polynomials with respect to
/// a [`NTTBasisPolynomialRingZq`](super::NTTBasisPolynomialRingZq) that itself isn't aware of.
///
/// Any polynomial in NTT representation in row `i` and column `j` can be accessed via `matrix[j * nr_columns + i]`.
///
/// Attributes
/// - `matrix`: holds the matrix entries with its coefficients
///
/// # Examples
/// ```
/// use qfall_math::integer_mod_q::{Modulus, MatPolynomialRingZq, MatNTTPolynomialRingZq, ModulusPolynomialRingZq};
/// use std::str::FromStr;
///
/// // sample random matrix
/// let mat_rnd = MatNTTPolynomialRingZq::sample_uniform(2, 2, 4, 257);
/// // or instantiate matrix from MatPolynomialRingZq
/// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
/// modulus.set_ntt_unchecked(64);
/// let mat_poly_ring = MatPolynomialRingZq::identity(2, 2, &modulus);
/// let mat_ntt_poly_ring = MatNTTPolynomialRingZq::from(&mat_poly_ring);
///
/// // multiply, add and subtract objects
/// let mod_q = Modulus::from(modulus.get_q());
/// let mut tmp_mat_ntt = mat_ntt_poly_ring.mul(&mat_rnd, &mod_q);
/// tmp_mat_ntt.add_assign(&mat_rnd, &mod_q);
/// tmp_mat_ntt.sub_assign(&mat_rnd, &mod_q);
///
/// // Return to MatPolynomialRingZq
/// let res = MatPolynomialRingZq::from((&mut tmp_mat_ntt, &modulus));
/// ```
#[derive(PartialEq, Eq, Serialize, Deserialize, Display, Clone)]
#[display("{:?}", {let x: Vec<String> = matrix.iter().map(|x| x.to_string()).collect(); x})]
pub struct MatNTTPolynomialRingZq {
    pub matrix: Vec<Z>,
    pub d: usize, // modulus degree
    pub nr_rows: usize,
    pub nr_columns: usize,
}

impl fmt::Debug for MatNTTPolynomialRingZq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "MatNTTPolynomialRingZq {{matrix: {:?}, d: {}, nr_rows: {}, nr_columns: {} storage: {{poly: {:?}}}}}",
            self.matrix, self.d, self.nr_rows, self.nr_columns, self.matrix
        )
    }
}
