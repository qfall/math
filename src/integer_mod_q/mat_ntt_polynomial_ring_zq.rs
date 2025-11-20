// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`MatNTTPolynomialRingZq`] containts the NTT representations of matrices over polynomials.

use crate::{integer::Z, integer_mod_q::ModulusPolynomialRingZq};
use derive_more::Display;
use serde::{Deserialize, Serialize};
use std::fmt;

mod arithmetic;
mod cmp;
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
/// - `nr_rows`: the number of rows of the matrix
/// - `nr_columns`: the number of columns of the matrix
/// - `modulus`: the [`ModulusPolynomialRingZq`] defining the modulus `q`, the ring `Z_q[X]/f(X)`, and
///   the NTT transform [`NTTBasisPolynomialRingZq`](crate::integer_mod_q::NTTBasisPolynomialRingZq)
///
/// # Examples
/// ```
/// use qfall_math::integer_mod_q::{Modulus, MatPolynomialRingZq, MatNTTPolynomialRingZq, ModulusPolynomialRingZq};
/// use std::str::FromStr;
///
/// // setup modulus with ability to transform to NTT
/// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
/// modulus.set_ntt_unchecked(64);
///
/// // sample random matrix
/// let mat_rnd = MatNTTPolynomialRingZq::sample_uniform(2, 2, &modulus);
/// // or instantiate matrix from MatPolynomialRingZq
/// let mat_poly_ring = MatPolynomialRingZq::identity(2, 2, &modulus);
/// let mat_ntt_poly_ring = MatNTTPolynomialRingZq::from(&mat_poly_ring);
///
/// // multiply, add and subtract objects
/// let mut tmp_mat_ntt = mat_ntt_poly_ring * &mat_rnd;
/// tmp_mat_ntt += &mat_rnd;
/// tmp_mat_ntt -= &mat_rnd;
///
/// // Return to MatPolynomialRingZq
/// let res = tmp_mat_ntt.inv_ntt();
/// ```
#[derive(PartialEq, Eq, Serialize, Deserialize, Display, Clone)]
#[display("{} / {}", print_vec_z(&self.matrix), self.modulus)]
pub struct MatNTTPolynomialRingZq {
    pub matrix: Vec<Z>,
    pub nr_rows: usize,
    pub nr_columns: usize,
    pub modulus: ModulusPolynomialRingZq,
}

impl fmt::Debug for MatNTTPolynomialRingZq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let short_print = print_vec_z(&self.matrix);
        let a: Vec<&str> = short_print.split_whitespace().collect();
        let short_print = format!("{}{} ..., {}{}", a[0], a[1], a[a.len() - 2], a[a.len() - 1]);

        write!(
            f,
            "MatNTTPolynomialRingZq {{matrix: {}, nr_rows: {}, nr_columns: {}, modulus: {}, storage: {{matrix: {:?}, modulus: {:?}}}}}",
            short_print, self.nr_rows, self.nr_columns, self.modulus, self.matrix, self.modulus
        )
    }
}

/// Quick solution to print a vector of [`Z`] values in the format `[1, 2, 3, 4, 5]`.
pub(crate) fn print_vec_z(vector: &Vec<Z>) -> String {
    let mut out = String::new();
    for v in vector {
        out.push_str(&format!("{}, ", v));
    }
    // Remove last whitespace and comma
    out.pop().unwrap();
    out.pop().unwrap();
    format!("[{out}]")
}
