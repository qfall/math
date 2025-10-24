// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`NTTPolynomialRingZq`] containts the NTT representations of polynomials.

use crate::integer_mod_q::NTTPolynomialRingZq;
use derive_more::Display;
use serde::{Deserialize, Serialize};
use std::fmt;

mod arithmetic;
mod from;
mod get;
mod sample;

/// [`NTTPolynomialRingZq`] contains the NTT representation of some polynomial with respect to
/// a [`NTTBasisPolynomialRingZq`](super::NTTBasisPolynomialRingZq) that itself isn't aware of.
///
/// Any polynomial in NTT representation in row `i` and column `j` can be accessed via `matrix[j][i]`.
///
/// Attributes
/// - `mat`: holds the matrix entries with its coefficients
///
/// # Examples
/// ```
///
/// ```
/// TODO
#[derive(PartialEq, Eq, Serialize, Deserialize, Display, Clone)]
#[display("{:?}", {let x: Vec<String> = matrix.iter().map(|x| x.iter().map(|y| y.to_string()).collect()).collect(); x})]
pub struct MatNTTPolynomialRingZq {
    pub matrix: Vec<Vec<NTTPolynomialRingZq>>,
}

impl fmt::Debug for MatNTTPolynomialRingZq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PolynomialRingZq {{poly: {:?}, storage: {{poly: {:?}}}}}",
            self.matrix, self.matrix
        )
    }
}
