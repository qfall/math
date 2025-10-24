// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`NTTPolynomialRingZq`] containts the NTT representations of polynomials.

use crate::integer::Z;
use derive_more::Display;
use serde::{Deserialize, Serialize};
use std::fmt;

mod arithmetic;
mod from;
mod sample;

/// [`NTTPolynomialRingZq`] contains the NTT representation of some polynomial with respect to
/// a [`NTTBasisPolynomialRingZq`](super::NTTBasisPolynomialRingZq) that itself isn't aware of.
///
/// Attributes
/// - `poly`: holds the coefficients
///
/// # Examples
/// ```
/// 
/// ```
/// TODO
#[derive(PartialEq, Eq, Serialize, Deserialize, Display, Clone)]
#[display("{:?}", {let x: Vec<String> = poly.iter().map(|x| x.to_string()).collect(); x})]
pub struct NTTPolynomialRingZq {
    pub poly: Vec<Z>,
}

impl fmt::Debug for NTTPolynomialRingZq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PolynomialRingZq {{poly: {:?}, storage: {{poly: {:?}}}}}",
            self.poly, self.poly
        )
    }
}
