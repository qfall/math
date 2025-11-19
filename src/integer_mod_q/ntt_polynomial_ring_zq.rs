// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`NTTPolynomialRingZq`] containts the NTT representations of polynomials.

use crate::{integer::Z, integer_mod_q::mat_ntt_polynomial_ring_zq::print_vec_z};
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
/// use qfall_math::integer_mod_q::{Modulus, PolynomialRingZq, NTTPolynomialRingZq, ModulusPolynomialRingZq};
/// use std::str::FromStr;
///
/// // sample random polynomial
/// let rnd = NTTPolynomialRingZq::sample_uniform(4, 257);
/// // or instantiate polynomial from PolynomialRingZq (or PolyOverZq)
/// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
/// modulus.set_ntt_unchecked(64);
/// let poly_ring = PolynomialRingZq::sample_uniform(&modulus);
/// let ntt_poly_ring = NTTPolynomialRingZq::from(&poly_ring);
///
/// // multiply, add and subtract objects
/// let mod_q = Modulus::from(modulus.get_q());
/// let mut tmp_ntt = ntt_poly_ring.mul(&rnd, &mod_q);
/// tmp_ntt.add_assign(&rnd, &mod_q);
/// tmp_ntt.sub_assign(&rnd, &mod_q);
///
/// // Return to PolynomialRingZq
/// let res = PolynomialRingZq::from((tmp_ntt, &modulus));
/// ```
#[derive(PartialEq, Eq, Serialize, Deserialize, Display, Clone)]
#[display("{}", print_vec_z(&self.poly))]
pub struct NTTPolynomialRingZq {
    pub poly: Vec<Z>,
}

impl fmt::Debug for NTTPolynomialRingZq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let short_print = print_vec_z(&self.poly);
        let a: Vec<&str> = short_print.split_whitespace().collect();
        let short_print = format!("{}{} ..., {}{}", a[0], a[1], a[a.len() - 2], a[a.len() - 1]);

        write!(
            f,
            "NTTPolynomialRingZq {{poly: {}, storage: {{poly: {:?}}}}}",
            short_print, self.poly
        )
    }
}
