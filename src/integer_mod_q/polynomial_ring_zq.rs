// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`PolynomialRingZq`] is a type of ring over PolyOverZq/f(X).
//! Where f(X) is a [`PolyOverZq`](crate::integer_mod_q::PolyOverZq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.
//!
//! **For Developers**: The [`ModulusPolynomialRingZq`] is not applied automatically, and
//! has to be called in the functions individually. Additionally the comparisons
//! assume that the entries are reduced, hence not reduction is performed in the check.
//!
//! The DEVELOPER has to call the [`PolynomialRingZq::reduce`], whenever
//! a computation may exceed the modulus, because it is not reduced automatically

use super::ModulusPolynomialRingZq;
use crate::integer::PolyOverZ;
use serde::{Deserialize, Serialize};

mod arithmetic;
mod from;
mod reduce;

/// [`PolynomialRingZq`] represents polynomials over the finite field
/// [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)/f(X) where `q` is prime and f(X) is a polynomial over [`Zq`](super::Zq).
///
/// Attributes
/// - `poly`: holds the value
/// - `modulus`: holds the prime `q` and f(X)
///
/// # Examples
#[derive(PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct PolynomialRingZq {
    poly: PolyOverZ,
    modulus: ModulusPolynomialRingZq,
}
