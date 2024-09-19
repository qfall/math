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
//! For **DEVELOPERS**: Many functions assume that the [`PolynomialRingZq`] instances are reduced.
//! To avoid unnecessary checks and reductions, always return canonical/reduced
//! values. The end-user should be unable to obtain a non-reduced value.
//! Therefore, the DEVELOPER has to call the [`PolynomialRingZq::reduce`], whenever
//! a computation may exceed the modulus, because it is not reduced automatically

use super::ModulusPolynomialRingZq;
use crate::integer::PolyOverZ;
use derive_more::Display;
use serde::{Deserialize, Serialize};

mod arithmetic;
mod from;
mod get;
mod properties;
mod reduce;
mod sample;
mod set;

/// [`PolynomialRingZq`] represents polynomials over the finite field
/// [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)/f(X) where f(X) is a polynomial over [`Zq`](super::Zq).
///
/// Attributes
/// - `poly`: holds the value
/// - `modulus`: holds the modulus q and f(X)
///
/// # Examples
/// ```
/// # use qfall_math::error::MathError;
/// use qfall_math::integer::PolyOverZ;
/// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
/// use qfall_math::integer_mod_q::PolyOverZq;
/// use qfall_math::integer_mod_q::PolynomialRingZq;
/// use std::str::FromStr;
///
/// let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
/// let modulus = ModulusPolynomialRingZq::from(poly_mod);
///
/// // instantiation
/// let a = PolynomialRingZq::from((PolyOverZ::from(5), &modulus));
/// let b = PolynomialRingZq::from((PolyOverZ::from_str("2  1 5").unwrap(), &modulus));
/// let _ = a.clone();
///
/// // arithmetics
/// let _ = &a + &b;
/// let _ = &a * &b;
///
/// // to_string incl. (de-)serialization
/// assert_eq!("1  5 / 3  1 0 1 mod 17", &a.to_string());
/// let _ = serde_json::to_string(&a).unwrap();
///
/// # Ok::<(), MathError>(())
/// ```
#[derive(PartialEq, Eq, Debug, Serialize, Deserialize, Display, Clone)]
#[display("{poly} / {modulus}")]
pub struct PolynomialRingZq {
    pub(crate) poly: PolyOverZ,
    pub(crate) modulus: ModulusPolynomialRingZq,
}
