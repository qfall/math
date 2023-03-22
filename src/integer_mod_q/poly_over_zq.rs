// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`PolyOverZq`] is a type of polynomial with arbitrarily many coefficients of type
//! [`Zq`](crate::integer_mod_q::Zq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use super::modulus::Modulus;
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_struct;

mod cmp;
mod from;
mod get;
mod ownership;
mod properties;
mod set;
mod to_string;

/// [`PolyOverZq`] is a type of polynomial with arbitrarily many coefficients of type
/// [`Zq`](crate::integer_mod_q::Zq).
///
// Attributes:
// - `poly`: holds the content of the polynomial
// - `modulus`: holds the value of the modulus
//
/// # Example
/// ```
/// use math::integer_mod_q::PolyOverZq;
/// use std::str::FromStr;
///
/// let poly = PolyOverZq::from_str("4  0 1 -2 3 mod 42").unwrap();
/// ```
#[derive(Debug)]
pub struct PolyOverZq {
    pub(crate) poly: fmpz_mod_poly_struct,
    pub(crate) modulus: Modulus,
}
