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
//!
//! For **DEVELOPERS**: Many functions assume that the [`PolyOverZq`] instances are reduced.
//! To avoid unnecessary checks and reductions, always return canonical/reduced
//! values. The end-user should be unable to obtain a non-reduced value.

use super::modulus::Modulus;
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_struct;

mod arithmetic;
mod cmp;
mod evaluate;
mod from;
mod get;
mod ownership;
mod properties;
mod serialize;
mod set;
mod to_string;

/// [`PolyOverZq`] is a type of polynomial with arbitrarily many coefficients of type
/// [`Zq`](crate::integer_mod_q::Zq).
///
// Attributes:
// - `poly`: holds the content of the polynomial
// - `modulus`: holds the value of the modulus
//
/// # Examples
/// ```
/// use qfall_math::integer::Z;
/// use qfall_math::integer_mod_q::PolyOverZq;
/// use qfall_math::traits::*;
/// use std::str::FromStr;
///
/// // instantiations
/// let poly_1 = PolyOverZq::from_str("4  0 1 2 3 mod 42").unwrap();
/// let poly_2 = poly_1.clone();
///
/// // evaluate function
/// let value = Z::from(3);
/// let res = poly_1.evaluate(&value);
///
/// // properties
/// let reducibility: bool = poly_1.is_irreducible();
///
/// // comparison
/// assert_eq!(poly_1, poly_2);
/// ```
#[derive(Debug)]
pub struct PolyOverZq {
    pub(crate) poly: fmpz_mod_poly_struct,
    pub(crate) modulus: Modulus,
}
