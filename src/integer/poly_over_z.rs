// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`PolyOverZ`] is a type of polynomial with arbitrarily many coefficients of type
//! [`Z`](crate::integer::Z)
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_poly::fmpz_poly_struct;

mod arithmetic;
mod cmp;
mod default;
mod evaluate;
mod from;
mod get;
mod ownership;
mod set;
mod to_string;

/// [`PolyOverZ`] is a type of polynomial with arbitrarily many coefficients of type
/// [`Z`](crate::integer::Z).
///
// Attributes:
// - `poly`: holds the content of the polynomial
//
/// # Example
/// ```
/// use math::integer::PolyOverZ;
/// use std::str::FromStr;
///
/// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
/// ```
#[derive(Debug)]
pub struct PolyOverZ {
    pub(crate) poly: fmpz_poly_struct,
}
