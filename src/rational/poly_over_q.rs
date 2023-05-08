// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`PolyOverQ`] is a type of polynomial with arbitrarily many coefficients of type
//! [`Q`](crate::rational::Q).
//! This implementation uses the [FLINT](https://flintlib.org/) library.
//!
//! For **DEVELOPERS**: Many functions assume that the [`PolyOverQ`] instances
//! are reduced. To avoid unnecessary checks and reductions, always return
//! canonical/reduced values. The end-user should be unable to obtain a
//! non-reduced value.

use flint_sys::fmpq_poly::fmpq_poly_struct;

mod arithmetic;
mod cmp;
mod default;
mod evaluate;
mod from;
mod get;
mod ownership;
mod serialize;
mod set;
mod to_string;

/// [`PolyOverQ`] is a type of polynomial with arbitrarily many coefficients of type
/// [`Q`](crate::rational::Q).
///
// Attributes:
// - `poly`: holds the content of the polynomial
//
/// # Examples
/// ```
/// use qfall_math::rational::{PolyOverQ, Q};
/// use qfall_math::traits::*;
/// use std::str::FromStr;
///
/// // instantiations
/// let poly_1 = PolyOverQ::from_str("4  0 1/2 2 3/4").unwrap();
/// let poly_2 = PolyOverQ::default();
///
/// // evaluate function
/// let value = Q::default();
/// let res = poly_1.evaluate(&value);
///
/// // comparison
/// assert_ne!(poly_1, poly_2);
/// ```
#[derive(Debug)]
pub struct PolyOverQ {
    pub(crate) poly: fmpq_poly_struct,
}
