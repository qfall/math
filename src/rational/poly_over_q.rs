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
use std::fmt;

mod arithmetic;
mod cmp;
mod coefficient_embedding;
mod default;
mod dot_product;
mod evaluate;
mod from;
mod get;
mod norm;
mod ownership;
mod properties;
mod rounding;
mod sample;
mod serialize;
mod set;
mod to_string;
mod unsafe_functions;

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
pub struct PolyOverQ {
    pub(crate) poly: fmpq_poly_struct,
}

impl fmt::Debug for PolyOverQ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PolyOverQ {{poly_f64(may be rounded; 5 decimals): {}, poly: {}, \
            storage: {{poly: {:?}}}}}",
            self.to_string_decimal(5),
            self,
            self.poly
        )
    }
}
