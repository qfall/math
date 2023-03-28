// Copyright © 2023 Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module implements [`Zq`].
//!
//! This implementation uses [`fmpz_mod`](https://www.flintlib.org/doc/fmpz_mod.html)
//! from the [FLINT](https://flintlib.org/) library.
//! FLINT uses a `fmpz_mod_ctx_struct` to store functions and data used for
//! optimizing modulo operations.
//! This struct is wrapped in [`Modulus`](super::Modulus) for easy use.
//!
//! For **DEVELOPERS**: The [`PartialEq`] trait expects the [`Zq`] instance to be reduced.
//! Hence, apply `reduce` after every possible `value` change!

use super::Modulus;
use crate::integer::Z;
use serde::{Deserialize, Serialize};

mod arithmetic;
mod from;
mod reduce;
mod to_string;

/// [`Zq`] is a type for integers of arbitrary length modulo `q`.
/// This means, integer in `[0..q)` (`0` inclusive, `q` exclusive).
///
/// # Example
/// ```
/// # use math::error::MathError;
/// use math::integer_mod_q::Zq;
///
/// let value = Zq::try_from((5, 10))?;
/// # Ok::<(), MathError>(())
/// ```
///
/// [`Zq`] represents an integer value in a modulus ring.
///
/// Attributes:
/// - `value`: holds a [`Z`] value for an integer value
/// - `modulus`: holds a [`Modulus`] above which the value is reduced
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Zq {
    pub(crate) value: Z,
    pub(crate) modulus: Modulus,
}
