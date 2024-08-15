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
//! For **DEVELOPERS**: Many functions assume that the [`Zq`] instances are reduced.
//! To avoid unnecessary checks and reductions, always return canonical/reduced
//! values. The end-user should be unable to obtain a non-reduced value.

use super::Modulus;
use crate::integer::Z;
use serde::{Deserialize, Serialize};

mod arithmetic;
mod distance;
pub(crate) mod fmpz_mod_helpers;
mod from;
mod get;
mod properties;
mod reduce;
mod sample;
mod to_string;

/// [`Zq`] is an arbitrary integer value in a residue class.
///
/// Attributes:
/// - `value`: holds a [`Z`] value for an integer value
/// - `modulus`: holds a [`Modulus`] above which the value is reduced
///
/// # Examples
/// ```
/// # use qfall_math::error::MathError;
/// use qfall_math::integer_mod_q::Zq;
/// use std::str::FromStr;
///
/// // instantiation
/// let a = Zq::from((5, 10));
/// let b = Zq::from_str("93 mod 10")?;
/// let _ = a.clone();
///
/// // arithmetics
/// let _ = &a + &b;
/// let _ = &a * &b;
///
/// // to_string incl. (de-)serialization
/// assert_eq!("5 mod 10", &a.to_string());
/// let _ = serde_json::to_string(&a).unwrap();
///
/// # Ok::<(), MathError>(())
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Zq {
    pub(crate) value: Z,
    pub(crate) modulus: Modulus,
}
