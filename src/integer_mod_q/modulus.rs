// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`Modulus`] is a type of a positive non-zero integer that is used in order to
//! do modulus operations. The modulus type itself is also used for
//! optimizations.
//!
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod::fmpz_mod_ctx;
use std::rc::Rc;

mod cmp;
mod from;
mod get;
mod ownership;
mod properties;
mod to_string;

/// [`Modulus`] is a type of a positive non-zero integer that is used
/// to do modulus operations.
///
/// Attributes:
/// - `modulus`: holds the value of the modulus
///
/// # Examples
/// Create [`Modulus`] from [`str`]:
/// ```
/// use math::integer_mod_q::Modulus;
/// use std::str::FromStr;
///
/// let modulus = Modulus::from_str("42").unwrap();
/// ```
///
/// Create [`Modulus`] from [`Z`](crate::integer::Z):
/// ```
/// # use math::integer_mod_q::Modulus;
/// # use math::integer::Z;
/// let value = Z::from(10);
///
/// let modulus: Modulus = (&value).try_into().unwrap();
/// let modulus: Modulus = <&Z>::try_into(&value).unwrap();
/// let modulus = Modulus::try_from_z(&value).unwrap();
/// let modulus = Modulus::try_from(&value).unwrap();
/// ```
#[derive(Debug)]
pub struct Modulus {
    pub(crate) modulus: Rc<fmpz_mod_ctx>,
}
