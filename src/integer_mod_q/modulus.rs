// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`Modulus`] is a type of a positive integer larger than `1` that is used in
//! order to do modulus operations. The modulus type itself is also used for
//! optimizations.
//! A [`Modulus`] of `1` is not allowed, since operations would always just
//! return `0`. This way, checks later in the code can be avoided.
//!
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod::fmpz_mod_ctx;
use std::rc::Rc;

mod cmp;
mod from;
mod get;
mod ownership;
mod properties;
mod serialize;
mod to_string;

/// [`Modulus`] is a type of a positive integer larger than `1` that is used
/// to do modulus operations.
///
/// Attributes:
/// - `modulus`: holds the value of the modulus
///
/// # Examples
/// Create [`Modulus`] from [`str`]:
/// ```
/// use qfall_math::integer_mod_q::Modulus;
/// use std::str::FromStr;
/// use qfall_math::integer::Z;
/// let value = Z::from(10);
///
/// // instantiations
/// let a = Modulus::from_str("42").unwrap();
/// let b: Modulus = (&value).try_into().unwrap();
///
/// // clone
/// let clone = a.clone();
///
/// // properties
/// let is_prime: bool = a.is_prime();
///
/// // to_string incl. (de-)serialization
/// assert_eq!("42", &a.to_string());
/// assert_eq!(
///     "{\"modulus\":\"42\"}",
///     serde_json::to_string(&a).unwrap()
/// );
///
/// // comparison
/// assert_eq!(a, clone);
/// ```
#[derive(Debug)]
pub struct Modulus {
    pub(crate) modulus: Rc<fmpz_mod_ctx>,
}
