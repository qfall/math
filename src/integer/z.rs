// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! `Z` is a type for integers with arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz::fmpz;

mod arithmetic;
mod cmp;
mod default;
mod exp;
mod from;
mod ownership;
mod serialize;
mod to_string;

/// [`Z`] represents any integer value.
///
/// Attributes:
/// - `value`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz)
///     for an integer value
///
/// # Examples
/// ```
/// use qfall_math::integer::Z;
/// use std::str::FromStr;
///
/// let a = Z::from_str("-876543")?;
/// let b = Z::from_i64(i64::MIN);
/// let zero = Z::default();
///
/// let result = &a - b.clone() + &zero;
///
/// drop(b);
///
/// assert_ne!(result, zero);
/// # Ok::<(), qfall_math::error::MathError>(())
/// ```
#[derive(Debug)]
pub struct Z {
    pub(crate) value: fmpz,
}
