// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! `Q` is a type for rationals of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpq::fmpq;

mod arithmetic;
mod cmp;
mod default;
mod exp;
mod from;
mod ownership;
mod serialize;
mod to_string;

/// [`Q`] represents any rational value.
///
/// Attributes:
/// - `value`: holds [FLINT](https://flintlib.org/)'s [struct](fmpq)
///     for a rational value
///
/// # Examples
/// ```
/// use qfall_math::rational::Q;
/// use std::str::FromStr;
///
/// let a = Q::from_str("-876543/235")?;
/// let zero = Q::default();
/// # Ok::<(), qfall_math::error::MathError>(())
/// ```
#[derive(Debug)]
pub struct Q {
    pub(crate) value: fmpq,
}
