// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`Q`] is a type for rationals of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.
//!
//! For **DEVELOPERS**: Many functions assume that the [`Q`] instances are reduced.
//! To avoid unnecessary checks and reductions, always return canonical/reduced
//! values. The end-user should be unable to obtain a non-reduced value.

use flint_sys::fmpq::fmpq;

mod arithmetic;
mod cmp;
mod default;
mod distance;
mod from;
mod get;
mod ownership;
mod properties;
mod rounding;
mod serialize;
mod to_string;

/// [`Q`] represents any rational value.
///
/// Attributes:
/// - `value`: holds [FLINT](https://flintlib.org/)'s [struct](fmpq)
///     for a rational value
///
/// # Implicit Typecasting
/// Most of our functions take as input values of type [`Into<Q>`].
/// These capture all types that can be turned into a [`Q`] value.
/// The types are [`Q`], [`Z`](crate::integer::Z), [`Zq`](crate::integer_mod_q::Zq),
/// [`Modulus`](crate::integer_mod_q::Modulus), [`i8`], [`i16`], [`i32`],
/// [`i64`], [`u8`], [`u16`], [`u32`], [`u64`], [`f32`], [`f64`]
/// and the references of all of these types.
/// These types are then implicitly casted to a [`Q`] before the desired action is
/// performed.
///
/// # Examples
/// ```
/// use qfall_math::rational::Q;
/// use std::str::FromStr;
///
/// // instantiations
/// let a = Q::from_str("-876543/235")?;
/// let b = Q::from(21);
/// let zero = Q::default();
/// let _ = a.clone();
///
/// // arithmetics
/// let _ = &a + &zero;
/// let _ = &a * &b;
///
/// // to_string incl. (de-)serialization
/// assert_eq!("-876543/235", &a.to_string());
/// assert_eq!(
///     "{\"value\":\"-876543/235\"}",
///     serde_json::to_string(&a).unwrap()
/// );
///
/// // comparison
/// assert_ne!(a, b);
/// # Ok::<(), qfall_math::error::MathError>(())
/// ```
#[derive(Debug)]
pub struct Q {
    pub(crate) value: fmpq,
}
