// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`VecZ`] is a vector with integer entries of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

mod from;
mod get;
mod mul;
mod set;
mod transpose;

use super::MatZ;

/// [`VecZ`] is a vector with entries of type [`Z`](crate::integer::Z).
///
/// Attributes:
/// - `matrix`: holds a [`MatZ`] instance with either #rows or #columns being `1`
///
/// # Examples
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VecZ {
    pub(crate) matrix: MatZ,
}
