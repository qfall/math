// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! `MatZ` is a type of matrix with integer entries of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mat::fmpz_mat_struct;

mod from;
mod get;
mod ownership;
mod set;

/// [`MatZ`] is a matrix with entries of type [`Z`](crate::integer::Z).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_mat_struct)
///     of the [`Z`](crate::integer::Z) matrix
///
/// # Examples
#[derive(Debug)]
pub struct MatZ {
    pub(crate) matrix: fmpz_mat_struct,
}
