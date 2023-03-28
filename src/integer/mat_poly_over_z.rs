// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`MatPolyOverZ`] is a type of matrix with entries of [`PolyOverZ`](crate::integer::PolyOverZ).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_poly_mat::fmpz_poly_mat_struct;

mod cmp;
mod from;
mod get;
mod ownership;
mod properties;
mod set;
mod to_string;

/// [`MatPolyOverZ`] is a matrix with entries of type [`PolyOverZ`](crate::integer::PolyOverZ).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_poly_mat_struct)
///     of the [`PolyOverZ`](crate::integer::PolyOverZ) matrix
///
/// # Examples
#[derive(Debug)]
pub struct MatPolyOverZ {
    pub(crate) matrix: fmpz_poly_mat_struct,
}
