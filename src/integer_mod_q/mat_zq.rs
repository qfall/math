// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! `MatZq` is a type of matrix with integer entries of arbitrary length modulo `q`.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod_mat::fmpz_mod_mat_struct;

mod cmp;
mod from;
mod get;
mod ownership;
mod serialize;
mod set;
mod to_string;

/// [`MatZq`] is a matrix with entries of type [`Zq`](crate::integer_mod_q::Zq).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_mod_mat_struct)
///     of the [`Zq`](crate::integer_mod_q::Zq) matrix
///
/// # Examples
#[derive(Debug)]
pub struct MatZq {
    pub(crate) matrix: fmpz_mod_mat_struct,
}
