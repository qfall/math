// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! `MatQ` is a type of matrix with rational entries of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpq_mat::fmpq_mat_struct;

mod cmp;
mod from;
mod get;
mod ownership;
mod set;
mod to_string;
mod transpose;

/// [`MatQ`] is a matrix with entries of type [`Q`](crate::rational::Q).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpq_mat_struct)
///     of the [`Q`](crate::rational::Q) matrix
///
/// # Examples
#[derive(Debug)]
pub struct MatQ {
    pub(crate) matrix: fmpq_mat_struct,
}
