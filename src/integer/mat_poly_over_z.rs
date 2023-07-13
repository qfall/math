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

mod arithmetic;
mod cmp;
mod coefficient_embedding;
mod concat;
mod default;
mod evaluate;
mod from;
mod get;
mod ownership;
mod properties;
mod sample;
mod serialize;
mod set;
mod to_string;
mod trace;
mod transpose;
mod vector;

/// [`MatPolyOverZ`] is a matrix with entries of type [`PolyOverZ`](crate::integer::PolyOverZ).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_poly_mat_struct)
///     of the [`PolyOverZ`](crate::integer::PolyOverZ) matrix
///
/// # Examples
/// ## Matrix usage
/// ```
/// use qfall_math::{
///     integer::{PolyOverZ, MatPolyOverZ},
///     traits::{GetEntry, SetEntry},
/// };
/// use std::str::FromStr;
///
/// // instantiate new matrix
/// let id_mat = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1]]").unwrap();
///
/// // clone object, set and get entry
/// let mut clone = id_mat.clone();
/// clone.set_entry(0, 0, PolyOverZ::from_str("1  2").unwrap());
/// assert_eq!(
///     clone.get_entry(1, 1).unwrap(),
///     PolyOverZ::from_str("1  1").unwrap(),
/// );
///
/// // to_string
/// assert_eq!("[[1  1, 0],[0, 1  1]]", &id_mat.to_string());
/// ```
///
/// ## Vector usage
/// ```
/// use qfall_math::{
///     integer::{PolyOverZ, MatPolyOverZ},
/// };
/// use std::str::FromStr;
///
/// let row_vec = MatPolyOverZ::from_str("[[1  1, 0, 1  1]]").unwrap();
/// let col_vec = MatPolyOverZ::from_str("[[1  -5],[1  -1],[0]]").unwrap();
///
/// // check if matrix instance is vector
/// assert!(row_vec.is_row_vector());
/// assert!(col_vec.is_column_vector());
/// ```
#[derive(Debug)]
pub struct MatPolyOverZ {
    pub(crate) matrix: fmpz_poly_mat_struct,
}
