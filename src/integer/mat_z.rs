// Copyright © 2023 Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! `MatZ` is a type of matrix with integer entries of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mat::fmpz_mat_struct;

mod cmp;
mod from;
mod get;
mod mul;
mod ownership;
mod serialize;
mod set;
mod to_string;
mod transpose;
mod vector;

/// [`MatZ`] is a matrix with entries of type [`Z`](crate::integer::Z).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_mat_struct)
///     of the [`Z`](crate::integer::Z) matrix
///
/// # Examples
/// ## Matrix usage
/// ```
/// use math::{
///     integer::{MatZ, Z},
///     traits::{GetEntry, SetEntry},
/// };
/// use std::str::FromStr;
///
/// // instantiate new matrix
/// let id_mat = MatZ::from_str("[[1,0],[0,1]]").unwrap();
///
/// // clone object, set and get entry
/// let mut clone = id_mat.clone();
/// clone.set_entry(0, 0, 2);
/// assert_eq!(clone.get_entry(1, 1).unwrap(), Z::ONE);
///
/// // multiplication, transposition and comparison
/// assert_eq!(id_mat.transpose() * &clone, clone);
///
/// // to_string incl. (de-)serialization
/// assert_eq!("[[1, 0],[0, 1]]", &id_mat.to_string());
/// assert_eq!(
///     "{\"matrix\":\"[[1, 0],[0, 1]]\"}",
///     serde_json::to_string(&id_mat).unwrap()
/// );
/// ```
///
/// ## Vector usage
/// ```
/// use math::{
///     integer::{MatZ, Z},
/// };
/// use std::str::FromStr;
///
/// let row_vec = MatZ::from_str("[[1,1,1]]").unwrap();
/// let col_vec = MatZ::from_str("[[1],[-1],[0]]").unwrap();
///
/// // check if matrix instance is vector
/// assert!(row_vec.is_row_vector());
/// assert!(col_vec.is_column_vector());
///
/// // dot product
/// assert_eq!(row_vec.dot_product(&col_vec).unwrap(), Z::ZERO);
///
/// // norm calculation
/// assert_eq!(col_vec.norm_sqrd_eucl().unwrap(), Z::from(2));
/// assert_eq!(row_vec.norm_infty().unwrap(), Z::ONE);
/// ```
#[derive(Debug)]
pub struct MatZ {
    pub(crate) matrix: fmpz_mat_struct,
}
