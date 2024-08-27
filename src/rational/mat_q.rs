// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`MatQ`] is a type of matrix with rational entries of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.
//!
//! For **DEVELOPERS**: Many functions assume that the [`MatQ`] instances are reduced.
//! To avoid unnecessary checks and reductions, always return canonical/reduced
//! values. The end-user should be unable to obtain a non-reduced value.

use flint_sys::fmpq_mat::fmpq_mat_struct;

mod arithmetic;
mod cholesky_decomp;
mod cmp;
mod concat;
mod default;
mod determinant;
mod from;
mod get;
mod gso;
mod inverse;
mod ownership;
mod properties;
mod rounding;
mod serialize;
mod set;
mod sort;
mod tensor;
mod to_string;
mod trace;
mod transpose;
mod vector;

/// [`MatQ`] is a matrix with entries of type [`Q`](crate::rational::Q).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpq_mat_struct)
///     of the [`Q`](crate::rational::Q) matrix
///
/// # Examples
/// ## Matrix usage
/// ```
/// use qfall_math::{
///     rational::{Q, MatQ},
///     traits::{GetEntry, SetEntry},
/// };
/// use std::str::FromStr;
///
/// // instantiate new matrix
/// let id_mat = MatQ::from_str("[[1/2, 0/1],[0, 1]]").unwrap();
///
/// // clone object, set and get entry
/// let mut clone = id_mat.clone();
/// clone.set_entry(0, 0, Q::from(2));
/// assert_eq!(
///     clone.get_entry(1, 1).unwrap(),
///     Q::ONE
/// );
///
/// // to_string
/// assert_eq!("[[1/2, 0],[0, 1]]", &id_mat.to_string());
/// ```
///
/// ## Vector usage
/// ```
/// use qfall_math::{
///     rational::{Q, MatQ},
/// };
/// use std::str::FromStr;
///
/// let row_vec = MatQ::from_str("[[1/3, 1/4, 1/5]]").unwrap();
/// let col_vec = MatQ::from_str("[[-1/-5],[-1],[0]]").unwrap();
///
/// // check if matrix instance is vector
/// assert!(row_vec.is_row_vector());
/// assert!(col_vec.is_column_vector());
/// ```
#[derive(Debug)]
pub struct MatQ {
    pub(crate) matrix: fmpq_mat_struct,
}
