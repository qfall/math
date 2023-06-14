// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`MatZq`] is a type of matrix with integer entries of arbitrary length modulo `q`.
//! This implementation uses the [FLINT](https://flintlib.org/) library.
//!
//! For **DEVELOPERS**: Many functions assume that the [`MatZq`] instances are reduced.
//! To avoid unnecessary checks and reductions, always return canonical/reduced
//! values. The end-user should be unable to obtain a non-reduced value.

use crate::integer_mod_q::Modulus;
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_struct;

mod arithmetic;
mod cmp;
mod concat;
mod default;
mod from;
mod get;
mod ownership;
mod sample;
mod serialize;
mod set;
mod solve;
mod sort;
mod tensor;
mod to_string;
mod trace;
mod transpose;
mod vector;

/// [`MatZq`] is a matrix with entries of type [`Zq`](crate::integer_mod_q::Zq).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_mod_mat_struct)
///     of the [`Zq`](crate::integer_mod_q::Zq) matrix
///
/// # Examples
/// ## Matrix usage
/// ```
/// use qfall_math::{
///     integer::Z,
///     integer_mod_q::MatZq,
///     traits::{GetEntry, SetEntry},
/// };
/// use std::str::FromStr;
///
/// // instantiate new matrix
/// let id_mat = MatZq::from_str("[[1,0],[0,1]] mod 2").unwrap();
///
/// // clone object, set and get entry
/// let mut clone = id_mat.clone();
/// clone.set_entry(0, 0, 2);
/// assert_eq!(GetEntry::<Z>::get_entry(&clone, 1, 1).unwrap(), Z::ONE);
///
/// // to_string incl. (de-)serialization
/// assert_eq!("[[1, 0],[0, 1]] mod 2", &id_mat.to_string());
/// ```
///
/// ## Vector usage
/// ```
/// use qfall_math::{
///     integer::Z,
///     integer_mod_q::MatZq,
/// };
/// use std::str::FromStr;
///
/// let row_vec = MatZq::from_str("[[1,1,1]] mod 2").unwrap();
/// let col_vec = MatZq::from_str("[[1],[-1],[0]] mod 2").unwrap();
///
/// // check if matrix instance is vector
/// assert!(row_vec.is_row_vector());
/// assert!(col_vec.is_column_vector());
/// ```
#[derive(Debug)]
pub struct MatZq {
    pub(crate) matrix: fmpz_mod_mat_struct,

    // Since `get_mod` is needed for many actions with `MatZq` instances
    // a separate storage of the modulus object guarantees memory safety and
    // is due to a reference counter in the `Modulus` object memory efficient.
    // The modulus of a `MatZq` is not able to be modified afterwards. Hence, we
    // do not need to care about conformity of the modulus stored in the `matrix`
    // attribute and `modulus` attribute, if they are both initalized from the same value.
    modulus: Modulus,
}
