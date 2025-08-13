// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`MatPolynomialRingZq`] is a type of matrix with entries of [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use super::ModulusPolynomialRingZq;
use crate::{integer::MatPolyOverZ, utils::parse::partial_string};
use derive_more::Display;
use serde::{Deserialize, Serialize};
use std::fmt;

mod arithmetic;
mod cmp;
mod coefficient_embedding;
mod concat;
mod default;
mod from;
mod get;
mod norm;
mod properties;
mod reduce;
mod sample;
mod set;
mod sort;
mod tensor;
mod to_string;
mod transpose;
mod unsafe_functions;
mod vector;

/// [`MatPolynomialRingZq`] is a matrix with entries of type [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq).
///
/// Attributes:
/// - `matrix`: holds the [`MatPolyOverZ`] matrix
/// - `modulus`: holds the [`ModulusPolynomialRingZq`] modulus of the matrix
///
/// # Examples
/// ## Matrix usage
/// ```
/// use qfall_math::{
///     integer::{PolyOverZ, MatPolyOverZ},
///     integer_mod_q::{MatPolynomialRingZq, PolyOverZq},
///     traits::{MatrixGetEntry, MatrixSetEntry},
/// };
/// use std::str::FromStr;
///
/// // instantiate new matrix
/// let id_mat = MatPolyOverZ::identity(2, 2);
/// // instantiate modulus_object
/// let modulus = PolyOverZq::from_str("5  1 0 0 0 1 mod 17").unwrap();
///
/// let poly_mat = MatPolynomialRingZq::from((id_mat, modulus));
///
/// // clone object, set and get entry
/// let mut clone = poly_mat.clone();
/// clone.set_entry(0, 0, PolyOverZ::from(-16));
///
/// let entry: PolyOverZ = clone.get_entry(0,0).unwrap();
/// assert_eq!(
///     entry,
///     PolyOverZ::from(1),
/// );
///
/// // to_string
/// assert_eq!("[[1  1, 0],[0, 1  1]] / 5  1 0 0 0 1 mod 17", &poly_mat.to_string());
/// ```
///
/// ## Vector usage
/// ```
/// use qfall_math::{
///     integer::{PolyOverZ, MatPolyOverZ},
///     integer_mod_q::{MatPolynomialRingZq, PolyOverZq},
/// };
/// use std::str::FromStr;
///
/// let row_vec = MatPolyOverZ::from_str("[[1  1, 0, 1  1]]").unwrap();
/// let col_vec = MatPolyOverZ::from_str("[[1  -5],[1  -1],[0]]").unwrap();
///
/// let modulus = PolyOverZq::from_str("5  1 0 0 0 1 mod 17").unwrap();
///
/// let row_vec = MatPolynomialRingZq::from((row_vec, modulus));
/// let col_vec = MatPolynomialRingZq::from((col_vec, row_vec.get_mod()));
///
/// // check if matrix instance is vector
/// assert!(row_vec.is_row_vector());
/// assert!(col_vec.is_column_vector());
/// ```
#[derive(PartialEq, Eq, Serialize, Deserialize, Display, Clone)]
#[display("{matrix} / {modulus}")]
pub struct MatPolynomialRingZq {
    pub(crate) matrix: MatPolyOverZ,
    pub(crate) modulus: ModulusPolynomialRingZq,
}

impl fmt::Debug for MatPolynomialRingZq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "MatPolynomialRingZq: {{matrix: {}, modulus: {} storage: {{matrix: {:?}, modulus: {:?}}}}}",
            // printing the entire matrix is not meaningful for large matrices
            partial_string(&self.get_representative_least_nonnegative_residue(), 3, 3),
            self.modulus,
            self.matrix,
            self.modulus
        )
    }
}
