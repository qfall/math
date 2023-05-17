// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `transpose` function.

use super::MatPolynomialRingZq;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_transpose;

impl MatPolynomialRingZq {
    /// Returns the transposed form of the given matrix, i.e. rows get transformed to columns
    /// and vice versa.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[1  42],[2  1 2],[1  17]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// let transpose = poly_ring_mat.transpose();
    /// ```
    pub fn transpose(&self) -> Self {
        let mut out =
            Self::new(self.get_num_columns(), self.get_num_rows(), &self.modulus).unwrap();
        unsafe { fmpz_poly_mat_transpose(&mut out.matrix.matrix, &self.matrix.matrix) };
        out
    }
}

#[cfg(test)]
mod test_transpose {

    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    const BITPRIME64: u64 = 18446744073709551557;

    /// Checks if a row is correctly converted to a column
    #[test]
    fn row_to_column() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[1  42],[2  1 2],[1  17]]").unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let cmp = MatPolyOverZ::from_str("[[1  8,2  1 2,1  0]]").unwrap();

        assert_eq!(cmp, poly_ring_mat.transpose().matrix);
    }

    /// Checks if a column is correctly converted to a row
    #[test]
    fn column_to_row() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[1  42,2  1 2,1  17]]").unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let cmp = MatPolyOverZ::from_str("[[1  8],[2  1 2],[1  0]]").unwrap();

        assert_eq!(cmp, poly_ring_mat.transpose().matrix);
    }

    /// Checks if large, negative, and zero values are transposed correctly
    #[test]
    fn different_entry_values() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", BITPRIME64)).unwrap();
        let poly_mat = MatPolyOverZ::from_str(&format!("[[1  {},1  -42,1  0]]", i64::MAX)).unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let cmp = MatPolyOverZ::from_str(&format!(
            "[[1  {}],[1  {}],[1  0]]",
            i64::MAX,
            BITPRIME64 - 42
        ))
        .unwrap();

        assert_eq!(cmp, poly_ring_mat.transpose().matrix);
    }
}
