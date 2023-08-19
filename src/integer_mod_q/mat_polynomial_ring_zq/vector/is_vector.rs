// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes all functionality to check
//! whether a matrix represents a vector, i.e. has only one row
//! or one column.
//! These methods should be used to ensure that vector functions
//! can only be called on suitably formed vector/matrices.

use crate::{
    integer_mod_q::MatPolynomialRingZq,
    traits::{GetNumColumns, GetNumRows},
};

impl MatPolynomialRingZq {
    /// Returns `true` if the provided [`MatPolynomialRingZq`] has only one row,
    /// i.e. is a row vector. Otherwise, returns `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42]]").unwrap();
    /// let poly_mat_2 = MatPolyOverZ::from_str("[[4  -1 0 1 1],[2  1 2]]").unwrap();
    ///
    /// let row_vec = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
    /// let col_vec = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
    ///
    /// assert!(row_vec.is_row_vector());
    /// assert!(!col_vec.is_row_vector());
    /// ```
    pub fn is_row_vector(&self) -> bool {
        self.get_num_rows() == 1
    }

    /// Returns `true` if the provided [`MatPolynomialRingZq`] has only one column,
    /// i.e. is a column vector. Otherwise, returns `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42]]").unwrap();
    /// let poly_mat_2 = MatPolyOverZ::from_str("[[4  -1 0 1 1],[2  1 2]]").unwrap();
    ///
    /// let row_vec = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
    /// let col_vec = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
    ///
    /// assert!(col_vec.is_column_vector());
    /// assert!(!row_vec.is_column_vector());
    /// ```
    pub fn is_column_vector(&self) -> bool {
        self.get_num_columns() == 1
    }

    /// Returns `true` if the provided [`MatPolynomialRingZq`] has only one column or one row,
    /// i.e. is a vector. Otherwise, returns `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42]]").unwrap();
    /// let poly_mat_2 = MatPolyOverZ::from_str("[[4  -1 0 1 1],[2  1 2]]").unwrap();
    ///
    /// let row_vec = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
    /// let col_vec = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
    ///
    /// assert!(row_vec.is_vector());
    /// assert!(col_vec.is_vector());
    /// ```
    pub fn is_vector(&self) -> bool {
        self.is_column_vector() || self.is_row_vector()
    }

    /// Returns `true` if the provided [`MatPolynomialRingZq`] has only one entry,
    /// i.e. is a 1x1 matrix. Otherwise, returns `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[1  42]]").unwrap();
    ///
    /// let vec = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// assert!(vec.has_single_entry());
    /// ```
    pub fn has_single_entry(&self) -> bool {
        self.is_column_vector() && self.is_row_vector()
    }
}

#[cfg(test)]
mod test_is_vector {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Check whether matrices with one row or one column
    /// get recognized as (row or column) vectors
    #[test]
    fn vectors_detected() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "5  1 1 0 0 {} mod {LARGE_PRIME}",
            i64::MAX
        ))
        .unwrap();
        let poly_mat_1 =
            MatPolyOverZ::from_str(&format!("[[4  1 {} 1 1, 1  42]]", i64::MAX)).unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str(&format!(
            "[[4  1 {} 1 1],[1  42],[0],[2  {} 2]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();

        let row = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let col = MatPolynomialRingZq::from((&poly_mat_2, &modulus));

        assert!(row.is_row_vector());
        assert!(!row.is_column_vector());
        assert!(row.is_vector());

        assert!(!col.is_row_vector());
        assert!(col.is_column_vector());
        assert!(col.is_vector());
    }

    /// Check whether matrices with more than one row or column
    /// don't get recognized as (row or column) vector
    #[test]
    fn non_vectors_detected() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "5  1 1 0 0 {} mod {LARGE_PRIME}",
            i64::MAX
        ))
        .unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str(&format!(
            "[[4  1 {} 1 1, 1  42],[3  1 1 1, 1  17]]",
            i64::MAX
        ))
        .unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str(&format!(
            "[[4  1 {} 1 1, 0],[1  42, 1  1],[0, 0]]",
            i64::MAX
        ))
        .unwrap();

        let mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));

        assert!(!mat_1.is_column_vector());
        assert!(!mat_1.is_row_vector());
        assert!(!mat_1.is_vector());

        assert!(!mat_2.is_column_vector());
        assert!(!mat_2.is_row_vector());
        assert!(!mat_2.is_vector());
    }

    /// Check whether matrices with only one entry get recognized as single entry matrices
    #[test]
    fn single_entry_detected() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "5  1 1 0 0 {} mod {LARGE_PRIME}",
            i64::MAX
        ))
        .unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[1  42]]").unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str(&format!("[[3  1 {} 1]]", i64::MAX)).unwrap();

        let small = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let large = MatPolynomialRingZq::from((&poly_mat_2, &modulus));

        // check whether single entry is correctly detected
        assert!(small.has_single_entry());
        assert!(large.has_single_entry());

        // check whether single entry is correctly detected as row and column vector
        assert!(small.is_row_vector());
        assert!(small.is_column_vector());
        assert!(small.is_vector());

        assert!(large.is_row_vector());
        assert!(large.is_column_vector());
        assert!(large.is_vector());
    }

    /// Check whether matrices with more than one entry
    /// don't get recognized as single entry matrices
    #[test]
    fn non_single_entry_detected() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "5  1 1 0 0 {} mod {LARGE_PRIME}",
            i64::MAX
        ))
        .unwrap();
        let poly_mat_1 =
            MatPolyOverZ::from_str(&format!("[[4  1 {} 1 1, 1  42]]", i64::MAX)).unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str(&format!(
            "[[4  1 {} 1 1],[1  42],[0],[2  {} 2]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let poly_mat_3 = MatPolyOverZ::from_str(&format!(
            "[[4  1 {} 1 1, 1  42],[3  1 1 1, 1  17]]",
            i64::MAX
        ))
        .unwrap();

        let row = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let col = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
        let mat = MatPolynomialRingZq::from((&poly_mat_3, &modulus));

        assert!(!row.has_single_entry());
        assert!(!col.has_single_entry());
        assert!(!mat.has_single_entry());
    }
}
