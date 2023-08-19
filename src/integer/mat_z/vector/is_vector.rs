// Copyright © 2023 Niklas Siemer
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

use super::super::MatZ;
use crate::traits::{GetNumColumns, GetNumRows};

impl MatZ {
    /// Returns `true` if the provided [`MatZ`] has only one row,
    /// i.e. is a row vector. Otherwise, returns `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let vec = MatZ::from_str("[[1, 2, 3]]").unwrap();
    ///
    /// assert!(vec.is_row_vector());
    /// assert!(!vec.transpose().is_row_vector());
    /// ```
    pub fn is_row_vector(&self) -> bool {
        self.get_num_rows() == 1
    }

    /// Returns `true` if the provided [`MatZ`] has only one column,
    /// i.e. is a column vector. Otherwise, returns `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let vec = MatZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// assert!(vec.is_column_vector());
    /// assert!(!vec.transpose().is_column_vector());
    /// ```
    pub fn is_column_vector(&self) -> bool {
        self.get_num_columns() == 1
    }

    /// Returns `true` if the provided [`MatZ`] has only one column or one row,
    /// i.e. is a vector. Otherwise, returns `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let vec = MatZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// assert!(vec.is_vector());
    /// assert!(vec.transpose().is_vector());
    /// ```
    pub fn is_vector(&self) -> bool {
        self.is_column_vector() || self.is_row_vector()
    }

    /// Returns `true` if the provided [`MatZ`] has only one entry,
    /// i.e. is a 1x1 matrix. Otherwise, returns `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let vec = MatZ::from_str("[[1]]").unwrap();
    ///
    /// assert!(vec.has_single_entry());
    /// ```
    pub fn has_single_entry(&self) -> bool {
        self.is_column_vector() && self.is_row_vector()
    }
}

#[cfg(test)]
mod test_is_vector {
    use super::*;
    use std::str::FromStr;

    /// Check whether matrices with one row or one column
    /// get recognized as (row or column) vectors
    #[test]
    fn vectors_detected() {
        let row = MatZ::from_str(&format!("[[1, {}]]", i64::MIN)).unwrap();
        let col = MatZ::from_str(&format!("[[1],[2],[{}],[4]]", i64::MAX)).unwrap();

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
        let mat_1 = MatZ::from_str(&format!("[[1, {}],[2, 3]]", i64::MIN)).unwrap();
        let mat_2 = MatZ::from_str(&format!("[[1, {}, 3],[4, 5, 6]]", i64::MAX)).unwrap();
        let mat_3 = MatZ::from_str(&format!("[[1, {}],[2, 3],[4, 5]]", i64::MIN)).unwrap();
        let mat_4 = MatZ::from_str("[[1, 0],[2, 0],[4, 0]]").unwrap();
        let mat_5 = MatZ::from_str("[[1, 2, 4],[0, 0, 0]]").unwrap();

        assert!(!mat_1.is_column_vector());
        assert!(!mat_1.is_row_vector());
        assert!(!mat_1.is_vector());

        assert!(!mat_2.is_column_vector());
        assert!(!mat_2.is_row_vector());
        assert!(!mat_2.is_vector());

        assert!(!mat_3.is_column_vector());
        assert!(!mat_3.is_row_vector());
        assert!(!mat_3.is_vector());

        assert!(!mat_4.is_column_vector());
        assert!(!mat_4.is_row_vector());
        assert!(!mat_4.is_vector());

        assert!(!mat_5.is_column_vector());
        assert!(!mat_5.is_row_vector());
        assert!(!mat_5.is_vector());
    }

    /// Check whether matrices with only one entry get recognized as single entry matrices
    #[test]
    fn single_entry_detected() {
        let small = MatZ::from_str("[[1]]").unwrap();
        let large = MatZ::from_str(&format!("[[{}]]", i64::MIN)).unwrap();

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
        let row = MatZ::from_str(&format!("[[1, {}]]", i64::MIN)).unwrap();
        let col = MatZ::from_str(&format!("[[1],[{}],[3]]", i64::MIN)).unwrap();
        let mat = MatZ::from_str("[[1, 2],[3, 4],[5, 6]]").unwrap();

        assert!(!row.has_single_entry());
        assert!(!col.has_single_entry());
        assert!(!mat.has_single_entry());
    }
}
