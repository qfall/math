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

use super::super::MatPolyOverZ;
use crate::traits::{GetNumColumns, GetNumRows};

impl MatPolyOverZ {
    /// Returns `true` if the provided [`MatPolyOverZ`] has only one row,
    /// i.e. is a row vector. Otherwise, returns `false`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let row_vec = MatPolyOverZ::from_str("[[1  1, 1  2, 1  3]]").unwrap();
    /// let col_vec = MatPolyOverZ::from_str("[[1  1],[0],[1  3]]").unwrap();
    ///
    /// assert!(row_vec.is_row_vector());
    /// assert!(!col_vec.is_row_vector());
    /// ```
    pub fn is_row_vector(&self) -> bool {
        self.get_num_rows() == 1
    }

    /// Returns `true` if the provided [`MatPolyOverZ`] has only one column,
    /// i.e. is a column vector. Otherwise, returns `false`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let row_vec = MatPolyOverZ::from_str("[[1  1, 1  2, 1  3]]").unwrap();
    /// let col_vec = MatPolyOverZ::from_str("[[1  1],[0],[1  3]]").unwrap();
    ///
    /// assert!(col_vec.is_column_vector());
    /// assert!(!row_vec.is_column_vector());
    /// ```
    pub fn is_column_vector(&self) -> bool {
        self.get_num_columns() == 1
    }

    /// Returns `true` if the provided [`MatPolyOverZ`] has only one column or one row,
    /// i.e. is a vector. Otherwise, returns `false`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let row_vec = MatPolyOverZ::from_str("[[1  1, 1  2, 1  3]]").unwrap();
    /// let col_vec = MatPolyOverZ::from_str("[[1  1],[0],[1  3]]").unwrap();
    ///
    /// assert!(row_vec.is_vector());
    /// assert!(col_vec.is_vector());
    /// ```
    pub fn is_vector(&self) -> bool {
        self.is_column_vector() || self.is_row_vector()
    }

    /// Returns `true` if the provided [`MatPolyOverZ`] has only one entry,
    /// i.e. is a 1x1 matrix. Otherwise, returns `false`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let vec = MatPolyOverZ::from_str("[[1  1]]").unwrap();
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
        let row = MatPolyOverZ::from_str(&format!("[[0, 1  {}]]", i64::MIN)).unwrap();
        let col =
            MatPolyOverZ::from_str(&format!("[[0],[ 1  2],[1  {}],[1  4]]", i64::MAX)).unwrap();

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
        let mat_1 = MatPolyOverZ::from_str(&format!("[[0, 1  {}],[1  2, 0]]", i64::MIN)).unwrap();
        let mat_2 =
            MatPolyOverZ::from_str(&format!("[[1  1, 1  {}, 0],[0,0,0]]", i64::MAX)).unwrap();
        let mat_3 =
            MatPolyOverZ::from_str(&format!("[[0,1  {}],[1  2,0],[1  4,1  5]]", i64::MIN)).unwrap();
        let mat_4 = MatPolyOverZ::from_str("[[1  1,0],[1  2,0],[1  4,0]]").unwrap();
        let mat_5 = MatPolyOverZ::from_str("[[1  1,1  2,1  4],[0,0,0]]").unwrap();

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
        let small = MatPolyOverZ::from_str("[[1  1]]").unwrap();
        let large = MatPolyOverZ::from_str(&format!("[[1  {}]]", i64::MIN)).unwrap();

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
        let row = MatPolyOverZ::from_str(&format!("[[0,1  {}]]", i64::MIN)).unwrap();
        let col = MatPolyOverZ::from_str(&format!("[[0],[1  {}],[1  3]]", i64::MIN)).unwrap();
        let mat = MatPolyOverZ::from_str("[[1  1,1  2],[1  3,1  4],[1  5,1  6]]").unwrap();

        assert!(!row.has_single_entry());
        assert!(!col.has_single_entry());
        assert!(!mat.has_single_entry());
    }
}
