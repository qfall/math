// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `transpose` function.

use crate::traits::{GetNumColumns, GetNumRows};

use super::MatZ;
use flint_sys::fmpz_mat::fmpz_mat_transpose;

impl MatZ {
    /// Returns the transposed form of the given matrix, i.e. rows get transformed to columns
    /// and vice versa.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let mat = MatZ::from_str("[[2,1],[2,1],[2,1]]").unwrap();
    /// let cmp = MatZ::from_str("[[2,2,2],[1,1,1]]").unwrap();
    ///
    /// assert_eq!(mat.transpose(), cmp);
    /// ```
    pub fn transpose(&self) -> Self {
        let mut out = Self::new(self.get_num_columns(), self.get_num_rows());
        unsafe { fmpz_mat_transpose(&mut out.matrix, &self.matrix) };
        out
    }
}

#[cfg(test)]
mod test_transpose {
    use super::MatZ;
    use std::str::FromStr;

    /// Checks if a row is correctly converted to a column
    #[test]
    fn row_to_column() {
        let mat = MatZ::from_str("[[1],[2],[3]]").unwrap();
        let cmp = MatZ::from_str("[[1,2,3]]").unwrap();

        assert_eq!(cmp, mat.transpose());
    }

    /// Checks if a column is correctly converted to a row
    #[test]
    fn column_to_row() {
        let mat = MatZ::from_str("[[1,2,3]]").unwrap();
        let cmp = MatZ::from_str("[[1],[2],[3]]").unwrap();

        assert_eq!(cmp, mat.transpose());
    }

    /// Checks if large, negative, and zero values are transposed correctly
    #[test]
    fn different_entry_values() {
        let mat = MatZ::from_str(&format!("[[{},{},0]]", i64::MAX, i64::MIN)).unwrap();
        let cmp = MatZ::from_str(&format!("[[{}],[{}],[0]]", i64::MAX, i64::MIN)).unwrap();

        assert_eq!(cmp, mat.transpose());
    }
}
