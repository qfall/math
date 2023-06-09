// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `transpose` function.

use crate::traits::*;

use super::MatQ;
use flint_sys::fmpq_mat::fmpq_mat_transpose;

impl MatQ {
    /// Returns the transposed form of the given matrix, i.e. rows get transformed to columns
    /// and vice versa.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let mat = MatQ::from_str("[[1/2,1],[2,1/7],[2,1]]").unwrap();
    /// let cmp = MatQ::from_str("[[1/2,2,2],[1,1/7,1]]").unwrap();
    ///
    /// assert_eq!(mat.transpose(), cmp);
    /// ```
    pub fn transpose(&self) -> Self {
        let mut out = Self::new(self.get_num_columns(), self.get_num_rows()).unwrap();
        unsafe { fmpq_mat_transpose(&mut out.matrix, &self.matrix) };
        out
    }
}

#[cfg(test)]
mod test_transpose {
    use super::MatQ;
    use std::str::FromStr;

    /// Checks if a row is correctly converted to a column
    #[test]
    fn row_to_column() {
        let mat = MatQ::from_str("[[1/2],[2],[8/4]]").unwrap();
        let cmp = MatQ::from_str("[[1/2,2,2]]").unwrap();

        assert_eq!(cmp, mat.transpose());
    }

    /// Checks if a column is correctly converted to a row
    #[test]
    fn column_to_row() {
        let mat = MatQ::from_str("[[1/2,2,2]]").unwrap();
        let cmp = MatQ::from_str("[[1/2],[2],[8/4]]").unwrap();

        assert_eq!(cmp, mat.transpose());
    }

    /// Checks if large, negative, and zero values are transposed correctly
    #[test]
    fn different_entry_values() {
        let mat = MatQ::from_str(&format!(
            "[[{},{},1/{},1/{},0]]",
            i64::MAX,
            i64::MIN,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let cmp = MatQ::from_str(&format!(
            "[[{}],[{}],[1/{}],[1/{}],[0]]",
            i64::MAX,
            i64::MIN,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();

        assert_eq!(cmp, mat.transpose());
    }
}
