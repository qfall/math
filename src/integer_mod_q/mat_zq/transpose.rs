// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `transpose` function.

use crate::traits::*;

use super::MatZq;
use flint_sys::fmpz_mat::fmpz_mat_transpose;

impl MatZq {
    /// Returns the transposed form of the given matrix, i.e. rows get transformed to columns
    /// and vice versa.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mat = MatZq::from_str("[[2, 1],[2, 1],[2, 1]] mod 4").unwrap();
    /// let cmp = MatZq::from_str("[[2, 2, 2],[1, 1, 1]] mod 4").unwrap();
    ///
    /// assert_eq!(mat.transpose(), cmp);
    /// ```
    pub fn transpose(&self) -> Self {
        let mut out = Self::new(self.get_num_columns(), self.get_num_rows(), self.get_mod());
        unsafe { fmpz_mat_transpose(&mut out.matrix.mat[0], &self.matrix.mat[0]) };
        out
    }
}

#[cfg(test)]
mod test_transpose {
    use super::MatZq;
    use std::str::FromStr;

    /// Checks if a row is correctly converted to a column
    #[test]
    fn row_to_column() {
        let mat = MatZq::from_str("[[1],[2],[3]] mod 4").unwrap();
        let cmp = MatZq::from_str("[[1, 2, 3]] mod 4").unwrap();

        assert_eq!(cmp, mat.transpose());
    }

    /// Checks if a column is correctly converted to a row
    #[test]
    fn column_to_row() {
        let mat = MatZq::from_str("[[1, 2, 3]] mod 4").unwrap();
        let cmp = MatZq::from_str("[[1],[2],[3]] mod 4").unwrap();

        assert_eq!(cmp, mat.transpose());
    }

    /// Checks if large, negative, and zero values are transposed correctly
    #[test]
    fn different_entry_values() {
        let mat = MatZq::from_str(&format!("[[{}, {}, 0]] mod 4", i64::MAX, i64::MIN)).unwrap();
        let cmp = MatZq::from_str(&format!("[[{}],[{}],[0]] mod 4", i64::MAX, i64::MIN)).unwrap();

        assert_eq!(cmp, mat.transpose());
    }
}
