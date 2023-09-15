// Copyright © 2023 Marvin Beckmann, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation to manipulate a [`MatPolyOverZ`] matrix.

use super::MatPolyOverZ;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    macros::for_others::implement_for_owned,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::{
        collective_evaluation::evaluate_vec_dimensions_set_row_or_col,
        index::{evaluate_index, evaluate_indices_for_matrix},
    },
};
use flint_sys::{
    fmpz_poly::{fmpz_poly_set, fmpz_poly_swap},
    fmpz_poly_mat::fmpz_poly_mat_entry,
};
use std::fmt::Display;

impl SetEntry<&PolyOverZ> for MatPolyOverZ {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if the specified entry is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatPolyOverZ, PolyOverZ};
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatPolyOverZ::new(2, 2);
    /// let value = PolyOverZ::from_str("2  1 1").unwrap();
    ///
    /// matrix.set_entry(0, 1, &value).unwrap();
    /// matrix.set_entry(-1, -2, &PolyOverZ::from(2)).unwrap();
    ///
    /// assert_eq!("[[0, 2  1 1],[1  2, 0]]", matrix.to_string());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if `row` or `column` are greater than the matrix size.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        value: &PolyOverZ,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_indices_for_matrix(self, row, column)?;

        // since `self` is a correct matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpz_set` can successfully clone the
        // value inside the matrix. Therefore no memory leaks can appear.
        unsafe {
            let entry = fmpz_poly_mat_entry(&self.matrix, row_i64, column_i64);
            fmpz_poly_set(entry, &value.poly)
        };

        Ok(())
    }
}

implement_for_owned!(PolyOverZ, MatPolyOverZ, SetEntry);

impl MatPolyOverZ {
    /// Sets a column of the given matrix to the provided column of `other`.
    ///
    /// Parameters:
    /// - `col_0`: specifies the column of `self` that should be modified
    /// - `other`: specifies the matrix providing the column replacing the column in `self`
    /// - `col_1`: specifies the column of `other` providing
    /// the values replacing the original column in `self`
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified columns is not part of its matrix
    /// or if the number of rows differs.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mut mat_1 = MatPolyOverZ::new(2, 2);
    /// let mat_2 = MatPolyOverZ::from_str("[[1  1],[0]]").unwrap();
    /// mat_1.set_column(1, &mat_2, 0);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of columns is greater than the matrix dimensions or negative.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of rows of `self` and `other` differ.
    pub fn set_column(
        &mut self,
        col_0: impl TryInto<i64> + Display,
        other: &Self,
        col_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        let col_0 = evaluate_index(col_0)?;
        let col_1 = evaluate_index(col_1)?;

        evaluate_vec_dimensions_set_row_or_col(
            "set_column",
            col_0,
            col_1,
            self.get_num_columns(),
            other.get_num_columns(),
            self.get_num_rows(),
            other.get_num_rows(),
        )?;

        for row in 0..self.get_num_rows() {
            unsafe {
                fmpz_poly_set(
                    fmpz_poly_mat_entry(&self.matrix, row, col_0),
                    fmpz_poly_mat_entry(&other.matrix, row, col_1),
                )
            };
        }

        Ok(())
    }

    /// Sets a row of the given matrix to the provided row of `other`.
    ///
    /// Parameters:
    /// - `row_0`: specifies the row of `self` that should be modified
    /// - `other`: specifies the matrix providing the row replacing the row in `self`
    /// - `row_1`: specifies the row of `other` providing
    /// the values replacing the original row in `self`
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified rows is not part of its matrix
    /// or if the number of columns differs.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mut mat_1 = MatPolyOverZ::new(2, 2);
    /// let mat_2 = MatPolyOverZ::from_str("[[1  1, 0]]").unwrap();
    /// mat_1.set_row(0, &mat_2, 0);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows is greater than the matrix dimensions or negative.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of columns of `self` and `other` differ.
    pub fn set_row(
        &mut self,
        row_0: impl TryInto<i64> + Display,
        other: &Self,
        row_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        let row_0 = evaluate_index(row_0)?;
        let row_1 = evaluate_index(row_1)?;

        evaluate_vec_dimensions_set_row_or_col(
            "set_row",
            row_0,
            row_1,
            self.get_num_rows(),
            other.get_num_rows(),
            self.get_num_columns(),
            other.get_num_columns(),
        )?;

        for col in 0..self.get_num_columns() {
            unsafe {
                fmpz_poly_set(
                    fmpz_poly_mat_entry(&self.matrix, row_0, col),
                    fmpz_poly_mat_entry(&other.matrix, row_1, col),
                )
            };
        }

        Ok(())
    }

    /// Swaps two entries of the specified matrix.
    ///
    /// Parameters:
    /// - `row_0`: specifies the row, in which the first entry is located
    /// - `col_0`: specifies the column, in which the first entry is located
    /// - `row_1`: specifies the row, in which the second entry is located
    /// - `col_1`: specifies the column, in which the second entry is located
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified entries is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mut matrix = MatPolyOverZ::new(4, 3);
    /// matrix.swap_entries(0, 0, 2, 1);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if row or column are greater than the matrix size.
    pub fn swap_entries(
        &mut self,
        row_0: impl TryInto<i64> + Display,
        col_0: impl TryInto<i64> + Display,
        row_1: impl TryInto<i64> + Display,
        col_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        let (row_0, col_0) = evaluate_indices_for_matrix(self, row_0, col_0)?;
        let (row_1, col_1) = evaluate_indices_for_matrix(self, row_1, col_1)?;

        unsafe {
            fmpz_poly_swap(
                fmpz_poly_mat_entry(&self.matrix, row_0, col_0),
                fmpz_poly_mat_entry(&self.matrix, row_1, col_1),
            )
        };
        Ok(())
    }

    /// Swaps two columns of the specified matrix.
    ///
    /// Parameters:
    /// - `col_0`: specifies the first column which is swapped with the second one
    /// - `col_1`: specifies the second column which is swapped with the first one
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified columns is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mut matrix = MatPolyOverZ::new(4, 3);
    /// matrix.swap_columns(0, 2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if one of the given columns is greater than the matrix or negative.
    pub fn swap_columns(
        &mut self,
        col_0: impl TryInto<i64> + Display,
        col_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        let col_0 = evaluate_index(col_0)?;
        let col_1 = evaluate_index(col_1)?;
        if col_0 >= self.get_num_columns() || col_1 >= self.get_num_columns() {
            return Err(MathError::OutOfBounds(
                format!("smaller than {}", self.get_num_columns()),
                if col_0 > col_1 {
                    col_0.to_string()
                } else {
                    col_1.to_string()
                },
            ));
        }
        for row in 0..self.get_num_rows() {
            unsafe {
                let entry_0 = fmpz_poly_mat_entry(&self.matrix, row, col_0);
                let entry_1 = fmpz_poly_mat_entry(&self.matrix, row, col_1);
                fmpz_poly_swap(entry_0, entry_1);
            }
        }
        Ok(())
    }

    /// Swaps two rows of the specified matrix.
    ///
    /// Parameters:
    /// - `row_0`: specifies the first row which is swapped with the second one
    /// - `row_1`: specifies the second row which is swapped with the first one
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified rows is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mut matrix = MatPolyOverZ::new(4, 3);
    /// matrix.swap_rows(0, 2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if one of the given rows is greater than the matrix or negative.
    pub fn swap_rows(
        &mut self,
        row_0: impl TryInto<i64> + Display,
        row_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        let row_0 = evaluate_index(row_0)?;
        let row_1 = evaluate_index(row_1)?;
        if row_0 >= self.get_num_rows() || row_1 >= self.get_num_rows() {
            return Err(MathError::OutOfBounds(
                format!("smaller than {}", self.get_num_columns()),
                if row_0 > row_1 {
                    row_0.to_string()
                } else {
                    row_1.to_string()
                },
            ));
        }
        for col in 0..self.get_num_columns() {
            unsafe {
                let entry_0 = fmpz_poly_mat_entry(&self.matrix, row_0, col);
                let entry_1 = fmpz_poly_mat_entry(&self.matrix, row_1, col);
                fmpz_poly_swap(entry_0, entry_1);
            }
        }
        Ok(())
    }

    /// Swaps the `i`-th column with the `n-i`-th column for all `i <= n/2`
    /// of the specified matrix with `n` columns.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mut matrix = MatPolyOverZ::new(4, 3);
    /// matrix.reverse_columns();
    /// ```
    pub fn reverse_columns(&mut self) {
        let num_cols = self.get_num_columns();
        for col in 0..(num_cols / 2) {
            self.swap_columns(col, num_cols - col - 1).unwrap();
        }
    }

    /// Swaps the `i`-th row with the `n-i`-th row for all `i <= n/2`
    /// of the specified matrix with `n` rows.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mut matrix = MatPolyOverZ::new(4, 3);
    /// matrix.reverse_rows();
    /// ```
    pub fn reverse_rows(&mut self) {
        let num_rows = self.get_num_rows();
        for row in 0..(num_rows / 2) {
            self.swap_rows(row, num_rows - row - 1).unwrap();
        }
    }
}

#[cfg(test)]
mod test_setter {
    use crate::{
        integer::{MatPolyOverZ, PolyOverZ},
        traits::{GetEntry, SetEntry},
    };
    use std::str::FromStr;

    /// Ensure that setting entries works with standard numbers.
    #[test]
    fn standard_value() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str("2  889 1").unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!("2  889 1", entry.to_string());
    }

    /// Ensure that setting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MAX)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", i64::MAX), entry.to_string());
    }

    /// Ensure that setting entries works with large numbers (larger than i64).
    #[test]
    fn large_positive() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry.to_string());
    }

    /// Ensure that setting entries works with referenced large numbers (larger than i64).
    #[test]
    fn large_positive_ref() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value_1 = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        let value_2 = PolyOverZ::from_str("2  8 1").unwrap();
        matrix.set_entry(1, 1, &value_1).unwrap();
        matrix.set_entry(0, 0, value_2).unwrap();

        let entry_1 = matrix.get_entry(1, 1).unwrap();
        let entry_2 = matrix.get_entry(0, 0).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry_1.to_string());
        assert_eq!("2  8 1", entry_2.to_string());
    }

    /// Ensure that setting entries works with large negative numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MIN)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", i64::MIN), entry.to_string());
    }

    /// Ensure that setting entries works with large negative numbers (larger than i64).
    #[test]
    fn large_negative() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value_str = &format!("2  -{} 1", u64::MAX);
        let value = PolyOverZ::from_str(value_str).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(PolyOverZ::from_str(value_str).unwrap(), entry);
    }

    /// Ensure that setting entries at (0, 0) works.
    #[test]
    fn setting_at_zero() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        matrix.set_entry(0, 0, &value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry.to_string());
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::default();

        assert!(matrix.set_entry(5, 1, &value).is_err());
        assert!(matrix.set_entry(-6, 1, value).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::default();

        assert!(matrix.set_entry(1, 100, &value).is_err());
        assert!(matrix.set_entry(1, -11, value).is_err());
    }

    /// Ensure that negative indices return address the correct entires.
    #[test]
    fn negative_indexing() {
        let mut matrix = MatPolyOverZ::new(3, 3);

        matrix.set_entry(-1, -1, &PolyOverZ::from(9)).unwrap();
        matrix.set_entry(-1, -2, &PolyOverZ::from(8)).unwrap();
        matrix.set_entry(-3, -3, &PolyOverZ::from(1)).unwrap();

        let matrix_cmp =
            MatPolyOverZ::from_str("[[1  1, 0, 0],[0, 0, 0],[0, 1  8, 1  9]]").unwrap();
        assert_eq!(matrix_cmp, matrix);
    }

    /// Ensures that setting columns works fine for small entries
    #[test]
    fn column_small_entries() {
        let mut mat_1 = MatPolyOverZ::from_str("[[0, 1  2, 0],[0, 1  5, 1  6]]").unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[0],[1  -1]]").unwrap();
        let cmp = MatPolyOverZ::from_str("[[0, 0, 0],[0, 1  -1, 1  6]]").unwrap();

        let _ = mat_1.set_column(1, &mat_2, 0);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting columns works fine for large entries
    #[test]
    fn column_large_entries() {
        let mut mat_1 = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatPolyOverZ::from_str(&format!(
            "[[1  1, 1  {}],[1  {}, 0],[1  7, 1  -1]]",
            i64::MIN,
            i64::MAX
        ))
        .unwrap();
        let cmp = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[0, 1  4, 1  {}, 1  5],[1  -1, 1  6, 2  8 9, 0]]",
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        let _ = mat_1.set_column(0, &mat_2, 1);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting the column to itself does not change anything
    #[test]
    fn column_swap_same_entry() {
        let mut mat_1 = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = mat_1.clone();

        let _ = mat_1.set_column(0, &cmp, 0);
        let _ = mat_1.set_column(1, &cmp, 1);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that `set_column` returns an error if one of the specified columns is out of bounds
    #[test]
    fn column_out_of_bounds() {
        let mut mat_1 = MatPolyOverZ::new(5, 2);
        let mat_2 = mat_1.clone();

        assert!(mat_1.set_column(-1, &mat_2, 0).is_err());
        assert!(mat_1.set_column(2, &mat_2, 0).is_err());
        assert!(mat_1.set_column(1, &mat_2, -1).is_err());
        assert!(mat_1.set_column(1, &mat_2, 2).is_err());
    }

    /// Ensures that mismatching row dimensions result in an error
    #[test]
    fn column_mismatching_columns() {
        let mut mat_1 = MatPolyOverZ::new(5, 2);
        let mat_2 = MatPolyOverZ::new(2, 2);

        assert!(mat_1.set_column(0, &mat_2, 0).is_err());
        assert!(mat_1.set_column(1, &mat_2, 1).is_err());
    }

    /// Ensures that setting rows works fine for small entries
    #[test]
    fn row_small_entries() {
        let mut mat_1 = MatPolyOverZ::from_str("[[0, 1  2, 0],[0, 2  5 6, 0]]").unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[0, 1  -1, 1  2]]").unwrap();
        let cmp = MatPolyOverZ::from_str("[[0, 1  2, 0],[0, 1  -1, 1  2]]").unwrap();

        let _ = mat_1.set_row(1, &mat_2, 0);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting rows works fine for large entries
    #[test]
    fn row_large_entries() {
        let mut mat_1 = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatPolyOverZ::from_str(&format!(
            "[[0, 0, 0, 0],[1  {}, 0, 1  {}, 0]]",
            i64::MIN,
            i64::MAX
        ))
        .unwrap();
        let cmp = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 0, 1  {}, 0],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]]",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();

        let _ = mat_1.set_row(0, &mat_2, 1);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting the rows to itself does not change anything
    #[test]
    fn row_swap_same_entry() {
        let mut mat_1 = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = mat_1.clone();

        let _ = mat_1.set_row(0, &cmp, 0);
        let _ = mat_1.set_row(1, &cmp, 1);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that `set_row` returns an error if one of the specified rows is out of bounds
    #[test]
    fn row_out_of_bounds() {
        let mut mat_1 = MatPolyOverZ::new(5, 2);
        let mat_2 = mat_1.clone();

        assert!(mat_1.set_row(-1, &mat_2, 0).is_err());
        assert!(mat_1.set_row(5, &mat_2, 0).is_err());
        assert!(mat_1.set_row(2, &mat_2, -1).is_err());
        assert!(mat_1.set_row(2, &mat_2, 5).is_err());
    }

    /// Ensures that mismatching column dimensions result in an error
    #[test]
    fn row_mismatching_columns() {
        let mut mat_1 = MatPolyOverZ::new(3, 2);
        let mat_2 = MatPolyOverZ::new(3, 3);

        assert!(mat_1.set_row(0, &mat_2, 0).is_err());
        assert!(mat_1.set_row(1, &mat_2, 1).is_err());
    }
}

#[cfg(test)]
mod test_swaps {
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensures that swapping entries works fine for small entries
    #[test]
    fn entries_small_entries() {
        let mut matrix = MatPolyOverZ::from_str("[[1  1, 1  2, 1  3],[1  4, 2  5 6, 0]]").unwrap();
        let cmp = MatPolyOverZ::from_str("[[1  1, 2  5 6, 1  3],[1  4, 1  2, 0]]").unwrap();

        let _ = matrix.swap_entries(1, 1, 0, 1);

        assert_eq!(cmp, matrix);
    }

    /// Ensures that swapping entries works fine for large entries
    #[test]
    fn entries_large_entries() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]]",
            u64::MAX,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();

        let _ = matrix.swap_entries(0, 0, 1, 2);

        assert_eq!(cmp, matrix);
    }

    /// Ensures that swapping the same entry does not change anything
    #[test]
    fn entries_swap_same_entry() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = matrix.clone();

        let _ = matrix.swap_entries(0, 0, 0, 0);
        let _ = matrix.swap_entries(1, 1, 1, 1);

        assert_eq!(cmp, matrix);
    }

    /// Ensures that `swap_entries` returns an error if one of the specified entries is out of bounds
    #[test]
    fn entries_out_of_bounds() {
        let mut matrix = MatPolyOverZ::new(5, 2);

        assert!(matrix.swap_entries(-6, 0, 0, 0).is_err());
        assert!(matrix.swap_entries(0, -3, 0, 0).is_err());
        assert!(matrix.swap_entries(0, 0, 5, 0).is_err());
        assert!(matrix.swap_entries(0, 5, 0, 0).is_err());
    }

    /// Ensure that `swap_entries` can properly handle negative indexing.
    #[test]
    fn entries_negative_indexing() {
        let mut matrix = MatPolyOverZ::identity(2, 2);

        matrix.swap_entries(-2, -2, -2, -1).unwrap();
        assert_eq!("[[0, 1  1],[0, 1  1]]", matrix.to_string());
    }

    /// Ensures that swapping columns works fine for small entries
    #[test]
    fn columns_small_entries() {
        let mut matrix = MatPolyOverZ::from_str("[[1  1, 1  2, 1  3],[1  4, 1  5, 1  6]]").unwrap();
        let cmp_vec_0 = MatPolyOverZ::from_str("[[1  1],[1  4]]").unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[1  3],[1  6]]").unwrap();
        let cmp_vec_2 = MatPolyOverZ::from_str("[[1  2],[1  5]]").unwrap();

        let _ = matrix.swap_columns(1, 2);

        assert_eq!(cmp_vec_0, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(2).unwrap());
    }

    /// Ensures that swapping columns works fine for large entries
    #[test]
    fn columns_large_entries() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 7, 0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 =
            MatPolyOverZ::from_str(&format!("[[1  3],[1  {}],[2  8 7]]", u64::MAX)).unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[1  1],[1  4],[1  6]]").unwrap();
        let cmp_vec_2 =
            MatPolyOverZ::from_str(&format!("[[1  {}],[1  {}],[1  7]]", i64::MIN, i64::MAX))
                .unwrap();
        let cmp_vec_3 = MatPolyOverZ::from_str("[[1  4],[1  5],[0]]").unwrap();

        let _ = matrix.swap_columns(0, 2);

        assert_eq!(cmp_vec_0, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(2).unwrap());
        assert_eq!(cmp_vec_3, matrix.get_column(3).unwrap());
    }

    /// Ensures that swapping the same column does not change anything
    #[test]
    fn columns_swap_same_col() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 1  8, 1  9]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = matrix.clone();

        let _ = matrix.swap_columns(0, 0);

        assert_eq!(cmp, matrix);
    }

    /// Ensures that `swap_columns` returns an error if one of the specified columns is out of bounds
    #[test]
    fn column_out_of_bounds() {
        let mut matrix = MatPolyOverZ::new(5, 2);

        assert!(matrix.swap_columns(-1, 0).is_err());
        assert!(matrix.swap_columns(0, -1).is_err());
        assert!(matrix.swap_columns(5, 0).is_err());
        assert!(matrix.swap_columns(0, 5).is_err());
    }

    /// Ensures that swapping rows works fine for small entries
    #[test]
    fn rows_small_entries() {
        let mut matrix = MatPolyOverZ::from_str("[[1  1, 1  2],[1  3, 2  4 5]]").unwrap();
        let cmp_vec_0 = MatPolyOverZ::from_str("[[1  3, 2  4 5]]").unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[1  1, 1  2]]").unwrap();

        let _ = matrix.swap_rows(1, 0);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
    }

    /// Ensures that swapping rows works fine for large entries
    #[test]
    fn rows_large_entries() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  7, 1  6, 1  8, 0],[1  {}, 1  4, 1  {}, 1  5]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 =
            MatPolyOverZ::from_str(&format!("[[1  {}, 1  4, 1  {}, 1  5]]", i64::MAX, u64::MAX))
                .unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[1  7, 1  6, 1  8, 0]]").unwrap();
        let cmp_vec_2 =
            MatPolyOverZ::from_str(&format!("[[1  {}, 1  1, 1  3, 1  4]]", i64::MIN)).unwrap();

        let _ = matrix.swap_rows(0, 2);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_row(2).unwrap());
    }

    /// Ensures that swapping the same row does not change anything
    #[test]
    fn rows_swap_same_row() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 1  8, 1  9]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = matrix.clone();

        let _ = matrix.swap_rows(1, 1);

        assert_eq!(cmp, matrix);
    }

    /// Ensures that `swap_rows` returns an error if one of the specified rows is out of bounds
    #[test]
    fn row_out_of_bounds() {
        let mut matrix = MatPolyOverZ::new(2, 4);

        assert!(matrix.swap_rows(-1, 0).is_err());
        assert!(matrix.swap_rows(0, -1).is_err());
        assert!(matrix.swap_rows(4, 0).is_err());
        assert!(matrix.swap_rows(0, 4).is_err());
    }
}

#[cfg(test)]
mod test_reverses {
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensures that reversing columns works fine for small entries
    #[test]
    fn columns_small_entries() {
        let mut matrix = MatPolyOverZ::from_str("[[1  1, 1  2, 2  3 4],[0, 1  5, 1  6]]").unwrap();
        let cmp_vec_0 = MatPolyOverZ::from_str("[[1  1],[0]]").unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[1  2],[1  5]]").unwrap();
        let cmp_vec_2 = MatPolyOverZ::from_str("[[2  3 4],[1  6]]").unwrap();

        matrix.reverse_columns();

        assert_eq!(cmp_vec_2, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_column(2).unwrap());
    }

    /// Ensures that reversing columns works fine for large entries
    #[test]
    fn columns_large_entries() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 =
            MatPolyOverZ::from_str(&format!("[[1  {}],[1  {}],[1  7]]", i64::MIN, i64::MAX))
                .unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[1  1],[1  4],[1  6]]").unwrap();
        let cmp_vec_2 =
            MatPolyOverZ::from_str(&format!("[[1  3],[1  {}],[2  8 9]]", u64::MAX)).unwrap();
        let cmp_vec_3 = MatPolyOverZ::from_str("[[1  4],[1  5],[0]]").unwrap();

        matrix.reverse_columns();

        assert_eq!(cmp_vec_3, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(2).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_column(3).unwrap());
    }

    /// Ensures that reversing rows works fine for small entries
    #[test]
    fn rows_small_entries() {
        let mut matrix = MatPolyOverZ::from_str("[[1  1, 1  2],[2  3 4, 0]]").unwrap();
        let cmp_vec_0 = MatPolyOverZ::from_str("[[1  1, 1  2]]").unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[2  3 4, 0]]").unwrap();

        matrix.reverse_rows();

        assert_eq!(cmp_vec_1, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(1).unwrap());
    }

    /// Ensures that reversing rows works fine for large entries
    #[test]
    fn rows_large_entries() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  7, 1  6, 2  8 9, 0],[1  {}, 1  4, 1  {}, 1  5]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 =
            MatPolyOverZ::from_str(&format!("[[1  {}, 1  1, 1  3, 1  4]]", i64::MIN)).unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[1  7, 1  6, 2  8 9, 0]]").unwrap();
        let cmp_vec_2 =
            MatPolyOverZ::from_str(&format!("[[1  {}, 1  4, 1  {}, 1  5]]", i64::MAX, u64::MAX))
                .unwrap();

        matrix.reverse_rows();

        assert_eq!(cmp_vec_2, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(2).unwrap());
    }
}
