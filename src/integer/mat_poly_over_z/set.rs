// Copyright © 2023 Marvin Beckmann, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation to set entries from a [`MatPolyOverZ`] matrix.

use super::MatPolyOverZ;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::index::{evaluate_index, evaluate_indices},
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
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if the specified entry is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::traits::*;
    ///
    /// let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
    /// let value = PolyOverZ::default();
    /// matrix.set_entry(1, 1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        value: &PolyOverZ,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_indices(self, row, column)?;

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

impl SetEntry<PolyOverZ> for MatPolyOverZ {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::traits::*;
    ///
    /// let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
    /// let value = PolyOverZ::default();
    /// matrix.set_entry(1, 1, value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        mut value: PolyOverZ,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_indices(self, row, column)?;

        // swapping the content of the entry with the given value since ownership
        // of the input is provided.
        unsafe {
            let entry = fmpz_poly_mat_entry(&self.matrix, row_i64, column_i64);
            fmpz_poly_swap(entry, &mut value.poly)
        }
        Ok(())
    }
}

impl MatPolyOverZ {
    /// Sets a column of the given matrix to the provided column of `other`.
    ///
    /// Parameters:
    /// - `col0`: specifies the column of `self` that should be modified
    /// - `other`: specifies the matrix providing the column replacing the column in `self`
    /// - `col1`: specifies the column of `other` providing
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
    /// let mut mat1 = MatPolyOverZ::new(2, 2).unwrap();
    /// let mat2 = MatPolyOverZ::from_str("[[1  1],[0]]").unwrap();
    /// mat1.set_column(1, &mat2, 0);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of columns is greater than the matrix dimensions or negative.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of rows of `self` and `other` differ.
    pub fn set_column(
        &mut self,
        col0: impl TryInto<i64> + Display,
        other: &Self,
        col1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        let col0 = evaluate_index(col0)?;
        let col1 = evaluate_index(col1)?;
        if col0 >= self.get_num_columns() {
            return Err(MathError::OutOfBounds(
                format!("smaller than {}", self.get_num_columns()),
                col0.to_string(),
            ));
        }
        if col1 >= other.get_num_columns() {
            return Err(MathError::OutOfBounds(
                format!("smaller than {}", other.get_num_columns()),
                col1.to_string(),
            ));
        }
        if self.get_num_rows() != other.get_num_rows() {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "as set_column was called on two matrices with different number of rows {} and {}",
                self.get_num_rows(),
                other.get_num_rows()
            )));
        }

        for row in 0..self.get_num_rows() {
            unsafe {
                fmpz_poly_set(
                    fmpz_poly_mat_entry(&self.matrix, row, col0),
                    fmpz_poly_mat_entry(&other.matrix, row, col1),
                )
            };
        }

        Ok(())
    }

    /// Sets a row of the given matrix to the provided row of `other`.
    ///
    /// Parameters:
    /// - `row0`: specifies the row of `self` that should be modified
    /// - `other`: specifies the matrix providing the row replacing the row in `self`
    /// - `row1`: specifies the row of `other` providing
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
    /// let mut mat1 = MatPolyOverZ::new(2, 2).unwrap();
    /// let mat2 = MatPolyOverZ::from_str("[[1  1,0]]").unwrap();
    /// mat1.set_row(0, &mat2, 0);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows is greater than the matrix dimensions or negative.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of columns of `self` and `other` differ.
    pub fn set_row(
        &mut self,
        row0: impl TryInto<i64> + Display,
        other: &Self,
        row1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        let row0 = evaluate_index(row0)?;
        let row1 = evaluate_index(row1)?;
        if row0 >= self.get_num_rows() {
            return Err(MathError::OutOfBounds(
                format!("smaller than {}", self.get_num_rows()),
                row0.to_string(),
            ));
        }
        if row1 >= other.get_num_rows() {
            return Err(MathError::OutOfBounds(
                format!("smaller than {}", other.get_num_rows()),
                row1.to_string(),
            ));
        }
        if self.get_num_columns() != other.get_num_columns() {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "as set_column was called on two matrices with different number of columns {} and {}",
                self.get_num_columns(),
                other.get_num_columns()
            )));
        }

        for col in 0..self.get_num_columns() {
            unsafe {
                fmpz_poly_set(
                    fmpz_poly_mat_entry(&self.matrix, row0, col),
                    fmpz_poly_mat_entry(&other.matrix, row1, col),
                )
            };
        }

        Ok(())
    }

    /// Swaps two entries of the specified matrix.
    ///
    /// Parameters:
    /// - `row0`: specifies the row, in which the first entry is located
    /// - `col0`: specifies the column, in which the first entry is located
    /// - `row1`: specifies the row, in which the second entry is located
    /// - `col1`: specifies the column, in which the second entry is located
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified entries is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mut matrix = MatPolyOverZ::new(4, 3).unwrap();
    /// matrix.swap_entries(0, 0, 2, 1);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    pub fn swap_entries(
        &mut self,
        row0: impl TryInto<i64> + Display,
        col0: impl TryInto<i64> + Display,
        row1: impl TryInto<i64> + Display,
        col1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        let (row0, col0) = evaluate_indices(self, row0, col0)?;
        let (row1, col1) = evaluate_indices(self, row1, col1)?;

        unsafe {
            fmpz_poly_swap(
                fmpz_poly_mat_entry(&self.matrix, row0, col0),
                fmpz_poly_mat_entry(&self.matrix, row1, col1),
            )
        };
        Ok(())
    }

    /// Swaps two columns of the specified matrix.
    ///
    /// Parameters:
    /// - `col0`: specifies the first column which is swapped with the second one
    /// - `col1`: specifies the second column which is swapped with the first one
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified columns is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mut matrix = MatPolyOverZ::new(4, 3).unwrap();
    /// matrix.swap_columns(0, 2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if one of the given columns is greater than the matrix or negative.
    pub fn swap_columns(
        &mut self,
        col0: impl TryInto<i64> + Display,
        col1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        let col0 = evaluate_index(col0)?;
        let col1 = evaluate_index(col1)?;
        if col0 >= self.get_num_columns() || col1 >= self.get_num_columns() {
            return Err(MathError::OutOfBounds(
                format!("smaller than {}", self.get_num_columns()),
                if col0 > col1 {
                    col0.to_string()
                } else {
                    col1.to_string()
                },
            ));
        }
        for row in 0..self.get_num_rows() {
            unsafe {
                let entry0 = fmpz_poly_mat_entry(&self.matrix, row, col0);
                let entry1 = fmpz_poly_mat_entry(&self.matrix, row, col1);
                fmpz_poly_swap(entry0, entry1);
            }
        }
        Ok(())
    }

    /// Swaps two rows of the specified matrix.
    ///
    /// Parameters:
    /// - `row0`: specifies the first row which is swapped with the second one
    /// - `row1`: specifies the second row which is swapped with the first one
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified rows is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mut matrix = MatPolyOverZ::new(4, 3).unwrap();
    /// matrix.swap_rows(0, 2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if one of the given rows is greater than the matrix or negative.
    pub fn swap_rows(
        &mut self,
        row0: impl TryInto<i64> + Display,
        row1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        let row0 = evaluate_index(row0)?;
        let row1 = evaluate_index(row1)?;
        if row0 >= self.get_num_rows() || row1 >= self.get_num_rows() {
            return Err(MathError::OutOfBounds(
                format!("smaller than {}", self.get_num_columns()),
                if row0 > row1 {
                    row0.to_string()
                } else {
                    row1.to_string()
                },
            ));
        }
        for col in 0..self.get_num_columns() {
            unsafe {
                let entry0 = fmpz_poly_mat_entry(&self.matrix, row0, col);
                let entry1 = fmpz_poly_mat_entry(&self.matrix, row1, col);
                fmpz_poly_swap(entry0, entry1);
            }
        }
        Ok(())
    }

    /// Swaps the `i`-th column with the `n-i`-th column for all i <= n/2
    /// of the specified matrix with `n` columns.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mut matrix = MatPolyOverZ::new(4, 3).unwrap();
    /// matrix.reverse_columns();
    /// ```
    pub fn reverse_columns(&mut self) {
        let num_cols = self.get_num_columns();
        for col in 0..(num_cols / 2) {
            self.swap_columns(col, num_cols - col - 1).unwrap();
        }
    }

    /// Swaps the `i`-th row with the `n-i`-th row for all i <= n/2
    /// of the specified matrix with `n` rows.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mut matrix = MatPolyOverZ::new(4, 3).unwrap();
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
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", 889)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", 889), entry.to_string());
    }

    /// Ensure that setting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MAX)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", i64::MAX), entry.to_string());
    }

    /// Ensure that setting entries works with large numbers (larger than i64).
    #[test]
    fn big_positive() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry.to_string());
    }

    /// Ensure that setting entries works with referenced large numbers (larger than i64).
    #[test]
    fn big_positive_ref() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value1 = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        let value2 = PolyOverZ::from_str(&format!("2  {} 1", 8)).unwrap();
        matrix.set_entry(1, 1, &value1).unwrap();
        matrix.set_entry(0, 0, value2).unwrap();

        let entry1 = matrix.get_entry(1, 1).unwrap();
        let entry2 = matrix.get_entry(0, 0).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry1.to_string());
        assert_eq!(format!("2  {} 1", 8), entry2.to_string());
    }

    /// Ensure that setting entries works with large negative numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MIN)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", i64::MIN), entry.to_string());
    }

    /// Ensure that setting entries works with large negative numbers (larger than i64).
    #[test]
    fn big_negative() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value_str = &format!("2  -{} 1", u64::MAX);
        let value = PolyOverZ::from_str(value_str).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(PolyOverZ::from_str(value_str).unwrap(), entry);
    }

    /// Ensure that setting entries at (0,0) works.
    #[test]
    fn setting_at_zero() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        matrix.set_entry(0, 0, &value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry.to_string());
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::default();

        assert!(matrix.set_entry(5, 1, value).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::default();

        assert!(matrix.set_entry(1, 100, value).is_err());
    }

    /// Ensures that setting columns works fine for small entries
    #[test]
    fn column_small_entries() {
        let mut m1 = MatPolyOverZ::from_str("[[0,1  2,0],[0,1  5,1  6]]").unwrap();
        let m2 = MatPolyOverZ::from_str("[[0],[1  -1]]").unwrap();
        let cmp = MatPolyOverZ::from_str("[[0,0,0],[0,1  -1,1  6]]").unwrap();

        let _ = m1.set_column(1, &m2, 0);

        assert_eq!(cmp, m1);
    }

    /// Ensures that setting columns works fine for large entries
    #[test]
    fn column_large_entries() {
        let mut m1 = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,2  8 9, 0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let m2 = MatPolyOverZ::from_str(&format!(
            "[[1  1,1  {}],[1  {},0],[1  7,1  -1]]",
            i64::MIN,
            i64::MAX
        ))
        .unwrap();
        let cmp = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  1,1  3,1  4],[0,1  4,1  {},1  5],[1  -1,1  6,2  8 9,0]]",
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        let _ = m1.set_column(0, &m2, 1);

        assert_eq!(cmp, m1);
    }

    /// Ensures that setting the column to itself does not change anything
    #[test]
    fn column_swap_same_entry() {
        let mut m1 = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,2  8 9,0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = m1.clone();

        let _ = m1.set_column(0, &cmp, 0);
        let _ = m1.set_column(1, &cmp, 1);

        assert_eq!(cmp, m1);
    }

    /// Ensures that `set_column` returns an error if one of the specified columns is out of bounds
    #[test]
    fn column_out_of_bounds() {
        let mut m1 = MatPolyOverZ::new(5, 2).unwrap();
        let m2 = m1.clone();

        assert!(m1.set_column(-1, &m2, 0).is_err());
        assert!(m1.set_column(2, &m2, 0).is_err());
        assert!(m1.set_column(1, &m2, -1).is_err());
        assert!(m1.set_column(1, &m2, 2).is_err());
    }

    /// Ensures that mismatching row dimensions result in an error
    #[test]
    fn column_mismatching_columns() {
        let mut m1 = MatPolyOverZ::new(5, 2).unwrap();
        let m2 = MatPolyOverZ::new(2, 2).unwrap();

        assert!(m1.set_column(0, &m2, 0).is_err());
        assert!(m1.set_column(1, &m2, 1).is_err());
    }

    /// Ensures that setting rows works fine for small entries
    #[test]
    fn row_small_entries() {
        let mut m1 = MatPolyOverZ::from_str("[[0,1  2,0],[0,2  5 6,0]]").unwrap();
        let m2 = MatPolyOverZ::from_str("[[0,1  -1,1  2]]").unwrap();
        let cmp = MatPolyOverZ::from_str("[[0,1  2,0],[0,1  -1,1  2]]").unwrap();

        let _ = m1.set_row(1, &m2, 0);

        assert_eq!(cmp, m1);
    }

    /// Ensures that setting rows works fine for large entries
    #[test]
    fn row_large_entries() {
        let mut m1 = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,2  8 9,0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let m2 = MatPolyOverZ::from_str(&format!(
            "[[0,0,0,0],[1  {},0,1  {},0]]",
            i64::MIN,
            i64::MAX
        ))
        .unwrap();
        let cmp = MatPolyOverZ::from_str(&format!(
            "[[1  {},0,1  {},0],[1  {},1  4,1  {},1  5],[1  7,1  6,2  8 9,0]]",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();

        let _ = m1.set_row(0, &m2, 1);

        assert_eq!(cmp, m1);
    }

    /// Ensures that setting the rows to itself does not change anything
    #[test]
    fn row_swap_same_entry() {
        let mut m1 = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,2  8 9,0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = m1.clone();

        let _ = m1.set_row(0, &cmp, 0);
        let _ = m1.set_row(1, &cmp, 1);

        assert_eq!(cmp, m1);
    }

    /// Ensures that `set_row` returns an error if one of the specified rows is out of bounds
    #[test]
    fn row_out_of_bounds() {
        let mut m1 = MatPolyOverZ::new(5, 2).unwrap();
        let m2 = m1.clone();

        assert!(m1.set_row(-1, &m2, 0).is_err());
        assert!(m1.set_row(5, &m2, 0).is_err());
        assert!(m1.set_row(2, &m2, -1).is_err());
        assert!(m1.set_row(2, &m2, 5).is_err());
    }

    /// Ensures that mismatching column dimensions result in an error
    #[test]
    fn row_mismatching_columns() {
        let mut m1 = MatPolyOverZ::new(3, 2).unwrap();
        let m2 = MatPolyOverZ::new(3, 3).unwrap();

        assert!(m1.set_row(0, &m2, 0).is_err());
        assert!(m1.set_row(1, &m2, 1).is_err());
    }
}

#[cfg(test)]
mod test_swaps {
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensures that swapping entries works fine for small entries
    #[test]
    fn entries_small_entries() {
        let mut matrix = MatPolyOverZ::from_str("[[1  1,1  2,1  3],[1  4,2  5 6,0]]").unwrap();
        let cmp = MatPolyOverZ::from_str("[[1  1,2  5 6,1  3],[1  4,1  2,0]]").unwrap();

        let _ = matrix.swap_entries(1, 1, 0, 1);

        assert_eq!(cmp, matrix);
    }

    /// Ensures that swapping entries works fine for large entries
    #[test]
    fn entries_large_entries() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,2  8 9,0]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,2  8 9,0]]",
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
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,2  8 9,0]]",
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
        let mut matrix = MatPolyOverZ::new(5, 2).unwrap();

        assert!(matrix.swap_entries(-1, 0, 0, 0).is_err());
        assert!(matrix.swap_entries(0, -1, 0, 0).is_err());
        assert!(matrix.swap_entries(0, 0, 5, 0).is_err());
        assert!(matrix.swap_entries(0, 5, 0, 0).is_err());
    }

    /// Ensures that swapping columns works fine for small entries
    #[test]
    fn columns_small_entries() {
        let mut matrix = MatPolyOverZ::from_str("[[1  1,1  2,1  3],[1  4,1  5,1  6]]").unwrap();
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
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,2  8 7,0]]",
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
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,1  8,1  9]]",
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
        let mut matrix = MatPolyOverZ::new(5, 2).unwrap();

        assert!(matrix.swap_columns(-1, 0).is_err());
        assert!(matrix.swap_columns(0, -1).is_err());
        assert!(matrix.swap_columns(5, 0).is_err());
        assert!(matrix.swap_columns(0, 5).is_err());
    }

    /// Ensures that swapping rows works fine for small entries
    #[test]
    fn rows_small_entries() {
        let mut matrix = MatPolyOverZ::from_str("[[1  1,1  2],[1  3,2  4 5]]").unwrap();
        let cmp_vec_0 = MatPolyOverZ::from_str("[[1  3,2  4 5]]").unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[1  1,1  2]]").unwrap();

        let _ = matrix.swap_rows(1, 0);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
    }

    /// Ensures that swapping rows works fine for large entries
    #[test]
    fn rows_large_entries() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  1,1  3,1  4],[1  7,1  6,1  8,0],[1  {},1  4,1  {},1  5]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 =
            MatPolyOverZ::from_str(&format!("[[1  {},1  4,1  {},1  5]]", i64::MAX, u64::MAX))
                .unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[1  7,1  6,1  8,0]]").unwrap();
        let cmp_vec_2 =
            MatPolyOverZ::from_str(&format!("[[1  {},1  1,1  3,1  4]]", i64::MIN)).unwrap();

        let _ = matrix.swap_rows(0, 2);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_row(2).unwrap());
    }

    /// Ensures that swapping the same row does not change anything
    #[test]
    fn rows_swap_same_row() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,1  8,1  9]]",
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
        let mut matrix = MatPolyOverZ::new(2, 4).unwrap();

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
        let mut matrix = MatPolyOverZ::from_str("[[1  1,1  2,2  3 4],[0,1  5,1  6]]").unwrap();
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
            "[[1  {},1  1,1  3,1  4],[1  {},1  4,1  {},1  5],[1  7,1  6,2  8 9,0]]",
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

        let _ = matrix.reverse_columns();

        assert_eq!(cmp_vec_3, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(2).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_column(3).unwrap());
    }

    /// Ensures that reversing rows works fine for small entries
    #[test]
    fn rows_small_entries() {
        let mut matrix = MatPolyOverZ::from_str("[[1  1,1  2],[2  3 4,0]]").unwrap();
        let cmp_vec_0 = MatPolyOverZ::from_str("[[1  1,1  2]]").unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[2  3 4,0]]").unwrap();

        let _ = matrix.reverse_rows();

        assert_eq!(cmp_vec_1, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(1).unwrap());
    }

    /// Ensures that reversing rows works fine for large entries
    #[test]
    fn rows_large_entries() {
        let mut matrix = MatPolyOverZ::from_str(&format!(
            "[[1  {},1  1,1  3,1  4],[1  7,1  6,2  8 9,0],[1  {},1  4,1  {},1  5]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 =
            MatPolyOverZ::from_str(&format!("[[1  {},1  1,1  3,1  4]]", i64::MIN)).unwrap();
        let cmp_vec_1 = MatPolyOverZ::from_str("[[1  7,1  6,2  8 9,0]]").unwrap();
        let cmp_vec_2 =
            MatPolyOverZ::from_str(&format!("[[1  {},1  4,1  {},1  5]]", i64::MAX, u64::MAX))
                .unwrap();

        let _ = matrix.reverse_rows();

        assert_eq!(cmp_vec_2, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(2).unwrap());
    }
}
