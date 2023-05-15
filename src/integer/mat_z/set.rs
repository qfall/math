// Copyright © 2023 Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation to set entries from a [`MatZ`] matrix.

use super::MatZ;
use crate::{
    error::MathError,
    integer::Z,
    macros::for_others::{implement_for_others, implement_for_owned},
    traits::{GetEntry, GetNumColumns, GetNumRows, SetEntry},
    utils::index::{evaluate_index, evaluate_indices},
};
use flint_sys::{
    fmpz::fmpz_set,
    fmpz_mat::{
        fmpz_mat_entry, fmpz_mat_invert_cols, fmpz_mat_invert_rows, fmpz_mat_swap_cols,
        fmpz_mat_swap_rows,
    },
};
use std::{
    fmt::Display,
    ptr::{null, null_mut},
};

impl SetEntry<&Z> for MatZ {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`Z`].
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
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::integer::Z;
    /// use qfall_math::traits::*;
    ///
    /// let mut matrix = MatZ::new(5, 10).unwrap();
    /// let value = Z::from(5);
    /// matrix.set_entry(1, 1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        value: &Z,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_indices(self, row, column)?;

        // since `self` is a correct matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpz_set` can successfully clone the
        // value inside the matrix. Therefore no memory leaks can appear.
        unsafe {
            let entry = fmpz_mat_entry(&self.matrix, row_i64, column_i64);
            fmpz_set(entry, &value.value)
        };

        Ok(())
    }
}

implement_for_owned!(Z, MatZ, SetEntry);

implement_for_others!(Z, MatZ, SetEntry for i8 i16 i32 i64 u8 u16 u32 u64);

impl MatZ {
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
    /// use qfall_math::integer::MatZ;
    ///
    /// let mut matrix = MatZ::new(4, 3).unwrap();
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

        let entry0 = self.get_entry(row0, col0)?;
        let entry1 = self.get_entry(row1, col1)?;

        self.set_entry(row0, col0, entry1)?;
        self.set_entry(row1, col1, entry0)?;
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
    /// use qfall_math::integer::MatZ;
    ///
    /// let mut matrix = MatZ::new(4, 3).unwrap();
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
        unsafe { fmpz_mat_swap_cols(&mut self.matrix, null(), col0, col1) }
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
    /// use qfall_math::integer::MatZ;
    ///
    /// let mut matrix = MatZ::new(4, 3).unwrap();
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
        unsafe { fmpz_mat_swap_rows(&mut self.matrix, null(), row0, row1) }
        Ok(())
    }

    /// Swaps the `i`-th column with the `n-i`-th column for all i <= n/2
    /// of the specified matrix with `n` columns.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let mut matrix = MatZ::new(4, 3).unwrap();
    /// matrix.reverse_columns();
    /// ```
    pub fn reverse_columns(&mut self) {
        // If the second argument to this function is not null, the permutation
        // of the columns is also applied to this argument.
        // Hence, passing in null is justified here.
        unsafe { fmpz_mat_invert_cols(&mut self.matrix, null_mut()) }
    }

    /// Swaps the `i`-th row with the `n-i`-th row for all i <= n/2
    /// of the specified matrix with `n` rows.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let mut matrix = MatZ::new(4, 3).unwrap();
    /// matrix.reverse_rows();
    /// ```
    pub fn reverse_rows(&mut self) {
        // If the second argument to this function is not null, the permutation
        // of the rows is also applied to this argument.
        // Hence, passing in null is justified here.
        unsafe { fmpz_mat_invert_rows(&mut self.matrix, null_mut()) }
    }
}

#[cfg(test)]
mod test_setter {
    use super::Z;
    use crate::integer::MatZ;
    use crate::traits::{GetEntry, SetEntry};
    use std::str::FromStr;

    /// Ensure that setting entries works with standard numbers.
    #[test]
    fn standard_value() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from(869);
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(entry, Z::from(869));
    }

    /// Ensure that setting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from(i64::MAX);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from(i64::MAX));
    }

    /// Ensure that setting entries works with large numbers (larger than i64).
    #[test]
    fn big_positive() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from(u64::MAX);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from(u64::MAX));
    }

    /// Ensure that setting entries works with referenced large numbers (larger than i64).
    #[test]
    fn big_positive_ref() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value1 = Z::from(u64::MAX);
        let value2 = Z::from(8);
        matrix.set_entry(1, 1, &value1).unwrap();
        matrix.set_entry(0, 0, value2).unwrap();

        let entry1 = matrix.get_entry(1, 1).unwrap();
        let entry2 = matrix.get_entry(0, 0).unwrap();

        assert_eq!(entry1, Z::from(u64::MAX));
        assert_eq!(entry2, Z::from(8));
    }

    /// Ensure that setting entries works with large negative numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from(i64::MIN);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from(i64::MIN));
    }

    /// Ensure that setting entries works with large negative numbers (larger than i64).
    #[test]
    fn big_negative() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value_str = &format!("-{}", u64::MAX);
        matrix
            .set_entry(1, 1, Z::from_str(value_str).unwrap())
            .unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from_str(value_str).unwrap());
    }

    /// Ensure that setting entries at (0,0) works.
    #[test]
    fn setting_at_zero() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from(i64::MIN);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(entry, Z::from(i64::MIN));
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from(i64::MAX);

        assert!(matrix.set_entry(5, 1, value).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from(i64::MAX);

        assert!(matrix.set_entry(1, 100, value).is_err());
    }
}

#[cfg(test)]
mod test_swaps {
    use super::MatZ;
    use std::str::FromStr;

    /// Ensures that swapping entries works fine for small entries
    #[test]
    fn entries_small_entries() {
        let mut matrix = MatZ::from_str("[[1,2,3],[4,5,6]]").unwrap();
        let cmp = MatZ::from_str("[[1,5,3],[4,2,6]]").unwrap();

        let _ = matrix.swap_entries(1, 1, 0, 1);

        assert_eq!(cmp, matrix);
    }

    /// Ensures that swapping entries works fine for large entries
    #[test]
    fn entries_large_entries() {
        let mut matrix = MatZ::from_str(&format!(
            "[[{},1,3, 4],[{},4,{},5],[7,6,8,9]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatZ::from_str(&format!(
            "[[{},1,3, 4],[{},4,{},5],[7,6,8,9]]",
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
        let mut matrix = MatZ::from_str(&format!(
            "[[{},1,3, 4],[{},4,{},5],[7,6,8,9]]",
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
        let mut matrix = MatZ::new(5, 2).unwrap();

        assert!(matrix.swap_entries(-1, 0, 0, 0).is_err());
        assert!(matrix.swap_entries(0, -1, 0, 0).is_err());
        assert!(matrix.swap_entries(0, 0, 5, 0).is_err());
        assert!(matrix.swap_entries(0, 5, 0, 0).is_err());
    }

    /// Ensures that swapping columns works fine for small entries
    #[test]
    fn columns_small_entries() {
        let mut matrix = MatZ::from_str("[[1,2,3],[4,5,6]]").unwrap();
        let cmp_vec_0 = MatZ::from_str("[[1],[4]]").unwrap();
        let cmp_vec_1 = MatZ::from_str("[[3],[6]]").unwrap();
        let cmp_vec_2 = MatZ::from_str("[[2],[5]]").unwrap();

        let _ = matrix.swap_columns(1, 2);

        assert_eq!(cmp_vec_0, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(2).unwrap());
    }

    /// Ensures that swapping columns works fine for large entries
    #[test]
    fn columns_large_entries() {
        let mut matrix = MatZ::from_str(&format!(
            "[[{},1,3, 4],[{},4,{},5],[7,6,8,9]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 = MatZ::from_str(&format!("[[3],[{}],[8]]", u64::MAX)).unwrap();
        let cmp_vec_1 = MatZ::from_str("[[1],[4],[6]]").unwrap();
        let cmp_vec_2 = MatZ::from_str(&format!("[[{}],[{}],[7]]", i64::MIN, i64::MAX)).unwrap();
        let cmp_vec_3 = MatZ::from_str("[[4],[5],[9]]").unwrap();

        let _ = matrix.swap_columns(0, 2);

        assert_eq!(cmp_vec_0, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(2).unwrap());
        assert_eq!(cmp_vec_3, matrix.get_column(3).unwrap());
    }

    /// Ensures that swapping the same column does not change anything
    #[test]
    fn columns_swap_same_col() {
        let mut matrix = MatZ::from_str(&format!(
            "[[{},1,3, 4],[{},4,{},5],[7,6,8,9]]",
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
        let mut matrix = MatZ::new(5, 2).unwrap();

        assert!(matrix.swap_columns(-1, 0).is_err());
        assert!(matrix.swap_columns(0, -1).is_err());
        assert!(matrix.swap_columns(5, 0).is_err());
        assert!(matrix.swap_columns(0, 5).is_err());
    }

    /// Ensures that swapping rows works fine for small entries
    #[test]
    fn rows_small_entries() {
        let mut matrix = MatZ::from_str("[[1,2],[3,4]]").unwrap();
        let cmp_vec_0 = MatZ::from_str("[[3,4]]").unwrap();
        let cmp_vec_1 = MatZ::from_str("[[1,2]]").unwrap();

        let _ = matrix.swap_rows(1, 0);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
    }

    /// Ensures that swapping rows works fine for large entries
    #[test]
    fn rows_large_entries() {
        let mut matrix = MatZ::from_str(&format!(
            "[[{},1,3, 4],[7,6,8,9],[{},4,{},5]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 = MatZ::from_str(&format!("[[{},4,{},5]]", i64::MAX, u64::MAX)).unwrap();
        let cmp_vec_1 = MatZ::from_str("[[7,6,8,9]]").unwrap();
        let cmp_vec_2 = MatZ::from_str(&format!("[[{},1,3, 4]]", i64::MIN)).unwrap();

        let _ = matrix.swap_rows(0, 2);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_row(2).unwrap());
    }

    /// Ensures that swapping the same row does not change anything
    #[test]
    fn rows_swap_same_row() {
        let mut matrix = MatZ::from_str(&format!(
            "[[{},1,3, 4],[{},4,{},5],[7,6,8,9]]",
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
        let mut matrix = MatZ::new(2, 4).unwrap();

        assert!(matrix.swap_rows(-1, 0).is_err());
        assert!(matrix.swap_rows(0, -1).is_err());
        assert!(matrix.swap_rows(4, 0).is_err());
        assert!(matrix.swap_rows(0, 4).is_err());
    }
}

#[cfg(test)]
mod test_reverses {
    use super::MatZ;
    use std::str::FromStr;

    /// Ensures that reversing columns works fine for small entries
    #[test]
    fn columns_small_entries() {
        let mut matrix = MatZ::from_str("[[1,2,3],[4,5,6]]").unwrap();
        let cmp_vec_0 = MatZ::from_str("[[1],[4]]").unwrap();
        let cmp_vec_1 = MatZ::from_str("[[2],[5]]").unwrap();
        let cmp_vec_2 = MatZ::from_str("[[3],[6]]").unwrap();

        matrix.reverse_columns();

        assert_eq!(cmp_vec_2, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_column(2).unwrap());
    }

    /// Ensures that reversing columns works fine for large entries
    #[test]
    fn columns_large_entries() {
        let mut matrix = MatZ::from_str(&format!(
            "[[{},1,3, 4],[{},4,{},5],[7,6,8,9]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 = MatZ::from_str(&format!("[[{}],[{}],[7]]", i64::MIN, i64::MAX)).unwrap();
        let cmp_vec_1 = MatZ::from_str("[[1],[4],[6]]").unwrap();
        let cmp_vec_2 = MatZ::from_str(&format!("[[3],[{}],[8]]", u64::MAX)).unwrap();
        let cmp_vec_3 = MatZ::from_str("[[4],[5],[9]]").unwrap();

        let _ = matrix.reverse_columns();

        assert_eq!(cmp_vec_3, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(2).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_column(3).unwrap());
    }

    /// Ensures that reversing rows works fine for small entries
    #[test]
    fn rows_small_entries() {
        let mut matrix = MatZ::from_str("[[1,2],[3,4]]").unwrap();
        let cmp_vec_0 = MatZ::from_str("[[1,2]]").unwrap();
        let cmp_vec_1 = MatZ::from_str("[[3,4]]").unwrap();

        let _ = matrix.reverse_rows();

        assert_eq!(cmp_vec_1, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(1).unwrap());
    }

    /// Ensures that reversing rows works fine for large entries
    #[test]
    fn rows_large_entries() {
        let mut matrix = MatZ::from_str(&format!(
            "[[{},1,3, 4],[7,6,8,9],[{},4,{},5]]",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 = MatZ::from_str(&format!("[[{},1,3, 4]]", i64::MIN)).unwrap();
        let cmp_vec_1 = MatZ::from_str("[[7,6,8,9]]").unwrap();
        let cmp_vec_2 = MatZ::from_str(&format!("[[{},4,{},5]]", i64::MAX, u64::MAX)).unwrap();

        let _ = matrix.reverse_rows();

        assert_eq!(cmp_vec_2, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(2).unwrap());
    }
}
