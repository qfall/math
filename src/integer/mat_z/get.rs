// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get entries from a [`MatZ`] matrix.

use super::MatZ;
use crate::{
    error::MathError,
    integer::Z,
    traits::{GetEntry, GetNumColumns, GetNumRows},
    utils::index::{evaluate_index, evaluate_indices},
};
use flint_sys::{
    fmpz::{fmpz, fmpz_set},
    fmpz_mat::fmpz_mat_entry,
};
use std::fmt::Display;

impl GetNumRows for MatZ {
    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatZ::new(5,6).unwrap();
    /// let rows = matrix.get_num_rows();
    /// ```
    fn get_num_rows(&self) -> i64 {
        self.matrix.r
    }
}

impl GetNumColumns for MatZ {
    /// Returns the number of columns of the matrix as a [`i64`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatZ::new(5,6).unwrap();
    /// let columns = matrix.get_num_columns();
    /// ```
    fn get_num_columns(&self) -> i64 {
        self.matrix.c
    }
}

impl GetEntry<Z> for MatZ {
    /// Outputs the [`Z`] value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Returns the [`Z`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::traits::GetEntry;
    ///
    /// let matrix = MatZ::new(5, 10).unwrap();
    /// let entry = matrix.get_entry(0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    fn get_entry(
        &self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
    ) -> Result<Z, MathError> {
        let (row_i64, column_i64) = evaluate_indices(self, row, column)?;

        // since `self.matrix` is a correct fmpz matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpz_set` can successfully clone the
        // entry of the matrix. Therefore no memory leaks can appear.
        let mut copy = fmpz(0);
        let entry = unsafe { fmpz_mat_entry(&self.matrix, row_i64, column_i64) };
        unsafe { fmpz_set(&mut copy, entry) };

        Ok(Z { value: copy })
    }
}

impl MatZ {
    /// Outputs the row vector of the specified row.
    ///
    /// Parameters:
    /// - `row`: specifies the row of the matrix
    ///
    /// Returns a row vector of the matrix at the position of the given
    /// row or an error, if the number of rows is
    /// greater than the matrix or negative.
    ///
    /// # Example
    /// ```rust
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
    ///
    /// let row0 = matrix.get_row(0).unwrap(); // first row
    /// let row1 = matrix.get_row(1).unwrap(); // second row
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of the row is greater than the matrix or negative.
    pub fn get_row(&self, row: impl TryInto<i64> + Display + Copy) -> Result<Self, MathError> {
        let row_i64 = evaluate_index(row)?;

        if self.get_num_rows() <= row_i64 {
            return Err(MathError::OutOfBounds(
                format!("be smaller than {}", self.get_num_rows()),
                format!("{}", row_i64),
            ));
        }

        let out = MatZ::new(1, self.get_num_columns()).unwrap();
        for column in 0..self.get_num_columns() {
            unsafe {
                fmpz_set(
                    fmpz_mat_entry(&out.matrix, 0, column),
                    fmpz_mat_entry(&self.matrix, row_i64, column),
                )
            };
        }
        Ok(out)
    }

    /// Outputs a column vector of the specified column.
    ///
    /// Input parameters:
    /// * `column`: specifies the column of the matrix
    ///
    /// Returns a column vector of the matrix at the position of the given
    /// column or an error, if the number of columns is
    /// greater than the matrix or negative.
    ///
    /// # Example
    /// ```rust
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
    ///
    /// let col0 = matrix.get_column(0).unwrap(); // first column
    /// let col1 = matrix.get_column(1).unwrap(); // second column
    /// let col2 = matrix.get_column(2).unwrap(); // third column
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of the column is greater than the matrix or negative.
    pub fn get_column(
        &self,
        column: impl TryInto<i64> + Display + Copy,
    ) -> Result<Self, MathError> {
        let column_i64 = evaluate_index(column)?;

        if self.get_num_columns() <= column_i64 {
            return Err(MathError::OutOfBounds(
                format!("be smaller than {}", self.get_num_columns()),
                format!("{}", column_i64),
            ));
        }

        let out = MatZ::new(self.get_num_rows(), 1).unwrap();
        for row in 0..self.get_num_rows() {
            unsafe {
                fmpz_set(
                    fmpz_mat_entry(&out.matrix, row, 0),
                    fmpz_mat_entry(&self.matrix, row, column_i64),
                )
            };
        }
        Ok(out)
    }

    /// Efficiently collects all [`fmpz`]s in a [`MatZ`] without cloning them.
    ///
    /// Hence, the values on the returned [`Vec`] are intended for short-term use
    /// as the access to [`fmpz`] values could lead to memory leaks or modified values
    /// once the [`MatZ`] instance was modified or dropped.
    ///
    /// # Example
    /// ```compile_fail
    /// use qfall_math::intger::MatZ;
    /// use std::str::FromStr;
    ///
    /// let mat = MatZ::from_str("[[1,2],[3,4],[5,6]]").unwrap();
    ///
    /// let fmpz_entries = mat.collect_entries();
    /// ```
    pub(crate) fn collect_entries(&self) -> Vec<fmpz> {
        let mut entries: Vec<fmpz> = vec![];

        for row in 0..self.get_num_rows() {
            for col in 0..self.get_num_columns() {
                // efficiently get entry without cloning the entry itself
                let entry = unsafe { *fmpz_mat_entry(&self.matrix, row, col) };
                entries.push(entry);
            }
        }

        entries
    }
}

#[cfg(test)]
mod test_get_entry {

    use super::Z;
    use crate::{
        integer::MatZ,
        traits::{GetEntry, SetEntry},
    };
    use std::str::FromStr;

    /// Ensure that getting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MAX);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from_i64(i64::MAX), entry);
    }

    /// Ensure that getting entries works with large numbers (larger than i64).
    #[test]
    fn big_positive() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from(u64::MAX);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from(u64::MAX), entry);
    }

    /// Ensure that getting entries works with large negative numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MIN);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from_i64(i64::MIN), entry);
    }

    /// Ensure that getting entries works with large negative numbers (larger than i64).
    #[test]
    fn big_negative() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value_str = &format!("-{}", u64::MAX);
        matrix
            .set_entry(1, 1, Z::from_str(value_str).unwrap())
            .unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from_str(value_str).unwrap(), entry);
    }

    /// Ensure that getting entries at (0,0) works.
    #[test]
    fn getting_at_zero() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MIN);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(entry, Z::from_i64(i64::MIN));
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let matrix = MatZ::new(5, 10).unwrap();

        assert!(matrix.get_entry(5, 1).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatZ::new(5, 10).unwrap();

        assert!(matrix.get_entry(1, 100).is_err());
    }

    /// Ensure that the entry is a deep copy and not just a clone of the reference.
    #[test]
    fn memory_test() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from(u64::MAX);
        matrix.set_entry(1, 1, value).unwrap();
        let entry = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(1, 1, Z::from_i64(0)).unwrap();

        assert_eq!(Z::from(u64::MAX), entry);
    }
}

#[cfg(test)]
mod test_get_num {

    use crate::{
        integer::MatZ,
        traits::{GetNumColumns, GetNumRows},
    };

    /// Ensure that the getter for rows works correctly.
    #[test]
    fn num_rows() {
        let matrix = MatZ::new(5, 10).unwrap();

        assert_eq!(matrix.get_num_rows(), 5);
    }

    /// Ensure that the getter for columns works correctly.
    #[test]
    fn num_columns() {
        let matrix = MatZ::new(5, 10).unwrap();

        assert_eq!(matrix.get_num_columns(), 10);
    }
}

#[cfg(test)]
mod test_get_vec {

    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensure that getting a row works
    #[test]
    fn get_row_works() {
        let matrix = MatZ::from_str(&format!("[[0,0,0],[4,{},{}]]", i64::MAX, i64::MIN)).unwrap();
        let row1 = matrix.get_row(0).unwrap();
        let row2 = matrix.get_row(1).unwrap();

        let cmp1 = MatZ::from_str("[[0,0,0]]").unwrap();
        let cmp2 = MatZ::from_str(&format!("[[4,{},{}]]", i64::MAX, i64::MIN)).unwrap();

        assert_eq!(cmp1, row1);
        assert_eq!(cmp2, row2);
    }

    /// Ensure that getting a column works
    #[test]
    fn get_column_works() {
        let matrix =
            MatZ::from_str(&format!("[[1,0,3],[{},0,5],[{},0,7]]", i64::MAX, i64::MIN)).unwrap();
        let column1 = matrix.get_column(0).unwrap();
        let column2 = matrix.get_column(1).unwrap();
        let column3 = matrix.get_column(2).unwrap();

        let cmp1 = MatZ::from_str(&format!("[[1],[{}],[{}]]", i64::MAX, i64::MIN)).unwrap();
        let cmp2 = MatZ::from_str("[[0],[0],[0]]").unwrap();
        let cmp3 = MatZ::from_str("[[3],[5],[7]]").unwrap();

        assert_eq!(cmp1, column1);
        assert_eq!(cmp2, column2);
        assert_eq!(cmp3, column3);
    }

    /// Ensure that wrong row and column dimensions yields an error
    #[test]
    fn wrong_dim_error() {
        let matrix =
            MatZ::from_str(&format!("[[1,2,3],[{},4,5],[{},6,7]]", i64::MAX, i64::MIN)).unwrap();
        let row1 = matrix.get_row(-1);
        let row2 = matrix.get_row(4);
        let column1 = matrix.get_column(-1);
        let column2 = matrix.get_column(4);

        assert!(row1.is_err());
        assert!(row2.is_err());
        assert!(column1.is_err());
        assert!(column2.is_err());
    }
}

#[cfg(test)]
mod test_collect_entries {
    use super::MatZ;
    use std::str::FromStr;

    #[test]
    fn all_entries_collected() {
        let mat_1 = MatZ::from_str(&format!("[[1,2],[{},{}],[3,4]]", i64::MAX, i64::MIN)).unwrap();
        let mat_2 = MatZ::from_str("[[-1,2]]").unwrap();

        let entries_1 = mat_1.collect_entries();
        let entries_2 = mat_2.collect_entries();

        assert_eq!(entries_1.len(), 6);
        assert_eq!(entries_1[0].0, 1);
        assert_eq!(entries_1[1].0, 2);
        assert!(entries_1[2].0 >= 2_i64.pow(62));
        assert!(entries_1[3].0 >= 2_i64.pow(62));
        assert_eq!(entries_1[4].0, 3);
        assert_eq!(entries_1[5].0, 4);

        assert_eq!(entries_2.len(), 2);
        assert_eq!(entries_2[0].0, -1);
        assert_eq!(entries_2[1].0, 2);
    }
}
