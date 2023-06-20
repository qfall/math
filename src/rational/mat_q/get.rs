// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`MatQ`] matrix.

use super::MatQ;
use crate::traits::{GetEntry, GetNumColumns, GetNumRows};
use crate::utils::index::{evaluate_index, evaluate_indices_for_matrix};
use crate::{error::MathError, rational::Q};
use flint_sys::{
    fmpq::{fmpq, fmpq_set},
    fmpq_mat::fmpq_mat_entry,
};
use std::fmt::Display;

impl GetNumRows for MatQ {
    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatQ::new(5,6);
    /// let rows = matrix.get_num_rows();
    /// ```
    fn get_num_rows(&self) -> i64 {
        self.matrix.r
    }
}

impl GetNumColumns for MatQ {
    /// Returns the number of columns of the matrix as a [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatQ::new(5,6);
    /// let columns = matrix.get_num_columns();
    /// ```
    fn get_num_columns(&self) -> i64 {
        self.matrix.c
    }
}

impl GetEntry<Q> for MatQ {
    /// Outputs the [`Q`] value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Returns the [`Q`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::traits::GetEntry;
    ///
    /// let matrix = MatQ::new(5, 10);
    /// let entry = matrix.get_entry(0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    fn get_entry(
        &self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
    ) -> Result<Q, MathError> {
        let (row_i64, column_i64) = evaluate_indices_for_matrix(self, row, column)?;

        // since `self.matrix` is a correct fmpq matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpq_set` can successfully clone the
        // entry of the matrix. Therefore no memory leaks can appear.
        let mut copy = Q::default();
        let entry = unsafe { fmpq_mat_entry(&self.matrix, row_i64, column_i64) };
        unsafe { fmpq_set(&mut copy.value, entry) };

        Ok(copy)
    }
}

impl MatQ {
    /// Outputs the row vector of the specified row.
    ///
    /// Parameters:
    /// - `row`: specifies the row of the matrix
    ///
    /// Returns a row vector of the matrix at the position of the given
    /// row or an error, if the number of rows is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[1, 2/3, 3],[3, 4, 5/2]]").unwrap();
    ///
    /// let row0 = matrix.get_row(0).unwrap(); // first row
    /// let row1 = matrix.get_row(1).unwrap(); // second row
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of the row is greater than the matrix or negative.
    pub fn get_row(&self, row: impl TryInto<i64> + Display) -> Result<Self, MathError> {
        let row_i64 = evaluate_index(row)?;

        if self.get_num_rows() <= row_i64 {
            return Err(MathError::OutOfBounds(
                format!("be smaller than {}", self.get_num_rows()),
                format!("{}", row_i64),
            ));
        }

        let out = MatQ::new(1, self.get_num_columns());
        for column in 0..self.get_num_columns() {
            unsafe {
                fmpq_set(
                    fmpq_mat_entry(&out.matrix, 0, column),
                    fmpq_mat_entry(&self.matrix, row_i64, column),
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
    /// # Examples
    /// ```rust
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[1, 2/3, 3],[3, 4, 5/2]]").unwrap();
    ///
    /// let col0 = matrix.get_column(0).unwrap(); // first column
    /// let col1 = matrix.get_column(1).unwrap(); // second column
    /// let col2 = matrix.get_column(2).unwrap(); // third column
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of the column is greater than the matrix or negative.
    pub fn get_column(&self, column: impl TryInto<i64> + Display) -> Result<Self, MathError> {
        let column_i64 = evaluate_index(column)?;

        if self.get_num_columns() <= column_i64 {
            return Err(MathError::OutOfBounds(
                format!("be smaller than {}", self.get_num_columns()),
                format!("{}", column_i64),
            ));
        }

        let out = MatQ::new(self.get_num_rows(), 1);
        for row in 0..self.get_num_rows() {
            unsafe {
                fmpq_set(
                    fmpq_mat_entry(&out.matrix, row, 0),
                    fmpq_mat_entry(&self.matrix, row, column_i64),
                )
            };
        }
        Ok(out)
    }

    /// Efficiently collects all [`fmpq`]s in a [`MatQ`] without cloning them.
    ///
    /// Hence, the values on the returned [`Vec`] are intended for short-term use
    /// as the access to [`fmpq`] values could lead to memory leaks or modified values
    /// once the [`MatQ`] instance was modified or dropped.
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let mat = MatQ::from_str("[[1/1,2],[3/1,4],[5/1,6]]").unwrap();
    ///
    /// let fmpz_entries = mat.collect_entries();
    /// ```
    pub(crate) fn collect_entries(&self) -> Vec<fmpq> {
        let mut entries: Vec<fmpq> = vec![];

        for row in 0..self.get_num_rows() {
            for col in 0..self.get_num_columns() {
                // efficiently get entry without cloning the entry itself
                let entry = unsafe { *fmpq_mat_entry(&self.matrix, row, col) };
                entries.push(entry);
            }
        }

        entries
    }
}

#[cfg(test)]
mod test_get_entry {
    use super::Q;
    use crate::{
        rational::MatQ,
        traits::{GetEntry, SetEntry},
    };
    use std::str::FromStr;

    /// Ensure that getting entries works with large large numerators and denominators.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatQ::new(5, 10);
        let value1 = Q::from((i64::MAX, 1));
        let value2 = Q::from((1, i64::MAX));
        matrix.set_entry(0, 0, value1).unwrap();
        matrix.set_entry(1, 1, value2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Q::from(i64::MAX), entry1);
        assert_eq!(Q::from((1, i64::MAX)), entry2);
    }

    /// Ensure that getting entries works with large numerators and denominators (larger than [`i64`]).
    #[test]
    fn big_positive() {
        let mut matrix = MatQ::new(5, 10);
        let value1 = Q::from(u64::MAX);
        let value2 = Q::from((1, u64::MAX));
        matrix.set_entry(0, 0, value1).unwrap();
        matrix.set_entry(1, 1, value2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Q::from(u64::MAX), entry1);
        assert_eq!(Q::from((1, u64::MAX)), entry2);
    }

    /// Ensure that getting entries works with large negative numerators and denominators.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatQ::new(5, 10);
        let value1 = Q::from(i64::MIN);
        let value2 = Q::from((1, i64::MIN));
        matrix.set_entry(0, 0, value1).unwrap();
        matrix.set_entry(1, 1, value2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Q::from(i64::MIN), entry1);
        assert_eq!(Q::from((1, i64::MIN)), entry2);
    }

    /// Ensure that getting entries works with large negative numerators and denominators (larger than [`i64`]).
    #[test]
    fn big_negative() {
        let mut matrix = MatQ::new(5, 10);
        let value1 = format!("-{}", u64::MAX);
        let value2 = format!("1/-{}", u64::MAX);
        matrix
            .set_entry(0, 0, Q::from_str(&value1).unwrap())
            .unwrap();
        matrix
            .set_entry(1, 1, Q::from_str(&value2).unwrap())
            .unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Q::from_str(&format!("-{}", u64::MAX)).unwrap(), entry1);
        assert_eq!(Q::from_str(&format!("1/-{}", u64::MAX)).unwrap(), entry2);
    }

    /// Ensure that getting entries at (0,0) works.
    #[test]
    fn getting_at_zero() {
        let mut matrix = MatQ::new(5, 10);
        let value = Q::from(i64::MIN);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(entry, Q::from(i64::MIN));
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let matrix = MatQ::new(5, 10);

        assert!(matrix.get_entry(5, 1).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatQ::new(5, 10);

        assert!(matrix.get_entry(1, 100).is_err());
    }

    /// Ensure that the entry is a deep copy and not just a clone of the reference.
    #[test]
    fn memory_test() {
        let mut matrix = MatQ::new(5, 10);
        let value = Q::from(u64::MAX);
        matrix.set_entry(1, 1, value).unwrap();
        let entry = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(1, 1, Q::from(0)).unwrap();

        assert_eq!(Q::from(u64::MAX), entry);
    }
}

#[cfg(test)]
mod test_get_num {
    use crate::{
        rational::MatQ,
        traits::{GetNumColumns, GetNumRows},
    };

    /// Ensure that the getter for number of rows works correctly.
    #[test]
    fn num_rows() {
        let matrix = MatQ::new(5, 10);

        assert_eq!(matrix.get_num_rows(), 5);
    }

    /// Ensure that the getter for number of columns works correctly.
    #[test]
    fn num_columns() {
        let matrix = MatQ::new(5, 10);

        assert_eq!(matrix.get_num_columns(), 10);
    }
}

#[cfg(test)]
mod test_get_vec {
    use crate::rational::MatQ;
    use std::str::FromStr;

    /// Ensure that getting a row works
    #[test]
    fn get_row_works() {
        let matrix = MatQ::from_str(&format!(
            "[[0,0,0,0,0],[4/3,{},{},1/{},1/{}]]",
            i64::MAX,
            i64::MIN,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let row1 = matrix.get_row(0).unwrap();
        let row2 = matrix.get_row(1).unwrap();

        let cmp1 = MatQ::from_str("[[0,0,0,0,0]]").unwrap();
        let cmp2 = MatQ::from_str(&format!(
            "[[4/3,{},{},1/{},1/{}]]",
            i64::MAX,
            i64::MIN,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();

        assert_eq!(cmp1, row1);
        assert_eq!(cmp2, row2);
    }

    /// Ensure that getting a column works
    #[test]
    fn get_column_works() {
        let matrix = MatQ::from_str(&format!(
            "[[1,0,3],[{},0,5],[{},0,7],[1/{},0,9],[1/{},0,11]]",
            i64::MAX,
            i64::MIN,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let column1 = matrix.get_column(0).unwrap();
        let column2 = matrix.get_column(1).unwrap();
        let column3 = matrix.get_column(2).unwrap();

        let cmp1 = MatQ::from_str(&format!(
            "[[1],[{}],[{}],[1/{}],[1/{}]]",
            i64::MAX,
            i64::MIN,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let cmp2 = MatQ::from_str("[[0],[0],[0],[0],[0]]").unwrap();
        let cmp3 = MatQ::from_str("[[3],[5],[7],[9],[11]]").unwrap();

        assert_eq!(cmp1, column1);
        assert_eq!(cmp2, column2);
        assert_eq!(cmp3, column3);
    }

    /// Ensure that wrong row and column dimensions yields an error
    #[test]
    fn wrong_dim_error() {
        let matrix =
            MatQ::from_str(&format!("[[1,2,3],[{},4,5],[{},6,7]]", i64::MAX, i64::MIN)).unwrap();
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
    use super::MatQ;
    use std::str::FromStr;

    #[test]
    fn all_entries_collected() {
        let mat_1 = MatQ::from_str(&format!(
            "[[1/{},2],[{},{}],[-3/-4,4]]",
            i64::MAX,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let mat_2 = MatQ::from_str("[[-1/1,2/-4]]").unwrap();

        let entries_1 = mat_1.collect_entries();
        let entries_2 = mat_2.collect_entries();

        assert_eq!(entries_1.len(), 6);
        assert_eq!(entries_1[0].num.0, 1);
        assert!(entries_1[0].den.0 >= 2_i64.pow(62));
        assert_eq!(entries_1[1].num.0, 2);
        assert_eq!(entries_1[1].den.0, 1);
        assert!(entries_1[2].num.0 >= 2_i64.pow(62));
        assert_eq!(entries_1[2].den.0, 1);
        assert!(entries_1[3].num.0 >= 2_i64.pow(62));
        assert_eq!(entries_1[3].den.0, 1);
        assert_eq!(entries_1[4].num.0, 3);
        assert_eq!(entries_1[4].den.0, 4);
        assert_eq!(entries_1[5].num.0, 4);
        assert_eq!(entries_1[5].den.0, 1);

        assert_eq!(entries_2.len(), 2);
        assert_eq!(entries_2[0].num.0, -1);
        assert_eq!(entries_2[0].den.0, 1);
        assert_eq!(entries_2[1].num.0, -1);
        assert_eq!(entries_2[1].den.0, 2);
    }
}
