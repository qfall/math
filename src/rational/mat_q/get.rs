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
use flint_sys::fmpq_mat::{fmpq_mat_init_set, fmpq_mat_window_clear, fmpq_mat_window_init};
use flint_sys::{
    fmpq::{fmpq, fmpq_set},
    fmpq_mat::fmpq_mat_entry,
};
use std::fmt::Display;
use std::mem::MaybeUninit;

impl GetNumRows for MatQ {
    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatQ::new(5, 6);
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
    /// let matrix = MatQ::new(5, 6);
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
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns the [`Q`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or greater than the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{MatQ, Q};
    /// use qfall_math::traits::GetEntry;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[1,2,3/4],[4,5,6],[7,8,9]]").unwrap();
    ///
    /// assert_eq!(matrix.get_entry(0, 2).unwrap(), Q::from((3,4)));
    /// assert_eq!(matrix.get_entry(2, 1).unwrap(), Q::from(8));
    /// assert_eq!(matrix.get_entry(-1, -2).unwrap(), Q::from(8));
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if `row` or `column` are greater than the matrix size.
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
                format!("{row_i64}"),
            ));
        }

        self.get_submatrix(row_i64, row_i64, 0, self.get_num_columns() - 1)
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
                format!("{column_i64}"),
            ));
        }

        self.get_submatrix(0, self.get_num_rows() - 1, column_i64, column_i64)
    }

    /// Returns a deep copy of the submatrix defined by the given parameters.
    /// All entries starting from `(row1, col1)` to `(row2, col2)`(inclusively) are collected in
    /// a new matrix.
    /// Note that `row1 >= row2` and `col1 >= col2` must hold after converting negative indices.
    /// Otherwise the function will panic.
    ///
    /// Parameters:
    /// `row1`: The starting row of the submatrix
    /// `row2`: The ending row of the submatrix
    /// `col1`: The starting column of the submatrix
    /// `col2`: The ending column of the submatrix
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns the submatrix from `(row1, col1)` to `(row2, col2)`(inclusively).
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let mat = MatQ::identity(3,3);
    ///
    /// let sub_mat_1 = mat.get_submatrix(0, 2, 1, 1).unwrap();
    /// let sub_mat_2 = mat.get_submatrix(0, -1, 1, -2).unwrap();
    ///
    /// let e2 = MatQ::from_str("[[0],[1],[0]]").unwrap();
    /// assert_eq!(e2, sub_mat_1);
    /// assert_eq!(e2, sub_mat_2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if any provided row or column is greater than the matrix.
    ///
    /// # Panics ...
    /// - if `col1 > col2` or `row1 > row2`.
    pub fn get_submatrix(
        &self,
        row1: impl TryInto<i64> + Display,
        row2: impl TryInto<i64> + Display,
        col1: impl TryInto<i64> + Display,
        col2: impl TryInto<i64> + Display,
    ) -> Result<Self, MathError> {
        let (row1, col1) = evaluate_indices_for_matrix(self, row1, col1)?;
        let (row2, col2) = evaluate_indices_for_matrix(self, row2, col2)?;
        assert!(
            row2 >= row1,
            "The number of rows must be positive, i.e. row2 ({row2}) must be greater or equal row1 ({row1})"
        );

        assert!(
            col2 >= col1,
            "The number of columns must be positive, i.e. col2 ({col2}) must be greater or equal col1 ({col1})"
        );

        // increase both values to have an inclusive capturing of the matrix entries
        let (row2, col2) = (row2 + 1, col2 + 1);

        let mut window = MaybeUninit::uninit();
        // The memory for the elements of window is shared with self.
        unsafe { fmpq_mat_window_init(window.as_mut_ptr(), &self.matrix, row1, col1, row2, col2) };
        let mut window_copy = MaybeUninit::uninit();
        unsafe {
            // Deep clone of the content of the window
            fmpq_mat_init_set(window_copy.as_mut_ptr(), window.as_ptr());
            // Clears the matrix window and releases any memory that it uses. Note that
            // the memory to the underlying matrix that window points to is not freed
            fmpq_mat_window_clear(window.as_mut_ptr());
        }
        Ok(MatQ {
            matrix: unsafe { window_copy.assume_init() },
        })
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
        let value1 = Q::from(i64::MAX);
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
        assert!(matrix.get_entry(-6, 1).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatQ::new(5, 10);

        assert!(matrix.get_entry(1, 100).is_err());
        assert!(matrix.get_entry(1, -11).is_err());
    }

    /// Ensure that negative indices return the correct values.
    #[test]
    fn negative_indexing() {
        let matrix = MatQ::from_str("[[1,2,3],[4,5,6],[7,8,9]]").unwrap();

        assert_eq!(matrix.get_entry(-1, -1).unwrap(), Q::from(9));
        assert_eq!(matrix.get_entry(-1, -2).unwrap(), Q::from(8));
        assert_eq!(matrix.get_entry(-3, -3).unwrap(), Q::from(1));
    }

    /// Ensure that the entry is a deep copy and not just a clone of the reference.
    #[test]
    fn memory_test() {
        let mut matrix = MatQ::new(5, 10);
        let value = Q::from(u64::MAX);
        matrix.set_entry(1, 1, value).unwrap();
        let entry = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(1, 1, Q::ZERO).unwrap();

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
mod test_get_submatrix {
    use crate::{
        integer::Z,
        rational::MatQ,
        traits::{GetNumColumns, GetNumRows},
    };
    use std::str::FromStr;

    /// Ensures that getting the entire matrix as a submatrix works.
    #[test]
    fn entire_matrix() {
        let mat = MatQ::identity(5, 5);

        let sub_mat = mat.get_submatrix(0, 4, 0, 4).unwrap();

        assert_eq!(mat, sub_mat);
    }

    /// Ensures that a single matrix entry can be retrieved.
    #[test]
    fn matrix_single_entry() {
        let mat = MatQ::identity(5, 5);

        let sub_mat = mat.get_submatrix(0, 0, 0, 0).unwrap();

        let cmp_mat = MatQ::identity(1, 1);
        assert_eq!(cmp_mat, sub_mat);
    }

    /// Ensures that the dimensions of the submatrix are correct.
    #[test]
    fn correct_dimensions() {
        let mat = MatQ::identity(100, 100);

        let sub_mat = mat.get_submatrix(1, 37, 0, 29).unwrap();

        assert_eq!(37, sub_mat.get_num_rows());
        assert_eq!(30, sub_mat.get_num_columns());
    }

    /// Ensures that a submatrix can be correctly retrieved for a matrix with large
    /// entries.
    #[test]
    fn large_entries() {
        let mat =
            MatQ::from_str(&format!("[[{}/3, 2, 3],[1, {}, 3]]", u64::MAX, i64::MIN)).unwrap();

        let sub_mat = mat.get_submatrix(0, 1, 0, 1).unwrap();

        let cmp_mat = MatQ::from_str(&format!("[[{}/3, 2],[1, {}]]", u64::MAX, i64::MIN)).unwrap();
        assert_eq!(cmp_mat, sub_mat);
    }

    /// Ensures that an error is returned if coordinates are addressed that are not
    /// within the matrix.
    #[test]
    fn invalid_coordinates() {
        let mat = MatQ::identity(10, 10);

        assert!(mat.get_submatrix(0, 0, 0, 10).is_err());
        assert!(mat.get_submatrix(0, 10, 0, 0).is_err());
        assert!(mat.get_submatrix(0, 0, -11, 0).is_err());
        assert!(mat.get_submatrix(-11, 0, 0, 0).is_err());
    }

    /// Ensure that negative indices return the correct submatrix.
    #[test]
    fn negative_indexing() {
        let matrix = MatQ::identity(3, 3);

        assert_eq!(matrix, matrix.get_submatrix(0, -1, 0, -1).unwrap());
        assert_eq!(matrix, matrix.get_submatrix(-3, -1, -3, -1).unwrap());
        assert_eq!(
            matrix.get_row(0).unwrap(),
            matrix.get_submatrix(0, -3, -3, -1).unwrap()
        );
    }

    /// Ensures that the function panics if no columns of the matrix are addressed.
    #[test]
    #[should_panic]
    fn no_columns() {
        let mat = MatQ::identity(10, 10);

        let _ = mat.get_submatrix(0, 0, 6, 5);
    }

    /// Ensures that the function panics if no rows of the matrix are addressed.
    #[test]
    #[should_panic]
    fn no_rows() {
        let mat = MatQ::identity(10, 10);

        let _ = mat.get_submatrix(5, 4, 0, 0);
    }

    /// Ensure that the submatrix function can be called with several types.
    #[test]
    fn availability() {
        let mat = MatQ::identity(10, 10);

        let _ = mat.get_submatrix(0_i8, 0_i8, 0_i8, 0_i8);
        let _ = mat.get_submatrix(0_i16, 0_i16, 0_i16, 0_i16);
        let _ = mat.get_submatrix(0_i32, 0_i32, 0_i32, 0_i32);
        let _ = mat.get_submatrix(0_i64, 0_i64, 0_i64, 0_i64);
        let _ = mat.get_submatrix(0_u8, 0_u8, 0_u8, 0_u8);
        let _ = mat.get_submatrix(0_u16, 0_i16, 0_u16, 0_u16);
        let _ = mat.get_submatrix(0_u32, 0_i32, 0_u32, 0_u32);
        let _ = mat.get_submatrix(0_u64, 0_i64, 0_u64, 0_u64);
        let _ = mat.get_submatrix(&Z::ZERO, &Z::ZERO, &Z::ZERO, &Z::ZERO);
    }
}

#[cfg(test)]
mod test_collect_entries {
    use super::MatQ;
    use std::str::FromStr;

    /// Ensures that all entries from the matrices are actually collected in the vector.
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
