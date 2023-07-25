// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`MatZ`] matrix.

use super::MatZ;
use crate::{
    error::MathError,
    integer::Z,
    traits::{GetEntry, GetNumColumns, GetNumRows},
    utils::index::{evaluate_index, evaluate_indices_for_matrix},
};
use flint_sys::{
    fmpz::{fmpz, fmpz_set},
    fmpz_mat::{fmpz_mat_entry, fmpz_mat_init_set, fmpz_mat_window_clear, fmpz_mat_window_init},
};
use std::{fmt::Display, mem::MaybeUninit};

impl GetNumRows for MatZ {
    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatZ::new(5, 6);
    /// let rows = matrix.get_num_rows();
    /// ```
    fn get_num_rows(&self) -> i64 {
        self.matrix.r
    }
}

impl GetNumColumns for MatZ {
    /// Returns the number of columns of the matrix as a [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatZ::new(5, 6);
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
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::traits::GetEntry;
    ///
    /// let matrix = MatZ::new(5, 10);
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
    ) -> Result<Z, MathError> {
        let (row_i64, column_i64) = evaluate_indices_for_matrix(self, row, column)?;

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
    /// # Examples
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
    /// All entries starting from `(r1, c1)` to `(r2, c2)`(inclusively) are collected in
    /// a new matrix.
    /// Note that `r1 >= r2` and `c1 >= c2` must hold. Otherwise the function will panic.
    ///
    /// Parameters:
    /// `r1`: The starting row of the submatrix
    /// `r2`: The ending row of the submatrix
    /// `c1`: The starting column of the submatrix
    /// `c2`: The ending column of the submatrix
    ///
    /// Returns the submatrix from `(r1, c1)` to `(r2, c2)`(inclusively).
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let mat = MatZ::identity(3,3);
    /// let sub_mat = mat.get_submatrix(0, 2, 1, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if any provided row or column is greater than the matrix or negative.
    ///
    /// # Panics ...
    /// - if `c1 > c2` or `r1 > r2`.
    pub fn get_submatrix(
        &self,
        r1: impl TryInto<i64> + Display,
        r2: impl TryInto<i64> + Display,
        c1: impl TryInto<i64> + Display,
        c2: impl TryInto<i64> + Display,
    ) -> Result<Self, MathError> {
        let (r1, c1) = evaluate_indices_for_matrix(self, r1, c1)?;
        let (r2, c2) = evaluate_indices_for_matrix(self, r2, c2)?;
        assert!(
            r2 >= r1,
            "The number of rows must be positive, i.e. r2 ({r2}) must be greater or equal r1 ({r1})"
        );

        assert!(
            c2 >= c1,
            "The number of columns must be positive, i.e. c2 ({c2}) must be greater or equal c1 ({c1})"
        );

        // increase both values to have an inclusive capturing of the matrix entries
        let (r2, c2) = (r2 + 1, c2 + 1);

        let mut window = MaybeUninit::uninit();
        // The memory for the elements of window is shared with self.
        unsafe { fmpz_mat_window_init(window.as_mut_ptr(), &self.matrix, r1, c1, r2, c2) };
        let mut window_copy = MaybeUninit::uninit();
        unsafe {
            // Deep clone of the content of the window
            fmpz_mat_init_set(window_copy.as_mut_ptr(), window.as_ptr());
            // Clears the matrix window and releases any memory that it uses. Note that
            // the memory to the underlying matrix that window points to is not freed
            fmpz_mat_window_clear(window.as_mut_ptr());
        }
        Ok(MatZ {
            matrix: unsafe { window_copy.assume_init() },
        })
    }

    /// Efficiently collects all [`fmpz`]s in a [`MatZ`] without cloning them.
    ///
    /// Hence, the values on the returned [`Vec`] are intended for short-term use
    /// as the access to [`fmpz`] values could lead to memory leaks or modified values
    /// once the [`MatZ`] instance was modified or dropped.
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::integer::MatZ;
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
        let mut matrix = MatZ::new(5, 10);
        let value = Z::from(i64::MAX);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from(i64::MAX), entry);
    }

    /// Ensure that getting entries works with large numbers (larger than i64).
    #[test]
    fn big_positive() {
        let mut matrix = MatZ::new(5, 10);
        let value = Z::from(u64::MAX);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from(u64::MAX), entry);
    }

    /// Ensure that getting entries works with large negative numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatZ::new(5, 10);
        let value = Z::from(i64::MIN);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from(i64::MIN), entry);
    }

    /// Ensure that getting entries works with large negative numbers (larger than i64).
    #[test]
    fn big_negative() {
        let mut matrix = MatZ::new(5, 10);
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
        let mut matrix = MatZ::new(5, 10);
        let value = Z::from(i64::MIN);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(entry, Z::from(i64::MIN));
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let matrix = MatZ::new(5, 10);

        assert!(matrix.get_entry(5, 1).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatZ::new(5, 10);

        assert!(matrix.get_entry(1, 100).is_err());
    }

    /// Ensure that the entry is a deep copy and not just a clone of the reference.
    #[test]
    fn memory_test() {
        let mut matrix = MatZ::new(5, 10);
        let value = Z::from(u64::MAX);
        matrix.set_entry(1, 1, value).unwrap();
        let entry = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(1, 1, Z::from(0)).unwrap();

        assert_eq!(Z::from(u64::MAX), entry);
    }
}

#[cfg(test)]
mod test_get_num {

    use crate::{
        integer::MatZ,
        traits::{GetNumColumns, GetNumRows},
    };

    /// Ensure that the getter for number of rows works correctly.
    #[test]
    fn num_rows() {
        let matrix = MatZ::new(5, 10);

        assert_eq!(matrix.get_num_rows(), 5);
    }

    /// Ensure that the getter for number of columns works correctly.
    #[test]
    fn num_columns() {
        let matrix = MatZ::new(5, 10);

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
mod test_get_submatrix {
    use crate::{
        integer::{MatZ, Z},
        traits::{GetNumColumns, GetNumRows},
    };
    use std::str::FromStr;

    /// Ensures that getting the entire matrix as a submatrix works.
    #[test]
    fn entire_matrix() {
        let mat = MatZ::identity(5, 5);

        let sub_mat = mat.get_submatrix(0, 4, 0, 4).unwrap();

        assert_eq!(mat, sub_mat)
    }

    /// Ensures that a single matrix entry can be retrieved.
    #[test]
    fn matrix_single_entry() {
        let mat = MatZ::identity(5, 5);

        let sub_mat = mat.get_submatrix(0, 0, 0, 0).unwrap();

        let cmp_mat = MatZ::identity(1, 1);
        assert_eq!(cmp_mat, sub_mat)
    }

    /// Ensures that the dimensions of the submatrix are correct.
    #[test]
    fn correct_dimensions() {
        let mat = MatZ::identity(100, 100);

        let sub_mat = mat.get_submatrix(1, 37, 0, 29).unwrap();

        assert_eq!(37, sub_mat.get_num_rows());
        assert_eq!(30, sub_mat.get_num_columns())
    }

    /// Ensures that a submatrix can be correctly retrieved for a matrix with large
    /// entries.
    #[test]
    fn large_entries() {
        let mat = MatZ::from_str(&format!("[[{}, 2, 3],[1, {}, 3]]", u64::MAX, i64::MIN)).unwrap();

        let sub_mat = mat.get_submatrix(0, 1, 0, 1).unwrap();

        let cmp_mat = MatZ::from_str(&format!("[[{}, 2],[1, {}]]", u64::MAX, i64::MIN)).unwrap();
        assert_eq!(cmp_mat, sub_mat)
    }

    /// Ensures that an error is returned if coordinates are addressed that are not
    /// within the matrix.
    #[test]
    fn invalid_coordinates() {
        let mat = MatZ::identity(10, 10);

        assert!(mat.get_submatrix(0, 0, 0, 10).is_err());
        assert!(mat.get_submatrix(0, 10, 0, 0).is_err());
        assert!(mat.get_submatrix(0, 0, -1, 0).is_err());
        assert!(mat.get_submatrix(-1, 0, 0, 0).is_err());
    }

    /// Ensures that the function panics if no columns of the matrix are addressed.
    #[test]
    #[should_panic]
    fn no_columns() {
        let mat = MatZ::identity(10, 10);

        let _ = mat.get_submatrix(0, 0, 6, 5);
    }

    /// Ensures that the function panics if no rows of the matrix are addressed.
    #[test]
    #[should_panic]
    fn no_rows() {
        let mat = MatZ::identity(10, 10);

        let _ = mat.get_submatrix(5, 4, 0, 0);
    }

    /// Ensure that the submatrix function can be called with several types.
    #[test]
    fn availability() {
        let mat = MatZ::identity(10, 10);

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
    use super::MatZ;
    use std::str::FromStr;

    /// Ensures that all entries from the matrices are actually collected in the vector.
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
