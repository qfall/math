// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`MatPolyOverZ`] matrix.

use super::MatPolyOverZ;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    traits::{GetEntry, GetNumColumns, GetNumRows},
    utils::index::{evaluate_index, evaluate_indices_for_matrix},
};
use flint_sys::{
    fmpz_poly::{fmpz_poly_set, fmpz_poly_struct},
    fmpz_poly_mat::{
        fmpz_poly_mat_entry, fmpz_poly_mat_init_set, fmpz_poly_mat_window_clear,
        fmpz_poly_mat_window_init,
    },
};
use std::{fmt::Display, mem::MaybeUninit};

impl GetNumRows for MatPolyOverZ {
    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatPolyOverZ::new(5, 6);
    /// let rows = matrix.get_num_rows();
    /// ```
    fn get_num_rows(&self) -> i64 {
        self.matrix.r
    }
}

impl GetNumColumns for MatPolyOverZ {
    /// Returns the number of columns of the matrix as a [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatPolyOverZ::new(5, 6);
    /// let columns = matrix.get_num_columns();
    /// ```
    fn get_num_columns(&self) -> i64 {
        self.matrix.c
    }
}

impl GetEntry<PolyOverZ> for MatPolyOverZ {
    /// Outputs the [`PolyOverZ`] value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns the [`PolyOverZ`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatPolyOverZ, PolyOverZ};
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  1, 1  2],[1  3, 1  4],[0, 1  6]]").unwrap();
    ///
    /// assert_eq!(PolyOverZ::from(2), matrix.get_entry(0, 1).unwrap());
    /// assert_eq!(PolyOverZ::from(4), matrix.get_entry(-2, 1).unwrap());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///     if `row` or `column` are greater than the matrix size.
    fn get_entry(
        &self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
    ) -> Result<PolyOverZ, MathError> {
        let (row_i64, column_i64) = evaluate_indices_for_matrix(self, row, column)?;

        // since `self.matrix` is a correct fmpz_poly matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpz_poly_set` can successfully clone the
        // entry of the matrix. Therefore no memory leaks can appear.
        let mut copy = PolyOverZ::default();
        let entry = unsafe { fmpz_poly_mat_entry(&self.matrix, row_i64, column_i64) };
        unsafe { fmpz_poly_set(&mut copy.poly, entry) };

        Ok(copy)
    }
}

impl MatPolyOverZ {
    /// Outputs the row vector of the specified row.
    ///
    /// Parameters:
    /// - `row`: specifies the row of the matrix
    ///
    /// Returns a row vector of the matrix at the position of the given
    /// `row` or an error, if the number of rows is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  1, 0],[1  3, 1  4],[0, 1  6]]").unwrap();
    ///
    /// let row_0 = matrix.get_row(0).unwrap(); // first row
    /// let row_1 = matrix.get_row(1).unwrap(); // second row
    /// let row_2 = matrix.get_row(2).unwrap(); // third row
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///     if the number of the row is greater than the matrix or negative.
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
    /// `column` or an error, if the number of columns is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  1, 0],[1  3, 1  4],[0, 1  6]]").unwrap();
    ///
    /// let col_0 = matrix.get_column(0).unwrap(); // first column
    /// let col_1 = matrix.get_column(1).unwrap(); // second column
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///     if the number of the column is greater than the matrix or negative.
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
    /// All entries starting from `(row_1, col_1)` to `(row_2, col_2)`(inclusively) are collected in
    /// a new matrix.
    /// Note that `row_1 >= row_2` and `col_1 >= col_2` must hold after converting negative indices.
    /// Otherwise the function will panic.
    ///
    /// Parameters:
    /// `row_1`: the starting row of the submatrix
    /// `row_2`: the ending row of the submatrix
    /// `col_1`: the starting column of the submatrix
    /// `col_2`: the ending column of the submatrix
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns the submatrix from `(row_1, col_1)` to `(row_2, col_2)`(inclusively)
    /// or an error, if any provided row or column is greater than the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mat = MatPolyOverZ::identity(3, 3);
    ///
    /// let sub_mat_1 = mat.get_submatrix(0, 2, 1, 1).unwrap();
    /// let sub_mat_2 = mat.get_submatrix(0, -1, 1, -2).unwrap();
    ///
    /// let e_2 = MatPolyOverZ::from_str("[[0],[1  1],[0]]").unwrap();
    /// assert_eq!(e_2, sub_mat_1);
    /// assert_eq!(e_2, sub_mat_2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///     if any provided row or column is greater than the matrix.
    ///
    /// # Panics ...
    /// - if `col_1 > col_2` or `row_1 > row_2`.
    pub fn get_submatrix(
        &self,
        row_1: impl TryInto<i64> + Display,
        row_2: impl TryInto<i64> + Display,
        col_1: impl TryInto<i64> + Display,
        col_2: impl TryInto<i64> + Display,
    ) -> Result<Self, MathError> {
        let (row_1, col_1) = evaluate_indices_for_matrix(self, row_1, col_1)?;
        let (row_2, col_2) = evaluate_indices_for_matrix(self, row_2, col_2)?;
        assert!(
            row_2 >= row_1,
            "The number of rows must be positive, i.e. row_2 ({row_2}) must be greater or equal row_1 ({row_1})"
        );

        assert!(
            col_2 >= col_1,
            "The number of columns must be positive, i.e. col_2 ({col_2}) must be greater or equal col_1 ({col_1})"
        );

        // increase both values to have an inclusive capturing of the matrix entries
        let (row_2, col_2) = (row_2 + 1, col_2 + 1);

        let mut window = MaybeUninit::uninit();
        // The memory for the elements of window is shared with self.
        unsafe {
            fmpz_poly_mat_window_init(
                window.as_mut_ptr(),
                &self.matrix,
                row_1,
                col_1,
                row_2,
                col_2,
            )
        };
        let mut window_copy = MaybeUninit::uninit();
        unsafe {
            // Deep clone of the content of the window
            fmpz_poly_mat_init_set(window_copy.as_mut_ptr(), window.as_ptr());
            // Clears the matrix window and releases any memory that it uses. Note that
            // the memory to the underlying matrix that window points to is not freed
            fmpz_poly_mat_window_clear(window.as_mut_ptr());
        }
        Ok(MatPolyOverZ {
            matrix: unsafe { window_copy.assume_init() },
        })
    }

    /// Efficiently collects all [`fmpz_poly_struct`]s in a [`MatPolyOverZ`] without cloning them.
    ///
    /// Hence, the values on the returned [`Vec`] are intended for short-term use
    /// as the access to [`fmpz_poly_struct`] values could lead to memory leaks or
    /// modified values once the [`MatPolyOverZ`] instance was modified or dropped.
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mat = MatPolyOverZ::from_str("[[1  1, 0],[1  3, 1  4],[0, 1  6]]").unwrap();
    ///
    /// let fmpz_entries = mat.collect_entries();
    /// ```
    pub(crate) fn collect_entries(&self) -> Vec<fmpz_poly_struct> {
        let mut entries: Vec<fmpz_poly_struct> = vec![];

        for row in 0..self.get_num_rows() {
            for col in 0..self.get_num_columns() {
                // efficiently get entry without cloning the entry itself
                let entry = unsafe { *fmpz_poly_mat_entry(&self.matrix, row, col) };
                entries.push(entry);
            }
        }

        entries
    }
}

#[cfg(test)]
mod test_get_entry {
    use crate::{
        integer::{MatPolyOverZ, PolyOverZ},
        traits::{GetEntry, SetEntry},
    };
    use std::str::FromStr;

    /// Ensure that getting entries works with large polynomials.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MAX)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(format!("2  {} 1", i64::MAX), entry.to_string());
    }

    /// Ensure that getting entries works with large polynomials (larger than [`i64`]).
    #[test]
    fn large_positive() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry.to_string());
    }

    /// Ensure that getting entries works with large negative polynomials.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MIN)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(format!("2  {} 1", i64::MIN), entry.to_string());
    }

    /// Ensure that getting entries works with large negative polynomials (larger than [`i64`]).
    #[test]
    fn large_negative() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str(&format!("2  -{} 1", u64::MAX)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(format!("2  -{} 1", u64::MAX), entry.to_string());
    }

    /// Ensure that polynomials with many entries are correctly retrieved
    #[test]
    fn large_poly() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value =
            PolyOverZ::from_str(&format!("10000  -{} 1{}", u64::MAX, " 17".repeat(9998))).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(
            format!("10000  -{} 1{}", u64::MAX, " 17".repeat(9998)),
            entry.to_string()
        );
    }

    /// Ensure that getting entries at (0, 0) works.
    #[test]
    fn getting_at_zero() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MAX)).unwrap();
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(format!("2  {} 1", i64::MAX), entry.to_string());
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let matrix = MatPolyOverZ::new(5, 10);

        assert!(matrix.get_entry(5, 1).is_err());
        assert!(matrix.get_entry(-6, 1).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatPolyOverZ::new(5, 10);

        assert!(matrix.get_entry(1, 100).is_err());
        assert!(matrix.get_entry(1, -11).is_err());
    }

    /// Ensure that negative indices return the correct values.
    #[test]
    fn negative_indexing() {
        let matrix = MatPolyOverZ::from_str("[[1  1, 1  2],[1  3, 1  4],[1  5 , 1  6]]").unwrap();

        assert_eq!(PolyOverZ::from(2), matrix.get_entry(0, -1).unwrap());
        assert_eq!(PolyOverZ::from(4), matrix.get_entry(-2, 1).unwrap());
        assert_eq!(PolyOverZ::from(4), matrix.get_entry(-2, -1).unwrap());
        assert_eq!(PolyOverZ::from(6), matrix.get_entry(-1, -1).unwrap());
    }

    /// Ensure that the entry is a deep copy and not just a clone of the reference.
    #[test]
    fn memory_test() {
        let mut matrix = MatPolyOverZ::new(5, 10);
        let value = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();
        let entry = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(1, 1, PolyOverZ::default()).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry.to_string());
    }
}

#[cfg(test)]
mod test_get_num {
    use crate::{
        integer::MatPolyOverZ,
        traits::{GetNumColumns, GetNumRows},
    };

    /// Ensure that the getter for number of rows works correctly.
    #[test]
    fn num_rows() {
        let matrix = MatPolyOverZ::new(5, 10);

        assert_eq!(matrix.get_num_rows(), 5);
    }

    /// Ensure that the getter for number of columns works correctly.
    #[test]
    fn num_columns() {
        let matrix = MatPolyOverZ::new(5, 10);

        assert_eq!(matrix.get_num_columns(), 10);
    }
}

#[cfg(test)]
mod test_get_vec {
    use crate::integer::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensure that getting a row works
    #[test]
    fn get_row_works() {
        let matrix = MatPolyOverZ::from_str(&format!(
            "[[0, 0, 0],[1  42, 1  {}, 1  {}]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let row_1 = matrix.get_row(0).unwrap();
        let row_2 = matrix.get_row(1).unwrap();

        let cmp_1 = MatPolyOverZ::from_str("[[0, 0, 0]]").unwrap();
        let cmp_2 = MatPolyOverZ::from_str(&format!("[[1  42, 1  {}, 1  {}]]", i64::MAX, i64::MIN))
            .unwrap();

        assert_eq!(cmp_1, row_1);
        assert_eq!(cmp_2, row_2);
    }

    /// Ensure that getting a column works
    #[test]
    fn get_column_works() {
        let matrix = MatPolyOverZ::from_str(&format!(
            "[[1  42, 0, 2  17 42],[1  {}, 0, 2  17 42],[1  {}, 0, 2  17 42]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let column_1 = matrix.get_column(0).unwrap();
        let column_2 = matrix.get_column(1).unwrap();
        let column_3 = matrix.get_column(2).unwrap();

        let cmp_1 =
            MatPolyOverZ::from_str(&format!("[[1  42],[1  {}],[1  {}]]", i64::MAX, i64::MIN))
                .unwrap();
        let cmp_2 = MatPolyOverZ::from_str("[[0],[0],[0]]").unwrap();
        let cmp_3 = MatPolyOverZ::from_str("[[2  17 42],[2  17 42],[2  17 42]]").unwrap();

        assert_eq!(cmp_1, column_1);
        assert_eq!(cmp_2, column_2);
        assert_eq!(cmp_3, column_3);
    }

    /// Ensure that wrong row and column dimensions yields an error
    #[test]
    fn wrong_dim_error() {
        let matrix = MatPolyOverZ::from_str(&format!(
            "[[1  17, 2  17 42, 3  1 1 1],[1  {}, 1  1, 2  2 3],[1  {}, 1  142, 1  1]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let row_1 = matrix.get_row(-1);
        let row_2 = matrix.get_row(4);
        let column_1 = matrix.get_column(-1);
        let column_2 = matrix.get_column(4);

        assert!(row_1.is_err());
        assert!(row_2.is_err());
        assert!(column_1.is_err());
        assert!(column_2.is_err());
    }
}

#[cfg(test)]
mod test_get_submatrix {
    use crate::{
        integer::{MatPolyOverZ, Z},
        traits::{GetNumColumns, GetNumRows},
    };
    use std::str::FromStr;

    /// Ensures that getting the entire matrix as a submatrix works.
    #[test]
    fn entire_matrix() {
        let mat = MatPolyOverZ::identity(5, 5);

        let sub_mat = mat.get_submatrix(0, 4, 0, 4).unwrap();

        assert_eq!(mat, sub_mat);
    }

    /// Ensures that a single matrix entry can be retrieved.
    #[test]
    fn matrix_single_entry() {
        let mat = MatPolyOverZ::identity(5, 5);

        let sub_mat = mat.get_submatrix(0, 0, 0, 0).unwrap();

        let cmp_mat = MatPolyOverZ::identity(1, 1);
        assert_eq!(cmp_mat, sub_mat);
    }

    /// Ensures that the dimensions of the submatrix are correct.
    #[test]
    fn correct_dimensions() {
        let mat = MatPolyOverZ::identity(100, 100);

        let sub_mat = mat.get_submatrix(1, 37, 0, 29).unwrap();

        assert_eq!(37, sub_mat.get_num_rows());
        assert_eq!(30, sub_mat.get_num_columns());
    }

    /// Ensures that a submatrix can be correctly retrieved for a matrix with large
    /// entries.
    #[test]
    fn large_entries() {
        let mat = MatPolyOverZ::from_str(&format!(
            "[[2  {} {}, 1  2, 1  3],[1  1, 1  {}, 1  3]]",
            u64::MAX,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();

        let sub_mat = mat.get_submatrix(0, 1, 0, 1).unwrap();

        let cmp_mat = MatPolyOverZ::from_str(&format!(
            "[[2  {} {}, 1  2],[1  1, 1  {}]]",
            u64::MAX,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        assert_eq!(cmp_mat, sub_mat);
    }

    /// Ensures that an error is returned if coordinates are addressed that are not
    /// within the matrix.
    #[test]
    fn invalid_coordinates() {
        let mat = MatPolyOverZ::identity(10, 10);

        assert!(mat.get_submatrix(0, 0, 0, 10).is_err());
        assert!(mat.get_submatrix(0, 10, 0, 0).is_err());
        assert!(mat.get_submatrix(0, 0, -11, 0).is_err());
        assert!(mat.get_submatrix(-11, 0, 0, 0).is_err());
    }

    /// Ensure that negative indices return the correct submatrix.
    #[test]
    fn negative_indexing() {
        let matrix = MatPolyOverZ::identity(3, 3);

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
        let mat = MatPolyOverZ::identity(10, 10);

        let _ = mat.get_submatrix(0, 0, 6, 5);
    }

    /// Ensures that the function panics if no rows of the matrix are addressed.
    #[test]
    #[should_panic]
    fn no_rows() {
        let mat = MatPolyOverZ::identity(10, 10);

        let _ = mat.get_submatrix(5, 4, 0, 0);
    }

    /// Ensure that the submatrix function can be called with several types.
    #[test]
    fn availability() {
        let mat = MatPolyOverZ::identity(10, 10);

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
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensures that all entries from the matrices are actually collected in the vector.
    #[test]
    fn all_entries_collected() {
        let mat_1 = MatPolyOverZ::from_str(&format!(
            "[[1  1, 0],[1  {}, 1  {}],[1  -3, 0]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[1  -1, 2  1 2]]").unwrap();

        let entries_1 = mat_1.collect_entries();
        let entries_2 = mat_2.collect_entries();

        assert_eq!(entries_1.len(), 6);
        assert_eq!(unsafe { *entries_1[0].coeffs }.0, 1);
        assert!(unsafe { *entries_1[2].coeffs }.0 >= 2_i64.pow(62));
        assert!(unsafe { *entries_1[3].coeffs }.0 >= 2_i64.pow(62));
        assert_eq!(unsafe { *entries_1[4].coeffs }.0, -3);

        assert_eq!(entries_2.len(), 2);
        assert_eq!(unsafe { *entries_2[0].coeffs.offset(0) }.0, -1);
        assert_eq!(entries_2[0].length, 1);
        assert_eq!(unsafe { *entries_2[1].coeffs.offset(0) }.0, 1);
        assert_eq!(unsafe { *entries_2[1].coeffs.offset(1) }.0, 2);
        assert_eq!(entries_2[1].length, 2);
    }
}
