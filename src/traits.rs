// Copyright © 2023 Marvin Beckmann, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains basic traits for this library. These include
//! specific traits for matrices and polynomials.

use crate::{
    error::MathError,
    utils::index::{evaluate_index_for_vector, evaluate_indices_for_matrix},
};
use flint_sys::fmpz::fmpz;
use std::fmt::Display;

/// Is implemented by every type where a base-check might be needed.
/// This also includes every type of matrix, because it allows for geneceric implementations.
/// Per default, a basecheck simply returs that the bases match and no error is returned.
pub trait CompareBase {
    /// Compares the base elements of the objects and returns true if they match
    /// and an operation between the two provided types is possible.
    ///
    /// Parameters:
    /// - `other`: The other object whose base is compared to `self`
    ///
    /// Returns true if the bases match and false otherwise.
    /// The default implementation just returns true.
    #[allow(unused_variables)]
    fn compare_base(&self, other: &Self) -> bool {
        true
    }

    /// Calls an error that gives small explanation how the base elements differ.
    /// This function only calls the error and does not check if the two actually differ.
    ///
    /// Parameters:
    /// - `other`: The other object whose base is compared to `self`
    ///
    /// Returns a MathError, typically [MathError::MismatchingModulus].
    /// The default implementation just returns `None`.
    #[allow(unused_variables)]
    fn call_compare_base_error(&self, other: &Self) -> Option<MathError> {
        None
    }
}

/// Is implemented by polynomials to evaluate them for a certain input.
pub trait Evaluate<T, U> {
    /// Evaluates the object, e.g. polynomial or a matrix of polynomials,
    /// for a given input value.
    ///
    /// Parameters:
    /// - `value`: the value with which to evaluate the object.
    ///
    /// Returns the evaluation of the object.
    fn evaluate(&self, value: T) -> U;
}

/// Is implemented by polynomials to get a coefficient.
pub trait GetCoefficient<T> {
    /// Returns a coefficient of the given object, e.g. a polynomial,
    /// for a given index.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient
    ///
    /// Returns the coefficient of the polynomial.
    fn get_coeff(&self, index: impl TryInto<i64> + Display) -> Result<T, MathError>;
}

/// Is implemented by polynomials to set a coefficient.
pub trait SetCoefficient<T> {
    /// Sets coefficient of the object, e.g. polynomial,
    /// for a given input value and a index.
    ///
    /// Parameters:
    /// - `index`: the coefficient to be set.
    /// - `value`: the value the coefficient is set to.
    fn set_coeff(&mut self, index: impl TryInto<i64> + Display, value: T) -> Result<(), MathError>;
}

/// Is implemented by matrices to get the number of rows and number of columns of the matrix.
pub trait MatrixDimensions {
    /// Returns the number of rows of a matrix.
    fn get_num_rows(&self) -> i64;

    /// Returns the number of columns of a matrix.
    fn get_num_columns(&self) -> i64;
}

/// Is implemented by matrices to get entries.
pub trait MatrixGetEntry<T>
where
    Self: MatrixDimensions,
    T: std::clone::Clone,
{
    /// Returns the value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located.
    /// - `column`: specifies the column in which the entry is located.
    ///
    /// Returns the value of the matrix at the position of the given
    /// row and column or an error if the number of rows or columns is
    /// greater than the matrix or negative.
    fn get_entry(
        &self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
    ) -> Result<T, MathError>;

    /// Returns the value of a specific matrix entry
    /// without performing any checks, e.g. checking whether the entry is
    /// part of the matrix.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located.
    /// - `column`: specifies the column in which the entry is located.
    ///
    /// # Safety
    /// To use this function safely, make sure that the selected entry is part
    /// of the matrix. If it is not, memory leaks, unexpected panics, etc. might
    /// occur.
    unsafe fn get_entry_unchecked(&self, row: i64, column: i64) -> T;

    /// Outputs a [`Vec<Vec<T>>`] containing all entries of the matrix s.t.
    /// any entry in row `i` and column `j` can be accessed via `entries[i][j]`
    /// if `entries = matrix.get_entries`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::{MatZ, Z}, traits::*};
    /// let matrix = MatZ::sample_uniform(3, 3, 0, 16).unwrap();
    ///
    /// let entries = matrix.get_entries();
    /// let mut added_entries = Z::default();
    /// for row in entries {
    ///     for entry in row {
    ///         added_entries += entry;
    ///     }
    /// }
    /// ```
    fn get_entries(&self) -> Vec<Vec<T>> {
        let mut entries = vec![vec![]; self.get_num_rows() as usize];

        for i in 0..self.get_num_rows() {
            for j in 0..self.get_num_columns() {
                let entry = unsafe { self.get_entry_unchecked(i, j) };
                entries[i as usize].push(entry);
            }
        }

        entries
    }

    /// Outputs a [`Vec<T>`] containing all entries of the matrix in a row-wise order, i.e.
    /// a matrix `[[2, 3, 4],[5, 6, 7]]` can be accessed via this function in this order `[2, 3, 4, 5, 6, 7]`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::{MatZ, Z}, traits::*};
    /// let matrix = MatZ::sample_uniform(3, 3, 0, 16).unwrap();
    ///
    /// let entries = matrix.get_entries_rowwise();
    /// let mut added_entries = Z::default();
    /// for entry in entries {
    ///     added_entries += entry;
    /// }
    /// ```
    fn get_entries_rowwise(&self) -> Vec<T> {
        let mut entries = vec![];

        for i in 0..self.get_num_rows() {
            for j in 0..self.get_num_columns() {
                let entry = unsafe { self.get_entry_unchecked(i, j) };
                entries.push(entry);
            }
        }

        entries
    }

    /// Outputs a [`Vec<T>`] containing all entries of the matrix in a column-wise order, i.e.
    /// a matrix `[[2, 3, 4],[5, 6, 7]]` can be accessed via this function in this order `[2, 5, 3, 6, 4, 7]`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::{MatZ, Z}, traits::*};
    /// let matrix = MatZ::sample_uniform(3, 3, 0, 16).unwrap();
    ///
    /// let entries = matrix.get_entries_columnwise();
    /// let mut added_entries = Z::default();
    /// for entry in entries {
    ///     added_entries += entry;
    /// }
    /// ```
    fn get_entries_columnwise(&self) -> Vec<T> {
        let mut entries = vec![];

        for j in 0..self.get_num_columns() {
            for i in 0..self.get_num_rows() {
                let entry = unsafe { self.get_entry_unchecked(i, j) };
                entries.push(entry);
            }
        }

        entries
    }
}

/// Is implemented by Matrices to get submatrices such as rows, columns, etc.
pub trait MatrixGetSubmatrix
where
    Self: Sized + MatrixDimensions,
{
    /// Outputs the row vector of the specified row.
    ///
    /// Parameters:
    /// - `row`: specifies the row of the matrix to return
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns a row vector of the matrix at the position of the given
    /// `row` or an error if specified row is not part of the matrix.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///   if specified row is not part of the matrix.
    fn get_row(&self, row: impl TryInto<i64> + Display + Clone) -> Result<Self, MathError> {
        let row = evaluate_index_for_vector(row, self.get_num_rows())?;
        Ok(unsafe { self.get_row_unchecked(row) })
    }

    /// Outputs the row vector of the specified row.
    ///
    /// Parameters:
    /// - `row`: specifies the row of the matrix to return
    ///
    /// Returns a row vector of the matrix at the position of the given
    /// `row`.
    ///
    /// # Safety
    /// To use this function safely, make sure that the selected row is part
    /// of the matrix. If it is not, memory leaks, unexpected panics, etc. might
    /// occur.
    unsafe fn get_row_unchecked(&self, row: i64) -> Self {
        self.get_submatrix_unchecked(row, row + 1, 0, self.get_num_columns())
    }

    /// Outputs the column vector of the specified column.
    ///
    /// Parameters:
    /// - `column`: specifies the column of the matrix to return
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns a column vector of the matrix at the position of the given
    /// `column` or an error if specified column is not part of the matrix.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///   if specified column is not part of the matrix.
    fn get_column(&self, column: impl TryInto<i64> + Display + Clone) -> Result<Self, MathError> {
        let column = evaluate_index_for_vector(column, self.get_num_columns())?;
        Ok(unsafe { self.get_column_unchecked(column) })
    }

    /// Outputs the column vector of the specified column.
    ///
    /// Parameters:
    /// - `column`: specifies the row of the matrix to return
    ///
    /// Returns a column vector of the matrix at the position of the given
    /// `column`.
    ///
    /// # Safety
    /// To use this function safely, make sure that the selected column is part
    /// of the matrix. If it is not, memory leaks, unexpected panics, etc. might
    /// occur.
    unsafe fn get_column_unchecked(&self, column: i64) -> Self {
        self.get_submatrix_unchecked(0, self.get_num_rows(), column, column + 1)
    }

    /// Returns a deep copy of the submatrix defined by the given parameters.
    /// All entries starting from `(row_1, col_1)` to `(row_2, col_2)`(inclusively) are collected in
    /// a new matrix.
    /// Note that `row_1 >= row_2` and `col_1 >= col_2` must hold after converting negative indices.
    /// Otherwise the function will panic.
    ///
    /// Parameters:
    /// `row_1`: the starting row of the specified submatrix
    /// `row_2`: the ending row of the specified submatrix
    /// `col_1`: the starting column of the specified submatrix
    /// `col_2`: the ending column of the specified submatrix
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns the submatrix from `(row_1, col_1)` to `(row_2, col_2)`(inclusively)
    /// or an error if any provided row or column is larger than the matrix.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///   if any provided row or column is larger than the matrix.
    ///
    /// # Panics ...
    /// - if `col_1 > col_2` or `row_1 > row_2`.
    fn get_submatrix(
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
        Ok(unsafe { self.get_submatrix_unchecked(row_1, row_2, col_1, col_2) })
    }

    /// Returns a deep copy of the submatrix defined by the given parameters
    /// and does not check the provided dimensions.
    /// There is also a safe version of this function that checks the input.
    ///
    /// Parameters:
    /// `row_1`: the starting row of the submatrix
    /// `row_2`: the ending row of the submatrix
    /// `col_1`: the starting column of the submatrix
    /// `col_2`: the ending column of the submatrix
    ///
    /// Returns the submatrix from `(row_1, col_1)` to `(row_2, col_2)`(exclusively).
    ///
    /// # Safety
    /// To use this function safely, make sure that the selected submatrix is part
    /// of the matrix. If it is not, memory leaks, unexpected panics, etc. might
    /// occur.
    unsafe fn get_submatrix_unchecked(
        &self,
        row_1: i64,
        row_2: i64,
        col_1: i64,
        col_2: i64,
    ) -> Self;

    /// Outputs a [`Vec`] containing all rows of the matrix in order.
    /// Use this function for simple iteration over the rows of the matrix.
    ///
    /// # Example
    /// ```
    /// use qfall_math::{integer::MatZ, traits::MatrixGetSubmatrix};
    /// let matrix = MatZ::sample_uniform(3, 3, 0, 16).unwrap();
    ///
    /// let mut added_rows = MatZ::new(1, 3);
    /// for row in matrix.get_rows() {
    ///     added_rows = added_rows + row;
    /// }
    /// ```
    ///
    /// If an index is required, use `.iter().enumerate()`, e.g. in this case.
    /// ```
    /// use qfall_math::{integer::MatZ, traits::*};
    /// let mut matrix = MatZ::sample_uniform(3, 3, 0, 16).unwrap();
    ///
    /// let mut added_rows = MatZ::new(1, 3);
    /// for (i, row) in matrix.get_rows().iter().enumerate() {
    ///     added_rows = added_rows + row;
    ///     matrix.set_row(i, &added_rows, 0).unwrap();
    /// }
    /// ```
    fn get_rows(&self) -> Vec<Self> {
        let mut rows = vec![];

        for i in 0..self.get_num_rows() {
            let entry = unsafe { self.get_row_unchecked(i) };
            rows.push(entry);
        }

        rows
    }

    /// Outputs a [`Vec`] containing all columns of the matrix in order.
    /// Use this function for simple iteration over the columns of the matrix.
    ///
    /// # Example
    /// ```
    /// use qfall_math::{integer::MatZ, traits::MatrixGetSubmatrix};
    /// let matrix = MatZ::sample_uniform(3, 3, 0, 16).unwrap();
    ///
    /// let mut added_columns = MatZ::new(3, 1);
    /// for column in matrix.get_columns() {
    ///     added_columns = added_columns + column;
    /// }
    /// ```
    ///
    /// If an index is required, use `.iter().enumerate()`, e.g. in this case.
    /// ```
    /// use qfall_math::{integer::MatZ, traits::*};
    /// let mut matrix = MatZ::sample_uniform(3, 3, 0, 16).unwrap();
    ///
    /// let mut added_columns = MatZ::new(3, 1);
    /// for (i, column) in matrix.get_columns().iter().enumerate() {
    ///     added_columns = added_columns + column;
    ///     matrix.set_column(i, &added_columns, 0).unwrap();
    /// }
    /// ```
    fn get_columns(&self) -> Vec<Self> {
        let mut columns = vec![];

        for i in 0..self.get_num_columns() {
            let entry = unsafe { self.get_column_unchecked(i) };
            columns.push(entry);
        }

        columns
    }
}

/// Is implemented by matrices to set entries.
pub trait MatrixSetEntry<T> {
    /// Sets the value of a specific matrix entry according to a given value.
    ///
    /// Returns an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located.
    /// - `column`: specifies the column in which the entry is located.
    /// - `value`: specifies the value to which the entry is set.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        value: T,
    ) -> Result<(), MathError>;

    /// Sets the value of a specific matrix entry according to a given value
    /// without performing any checks, e.g. checking whether the entry is
    /// part of the matrix or if the moduli of the matrices match.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located.
    /// - `column`: specifies the column in which the entry is located.
    /// - `value`: specifies the value to which the entry is set.
    ///
    /// # Safety
    /// To use this function safely, make sure that the selected entry is part
    /// of the matrix. If it is not, memory leaks, unexpected panics, etc. might
    /// occur.
    unsafe fn set_entry_unchecked(&mut self, row: i64, column: i64, value: T);
}

/// Is implemented by matrices to set more than a single entry of the matrix.
pub trait MatrixSetSubmatrix
where
    Self: Sized + MatrixDimensions + CompareBase,
{
    /// Sets a row of the given matrix to the provided row of `other`.
    ///
    /// Parameters:
    /// - `row_0`: specifies the row of `self` that should be modified
    /// - `other`: specifies the matrix providing the row replacing the row in `self`
    /// - `row_1`: specifies the row of `other` providing
    ///   the values replacing the original row in `self`
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified rows is not part of its matrix
    /// or if the number of columns differs.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///   if the provided row index is not defined within the margins of the matrix.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    ///   if the number of columns of `self` and `other` differ.
    fn set_row(
        &mut self,
        row_0: impl TryInto<i64> + Display,
        other: &Self,
        row_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError>;

    /// Sets a column of the given matrix to the provided column of `other`.
    ///
    /// Parameters:
    /// - `col_0`: specifies the column of `self` that should be modified
    /// - `other`: specifies the matrix providing the column replacing the column in `self`
    /// - `col_1`: specifies the column of `other` providing
    ///   the values replacing the original column in `self`
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified columns is not part of its matrix
    /// or if the number of rows differs.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///   if the provided column index is not defined within the margins of the matrix.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    ///   if the number of rows of `self` and `other` differ.
    fn set_column(
        &mut self,
        col_0: impl TryInto<i64> + Display,
        other: &Self,
        col_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError>;

    #[allow(clippy::too_many_arguments)]
    fn set_submatrix(
        &mut self,
        row_self_start: impl TryInto<i64> + Display,
        col_self_start: impl TryInto<i64> + Display,
        other: &Self,
        row_other_start: impl TryInto<i64> + Display,
        col_other_start: impl TryInto<i64> + Display,
        row_other_end: impl TryInto<i64> + Display,
        col_other_end: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        if !self.compare_base(other) {
            return Err(self.call_compare_base_error(other).unwrap());
        }

        let (row_self_start, col_self_start) =
            evaluate_indices_for_matrix(self, row_self_start, col_self_start)?;
        let (row_other_start, col_other_start) =
            evaluate_indices_for_matrix(other, row_other_start, col_other_start)?;
        let (row_other_end, col_other_end) =
            evaluate_indices_for_matrix(other, row_other_end, col_other_end)?;

        assert!(
                row_other_end >= row_other_start,
                "The number of rows must be positive, i.e. row_other_end ({row_other_end}) must be greater or equal row_other_start ({row_other_start})"
            );

        assert!(
                col_other_end >= col_other_start,
                "The number of columns must be positive, i.e. col_other_end ({col_other_end}) must be greater or equal col_other_start ({col_other_start})"
            );

        // increase both values to have an inclusive capturing of the matrix entries
        let (row_other_end, col_other_end) = (row_other_end + 1, col_other_end + 1);
        let nr_rows = row_other_end - row_other_start;
        let nr_cols = col_other_end - col_other_start;
        let row_self_end =
            evaluate_index_for_vector(row_self_start + nr_rows, self.get_num_rows())?;
        let col_self_end =
            evaluate_index_for_vector(col_self_start + nr_cols, self.get_num_columns())?;

        unsafe {
            self.set_submatrix_unchecked(
                row_self_start,
                col_self_start,
                row_self_end,
                col_self_end,
                other,
                row_other_start,
                col_other_start,
                row_other_end,
                col_other_end,
            );
        }

        Ok(())
    }

    /// # Safety
    #[allow(clippy::too_many_arguments)]
    unsafe fn set_submatrix_unchecked(
        &mut self,
        row_self_start: i64,
        col_self_start: i64,
        row_self_end: i64,
        col_self_end: i64,
        other: &Self,
        row_other_start: i64,
        col_other_start: i64,
        row_other_end: i64,
        col_other_end: i64,
    );
}

pub trait MatrixSwaps {
    /// Swaps two entries of the specified matrix.
    ///
    /// Parameters:
    /// - `row_0`: specifies the row, in which the first entry is located
    /// - `col_0`: specifies the column, in which the first entry is located
    /// - `row_1`: specifies the row, in which the second entry is located
    /// - `col_1`: specifies the column, in which the second entry is located
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified entries is not part of the matrix.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///   if row or column are greater than the matrix size.
    fn swap_entries(
        &mut self,
        row_0: impl TryInto<i64> + Display,
        col_0: impl TryInto<i64> + Display,
        row_1: impl TryInto<i64> + Display,
        col_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError>;

    /// Swaps two rows of the specified matrix.
    ///
    /// Parameters:
    /// - `row_0`: specifies the first row which is swapped with the second one
    /// - `row_1`: specifies the second row which is swapped with the first one
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified rows is not part of the matrix.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///   if one of the given rows is not in the matrix.
    fn swap_rows(
        &mut self,
        row_0: impl TryInto<i64> + Display,
        row_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError>;

    /// Swaps two columns of the specified matrix.
    ///
    /// Parameters:
    /// - `col_0`: specifies the first column which is swapped with the second one
    /// - `col_1`: specifies the second column which is swapped with the first one
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified columns is not part of the matrix.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///   if one of the given columns is not in the matrix.
    fn swap_columns(
        &mut self,
        col_0: impl TryInto<i64> + Display,
        col_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError>;
}

/// Is implemented by matrices to compute the tensor product.
pub trait Tensor {
    /// Computes the tensor product of `self` with `other`
    ///
    /// Parameters:
    /// - `other`: the value with which the tensor product is computed.
    ///
    /// Returns the tensor product
    fn tensor_product(&self, other: &Self) -> Self;
}

/// Is implemented by matrices to concatenate them.
pub trait Concatenate {
    type Output;

    /// Concatenates `self` with `other` vertically.
    ///
    /// Parameters:
    /// - `other`: the other matrix to concatenate with `self`
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///   [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    ///   if the matrices can not be concatenated due to mismatching dimensions
    fn concat_vertical(self, other: Self) -> Result<Self::Output, MathError>;

    /// Concatenates `self` with `other` horizontally.
    ///
    /// Parameters:
    /// - `other`: the other matrix to concatenate with `self`
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///   [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    ///   if the matrices can not be concatenated due to mismatching dimensions
    fn concat_horizontal(self, other: Self) -> Result<Self::Output, MathError>;
}

/// Is implemented by basic types to calculate distances.
pub trait Distance<T = Self> {
    type Output;

    /// Computes the absolute distance between two values.
    ///
    /// Parameters:
    /// - `other`: specifies the value whose distance is calculated to `self`
    ///
    /// Returns the absolute difference, i.e. distance between the two given values
    /// as a new instance.
    fn distance(&self, other: T) -> Self::Output;
}

/// Is implemented by [`Z`](crate::integer::Z) instances to compute the `lcm`.
pub trait Lcm<T = Self> {
    type Output;

    /// Outputs the least common multiple (lcm) of the two given values
    /// with `lcm(a, 0) = 0`.
    ///
    /// Parameters:
    /// - `other`: specifies one of the values of which the `lcm` is computed
    ///
    /// Returns the least common multiple of `self` and `other` as a new value.
    fn lcm(&self, other: T) -> Self::Output;
}

/// Is implemented by basic types to raise a value to the power of another.
pub trait Pow<T> {
    type Output;

    /// Raises the value of `self` to the power of an `exp`.
    ///
    /// Parameters:
    /// - `exp`: specifies the exponent to which the value is raised
    ///
    /// Returns the value of `self` powered by `exp` as a new `Output` instance.
    fn pow(&self, exp: T) -> Result<Self::Output, MathError>;
}

/// Is implemented by [`Z`](crate::integer::Z) instances to calculate the `gcd`
pub trait Gcd<T = Self> {
    type Output;

    /// Outputs the greatest common divisor (gcd) of the two given values
    /// with `gcd(a, 0) = |a|`.
    ///
    /// Parameters:
    /// - `other`: specifies one of the values of which the gcd is computed
    ///
    /// Returns the greatest common divisor of `self` and `other`.
    fn gcd(&self, other: T) -> Self::Output;
}

/// Is implemented by [`Z`](crate::integer::Z) instances to calculate the
/// extended `gcd`
pub trait Xgcd<T = Self> {
    type Output;

    /// Outputs the extended greatest common divisor (xgcd) of the two given values,
    /// i.e. a triple `(gcd(a, b), x, y)`, where `a*x + b*y = gcd(a, b)*`.
    ///
    /// Parameters:
    /// - `other`: specifies one of the values of which the gcd is computed
    ///
    /// Returns a triple `(gcd(a, b), x, y)` containing the greatest common divisor,
    /// `x`, and `y` s.t. `gcd(a, b) = a*x + b*y`.
    fn xgcd(&self, other: T) -> Self::Output;
}

/// This is a trait to abstract Integers.
///
/// It is implemented by [`Z`](crate::integer::Z), [`Zq`](crate::integer_mod_q::Zq),
/// [`Modulus`](crate::integer_mod_q::Modulus),
/// and rust's 8, 16, 32, and 64 bit signed and unsigned integers.
/// The implementations exist for their owned and borrowed variants.
///
/// # Safety
/// Handling [`fmpz`] directly requires thinking about memory issues.
/// Read the documentation of the functions carefully before you use them.
pub(crate) unsafe trait AsInteger {
    /// Returns an [`fmpz`] representing the value.
    /// Data about the original object might not be contained in the return value.
    /// For example, [`Zq`](crate::integer_mod_q::Zq)'s return value does not
    /// contain Information about the modulus.
    ///
    /// # Safety
    /// The caller has to ensure that the returned [`fmpz`] is cleared properly.
    /// This is not happening automatically.
    /// Not clearing the [`fmpz`] is a memory leak.
    unsafe fn into_fmpz(self) -> fmpz;

    /// Returns a reference to an internal [`fmpz`] that represents the value.
    /// If the data type does not contain an [`fmpz`] completely [`None`] is returned.
    ///
    /// It is intended to be used when a read only [`fmpz`] reference is required
    /// for a Flint function call.
    /// If the data type does not contain an [`fmpz`], [`into_fmpz`](AsInteger::into_fmpz)
    /// can be used instead.
    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        None
    }
}

/// Is implemented by polynomials to receive a matrix representation of their coefficients.
pub trait IntoCoefficientEmbedding<T> {
    /// Returns a canonical coefficient embedding of the value,
    /// e.g. a matrix representation of the coefficients of a polynomial.
    ///
    /// Parameters:
    /// - `size`: determines the length of the object in which the coefficients are
    ///   embedded, e.g. length of the vector
    fn into_coefficient_embedding(self, size: impl Into<i64>) -> T;
}

/// Is implemented by polynomials to reverse the coefficient embedding.
pub trait FromCoefficientEmbedding<T> {
    /// Reverses the coefficient embedding, e.g. takes as input a vector and
    /// returns a polynomial.
    ///
    /// Parameters:
    /// - `embedding`: the coefficient embedding
    fn from_coefficient_embedding(embedding: T) -> Self;
}
