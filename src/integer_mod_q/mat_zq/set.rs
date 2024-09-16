// Copyright © 2023 Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation to manipulate a [`MatZq`] matrix.

use crate::{
    error::MathError,
    integer::Z,
    integer_mod_q::{MatZq, Modulus, Zq},
    macros::for_others::implement_for_owned,
    traits::{AsInteger, GetNumColumns, GetNumRows, SetEntry},
    utils::{
        collective_evaluation::evaluate_vec_dimensions_set_row_or_col,
        index::{evaluate_index, evaluate_indices_for_matrix},
    },
};
use flint_sys::{
    fmpz::{fmpz_set, fmpz_swap},
    fmpz_mat::{
        fmpz_mat_entry, fmpz_mat_invert_cols, fmpz_mat_invert_rows, fmpz_mat_swap_cols,
        fmpz_mat_swap_rows,
    },
    fmpz_mod_mat::{_fmpz_mod_mat_reduce, _fmpz_mod_mat_set_mod, fmpz_mod_mat_set_entry},
};
use std::{
    fmt::Display,
    ptr::{null, null_mut},
};

impl<Integer: Into<Z>> SetEntry<Integer> for MatZq {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`Z`].
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
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::traits::*;
    ///
    /// let mut matrix = MatZq::new(3, 3, 10);
    ///
    /// matrix.set_entry(0, 1, 5).unwrap();
    /// matrix.set_entry(-1, 2, 19).unwrap();
    ///
    /// assert_eq!("[[0, 5, 0],[0, 0, 0],[0, 0, 9]] mod 10", matrix.to_string());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///     if `row` or `column` are greater than the matrix size.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        value: Integer,
    ) -> Result<(), MathError> {
        // Calculate mod q before adding the entry to the matrix.
        let value: Zq = Zq::from((value, &self.modulus));

        self.set_entry(row, column, value)
    }
}

impl SetEntry<&Zq> for MatZq {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`Zq`].
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
    /// Otherwise, a [`MathError`] is returned if either the specified entry
    /// is not part of the matrix or the moduli mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatZq, Zq};
    /// use qfall_math::traits::SetEntry;
    ///
    /// let mut matrix = MatZq::new(3, 3, 10);
    /// let value = Zq::from((5, 10));
    ///
    /// matrix.set_entry(0, 1, &value).unwrap();
    /// matrix.set_entry(-1, 2, Zq::from((9, 10))).unwrap();
    ///
    /// assert_eq!("[[0, 5, 0],[0, 0, 0],[0, 0, 9]] mod 10", matrix.to_string());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///     if `row` or `column` are greater than the matrix size.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`]
    ///     if the moduli mismatch.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        value: &Zq,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_indices_for_matrix(self, row, column)?;

        if self.modulus != value.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Modulus of matrix: '{}'. Modulus of value: '{}'.
            If the modulus should be ignored please convert into a Z beforehand.",
                self.get_mod(),
                value.modulus
            )));
        }

        unsafe {
            // get entry and replace the pointed at value with the specified value
            fmpz_mod_mat_set_entry(&mut self.matrix, row_i64, column_i64, &value.value.value)
        }

        Ok(())
    }
}

implement_for_owned!(Zq, MatZq, SetEntry);

impl MatZq {
    /// Sets a column of the given matrix to the provided column of `other`.
    ///
    /// Parameters:
    /// - `col_0`: specifies the column of `self` that should be modified
    /// - `other`: specifies the matrix providing the column replacing the column in `self`
    /// - `col_1`: specifies the column of `other` providing
    ///     the values replacing the original column in `self`
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    ///     Otherwise, a [`MathError`] is returned if one of the specified columns is not part of its matrix
    ///     or if the number of rows differs.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mut mat_1 = MatZq::new(2, 2, 3);
    /// let mat_2 = MatZq::from_str("[[1],[2]] mod 3").unwrap();
    /// mat_1.set_column(1, &mat_2, 0);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///     if the number of columns is greater than the matrix dimensions or negative.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    ///     if the number of rows of `self` and `other` differ.
    /// - Returns a [`MathError`] of type [`MismatchingModulus`](MathError::MismatchingModulus)
    ///     if the moduli of `self` and `other` mismatch.
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

        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                "set_column requires the moduli to be equal, but {} differs from {}",
                self.get_mod(),
                other.get_mod()
            )));
        }

        for row in 0..self.get_num_rows() {
            unsafe {
                fmpz_set(
                    fmpz_mat_entry(&self.matrix.mat[0], row, col_0),
                    fmpz_mat_entry(&other.matrix.mat[0], row, col_1),
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
    ///     the values replacing the original row in `self`
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified rows is not part of its matrix
    /// or if the number of columns differs.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mut mat_1 = MatZq::new(2, 2, 3);
    /// let mat_2 = MatZq::from_str("[[1, 2]] mod 3").unwrap();
    /// mat_1.set_row(0, &mat_2, 0);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///     if the number of rows is greater than the matrix dimensions or negative.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    ///     if the number of columns of `self` and `other` differ.
    /// - Returns a [`MathError`] of type [`MismatchingModulus`](MathError::MismatchingModulus)
    ///     if the moduli of `self` and `other` mismatch.
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

        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                "set_row requires the moduli to be equal, but {} differs from {}",
                self.get_mod(),
                other.get_mod()
            )));
        }

        for col in 0..self.get_num_columns() {
            unsafe {
                fmpz_set(
                    fmpz_mat_entry(&self.matrix.mat[0], row_0, col),
                    fmpz_mat_entry(&other.matrix.mat[0], row_1, col),
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
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mut matrix = MatZq::new(4, 3, 5);
    /// matrix.swap_entries(0, 0, 2, 1);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///     if row or column are greater than the matrix size.
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
            fmpz_swap(
                fmpz_mat_entry(&self.matrix.mat[0], row_0, col_0),
                fmpz_mat_entry(&self.matrix.mat[0], row_1, col_1),
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
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mut matrix = MatZq::new(4, 3, 5);
    /// matrix.swap_columns(0, 2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///     if one of the given columns is greater than the matrix or negative.
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
        unsafe { fmpz_mat_swap_cols(&mut self.matrix.mat[0], null(), col_0, col_1) }
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
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mut matrix = MatZq::new(4, 3, 5);
    /// matrix.swap_rows(0, 2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///     if one of the given rows is greater than the matrix or negative.
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
        unsafe { fmpz_mat_swap_rows(&mut self.matrix.mat[0], null(), row_0, row_1) }
        Ok(())
    }

    /// Swaps the `i`-th column with the `n-i`-th column for all `i <= n/2`
    /// of the specified matrix with `n` columns.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mut matrix = MatZq::new(4, 3, 5);
    /// matrix.reverse_columns();
    /// ```
    pub fn reverse_columns(&mut self) {
        // If the second argument to this function is not null, the permutation
        // of the columns is also applied to this argument.
        // Hence, passing in null is justified here.
        unsafe { fmpz_mat_invert_cols(&mut self.matrix.mat[0], null_mut()) }
    }

    /// Swaps the `i`-th row with the `n-i`-th row for all `i <= n/2`
    /// of the specified matrix with `n` rows.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mut matrix = MatZq::new(4, 3, 5);
    /// matrix.reverse_rows();
    /// ```
    pub fn reverse_rows(&mut self) {
        // If the second argument to this function is not null, the permutation
        // of the rows is also applied to this argument.
        // Hence, passing in null is justified here.
        unsafe { fmpz_mat_invert_rows(&mut self.matrix.mat[0], null_mut()) }
    }

    /// Changes the modulus of the given matrix to the new modulus.
    /// It takes the representation of each coefficient in [0, q) as the new
    /// matrix entries and reduces them by the new modulus automatically.
    ///
    /// Parameters:
    /// - `modulus`: The new modulus of the matrix
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatZq, Modulus};
    /// use std::str::FromStr;
    ///
    /// let mut mat = MatZq::from_str("[[1, 2]] mod 3").unwrap();
    /// mat.change_modulus(2);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    pub fn change_modulus(&mut self, modulus: impl Into<Modulus>) {
        self.modulus = modulus.into();
        unsafe {
            _fmpz_mod_mat_set_mod(&mut self.matrix, self.modulus.get_fmpz_ref().unwrap());
            _fmpz_mod_mat_reduce(&mut self.matrix)
        }
    }
}

#[cfg(test)]
mod test_setter {
    use crate::{
        integer::Z,
        integer_mod_q::{MatZq, Zq},
        traits::{GetEntry, SetEntry},
    };
    use std::str::FromStr;

    /// Ensure that setting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatZq::new(5, 10, u64::MAX);
        let value = Z::from(i64::MAX);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from(i64::MAX), entry);
    }

    /// Ensure that setting entries works with large numbers (larger than [`i64`]).
    #[test]
    fn large_positive() {
        let mut matrix = MatZq::new(5, 10, u64::MAX);
        let value = Z::from(u64::MAX - 1);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from(u64::MAX - 1), entry);
    }

    /// Ensure that setting entries works with large numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatZq::new(5, 10, u64::MAX);
        let value = Z::from(-i64::MAX);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from((u64::MAX as i128 - i64::MAX as i128) as u64), entry);
    }

    /// Ensure that setting entries works with large numbers (larger than [`i64`]).
    #[test]
    fn large_negative() {
        let mut matrix = MatZq::new(5, 10, u64::MAX);
        let value = Z::from(-i64::MAX - 1);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(
            Z::from((u64::MAX as i128 - i64::MAX as i128) as u64 - 1),
            entry
        );
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let mut matrix = MatZq::new(5, 10, 7);

        assert!(matrix.set_entry(5, 1, 3).is_err());
        assert!(matrix.set_entry(-6, 1, 1).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let mut matrix = MatZq::new(5, 10, 7);

        assert!(matrix.set_entry(1, 100, 3).is_err());
        assert!(matrix.set_entry(1, -11, 1).is_err());
    }

    /// Ensure that setting entries works with different types.
    #[test]
    fn diff_types() {
        let mut matrix = MatZq::new(5, 10, 56);

        matrix.set_entry(0, 0, Z::default()).unwrap();
        matrix.set_entry(0, 0, Zq::from((12, 56))).unwrap();
        matrix.set_entry(0, 0, 3).unwrap();
        matrix.set_entry(0, 0, &Z::default()).unwrap();
        matrix.set_entry(0, 0, &Zq::from((12, 56))).unwrap();
    }

    /// Ensure that negative indices return address the correct entires.
    #[test]
    fn negative_indexing() {
        let mut matrix = MatZq::new(3, 3, 10);

        matrix.set_entry(-1, -1, 9).unwrap();
        matrix.set_entry(-1, -2, 8).unwrap();
        matrix.set_entry(-3, -3, Zq::from((1, 10))).unwrap();

        let matrix_cmp = MatZq::from_str("[[1, 0, 0],[0, 0, 0],[0, 8, 9]] mod 10").unwrap();
        assert_eq!(matrix_cmp, matrix);
    }

    /// Ensure that value is correctly reduced.
    #[test]
    fn set_entry_reduce() {
        let mut matrix = MatZq::new(5, 10, 3);
        matrix.set_entry(1, 1, Z::from(u64::MAX)).unwrap();

        let entry: Z = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from(0));
    }

    /// Ensure that differing moduli result in an error.
    #[test]
    fn modulus_error() {
        let mut matrix = MatZq::new(5, 10, 3);
        assert!(matrix.set_entry(1, 1, Zq::from((2, 5))).is_err());
    }

    /// Ensures that setting columns works fine for small entries
    #[test]
    fn column_small_entries() {
        let mut mat_1 = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 11").unwrap();
        let mat_2 = MatZq::from_str("[[0],[-1]] mod 11").unwrap();

        let cmp = MatZq::from_str("[[1, 0, 3],[4, -1, 6]] mod 11").unwrap();

        let _ = mat_1.set_column(1, &mat_2, 0);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting columns works fine for large entries
    #[test]
    fn column_large_entries() {
        let mut mat_1 = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatZq::from_str(&format!(
            "[[1, {}],[{}, 0],[7, -1]] mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[0, 4, {}, 5],[-1, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();

        let _ = mat_1.set_column(0, &mat_2, 1);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting the column to itself does not change anything
    #[test]
    fn column_swap_same_entry() {
        let mut mat_1 = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
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
        let mut mat_1 = MatZq::new(5, 2, 17);
        let mat_2 = mat_1.clone();

        assert!(mat_1.set_column(-1, &mat_2, 0).is_err());
        assert!(mat_1.set_column(2, &mat_2, 0).is_err());
        assert!(mat_1.set_column(1, &mat_2, -1).is_err());
        assert!(mat_1.set_column(1, &mat_2, 2).is_err());
    }

    /// Ensures that mismatching row dimensions result in an error
    #[test]
    fn column_mismatching_columns() {
        let mut mat_1 = MatZq::new(5, 2, 17);
        let mat_2 = MatZq::new(2, 2, 17);

        assert!(mat_1.set_column(0, &mat_2, 0).is_err());
        assert!(mat_1.set_column(1, &mat_2, 1).is_err());
    }

    /// Ensures that mismatching moduli result in an error
    #[test]
    fn column_mismatching_moduli() {
        let mut mat_1 = MatZq::new(3, 3, 19);
        let mat_2 = MatZq::new(3, 3, 17);

        assert!(mat_1.set_column(0, &mat_2, 0).is_err());
    }

    /// Ensures that setting rows works fine for small entries
    #[test]
    fn row_small_entries() {
        let mut mat_1 = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 11").unwrap();
        let mat_2 = MatZq::from_str("[[0, -1, 2]] mod 11").unwrap();
        let cmp = MatZq::from_str("[[1, 2, 3],[0, -1, 2]] mod 11").unwrap();

        let _ = mat_1.set_row(1, &mat_2, 0);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting rows works fine for large entries
    #[test]
    fn row_large_entries() {
        let mut mat_1 = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatZq::from_str(&format!(
            "[[0, 0, 0, 0],[{}, 0, {}, 0]] mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatZq::from_str(&format!(
            "[[{}, 0, {}, 0],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
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
        let mut mat_1 = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
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
        let mut mat_1 = MatZq::new(5, 2, 17);
        let mat_2 = mat_1.clone();

        assert!(mat_1.set_row(-1, &mat_2, 0).is_err());
        assert!(mat_1.set_row(5, &mat_2, 0).is_err());
        assert!(mat_1.set_row(2, &mat_2, -1).is_err());
        assert!(mat_1.set_row(2, &mat_2, 5).is_err());
    }

    /// Ensures that mismatching column dimensions result in an error
    #[test]
    fn row_mismatching_columns() {
        let mut mat_1 = MatZq::new(3, 2, 17);
        let mat_2 = MatZq::new(3, 3, 17);

        assert!(mat_1.set_row(0, &mat_2, 0).is_err());
        assert!(mat_1.set_row(1, &mat_2, 1).is_err());
    }

    /// Ensures that mismatching moduli result in an error
    #[test]
    fn row_mismatching_moduli() {
        let mut mat_1 = MatZq::new(3, 3, 19);
        let mat_2 = MatZq::new(3, 3, 17);

        assert!(mat_1.set_row(0, &mat_2, 0).is_err());
    }
}

#[cfg(test)]
mod test_swaps {
    use super::MatZq;
    use std::str::FromStr;

    /// Ensures that swapping entries works fine for small entries
    #[test]
    fn entries_small_entries() {
        let mut matrix = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 7").unwrap();
        let cmp = MatZq::from_str("[[1, 5, 3],[4, 2, 6]] mod 7").unwrap();

        let _ = matrix.swap_entries(1, 1, 0, 1);

        assert_eq!(cmp, matrix);
    }

    /// Ensures that swapping entries works fine for large entries
    #[test]
    fn entries_large_entries() {
        let mut matrix = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MAX,
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        let _ = matrix.swap_entries(0, 0, 1, 2);

        assert_eq!(cmp, matrix);
    }

    /// Ensures that swapping the same entry does not change anything
    #[test]
    fn entries_swap_same_entry() {
        let mut matrix = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
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
        let mut matrix = MatZq::new(5, 2, 5);

        assert!(matrix.swap_entries(-6, 0, 0, 0).is_err());
        assert!(matrix.swap_entries(0, -3, 0, 0).is_err());
        assert!(matrix.swap_entries(0, 0, 5, 0).is_err());
        assert!(matrix.swap_entries(0, 5, 0, 0).is_err());
    }

    /// Ensure that `swap_entries` can properly handle negative indexing.
    #[test]
    fn entries_negative_indexing() {
        let mut matrix = MatZq::identity(2, 2, 2);

        matrix.swap_entries(-2, -2, -2, -1).unwrap();
        assert_eq!("[[0, 1],[0, 1]] mod 2", matrix.to_string());
    }

    /// Ensures that swapping columns works fine for small entries
    #[test]
    fn columns_small_entries() {
        let mut matrix = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 17").unwrap();
        let cmp_vec_0 = MatZq::from_str("[[1],[4]] mod 17").unwrap();
        let cmp_vec_1 = MatZq::from_str("[[3],[6]] mod 17").unwrap();
        let cmp_vec_2 = MatZq::from_str("[[2],[5]] mod 17").unwrap();

        let _ = matrix.swap_columns(1, 2);

        assert_eq!(cmp_vec_0, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(2).unwrap());
    }

    /// Ensures that swapping columns works fine for large entries
    #[test]
    fn columns_large_entries() {
        let mut matrix = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 =
            MatZq::from_str(&format!("[[3],[{}],[8]] mod {}", i64::MAX, u64::MAX)).unwrap();
        let cmp_vec_1 = MatZq::from_str(&format!("[[1],[4],[6]] mod {}", u64::MAX)).unwrap();
        let cmp_vec_2 = MatZq::from_str(&format!(
            "[[{}],[{}],[7]] mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_3 = MatZq::from_str(&format!("[[4],[5],[9]] mod {}", u64::MAX)).unwrap();

        let _ = matrix.swap_columns(0, 2);

        assert_eq!(cmp_vec_0, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(2).unwrap());
        assert_eq!(cmp_vec_3, matrix.get_column(3).unwrap());
    }

    /// Ensures that swapping the same column does not change anything
    #[test]
    fn columns_swap_same_col() {
        let mut matrix = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
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
        let mut matrix = MatZq::new(5, 2, 5);

        assert!(matrix.swap_columns(-1, 0).is_err());
        assert!(matrix.swap_columns(0, -1).is_err());
        assert!(matrix.swap_columns(5, 0).is_err());
        assert!(matrix.swap_columns(0, 5).is_err());
    }

    /// Ensures that swapping rows works fine for small entries
    #[test]
    fn rows_small_entries() {
        let mut matrix = MatZq::from_str("[[1, 2],[3, 4]] mod 12").unwrap();
        let cmp_vec_0 = MatZq::from_str("[[3, 4]] mod 12").unwrap();
        let cmp_vec_1 = MatZq::from_str("[[1, 2]] mod 12").unwrap();

        let _ = matrix.swap_rows(1, 0);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
    }

    /// Ensures that swapping rows works fine for large entries
    #[test]
    fn rows_large_entries() {
        let mut matrix = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[7, 6, 8, 9],[{}, 4, {}, 5]] mod {}",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 = MatZq::from_str(&format!(
            "[[{}, 4, {}, 5]] mod {}",
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_1 = MatZq::from_str(&format!("[[7, 6, 8, 9]] mod {}", u64::MAX)).unwrap();
        let cmp_vec_2 =
            MatZq::from_str(&format!("[[{}, 1, 3, 4]] mod {}", i64::MIN, u64::MAX)).unwrap();

        let _ = matrix.swap_rows(0, 2);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_row(2).unwrap());
    }

    /// Ensures that swapping the same row does not change anything
    #[test]
    fn rows_swap_same_row() {
        let mut matrix = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
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
        let mut matrix = MatZq::new(2, 4, 5);

        assert!(matrix.swap_rows(-1, 0).is_err());
        assert!(matrix.swap_rows(0, -1).is_err());
        assert!(matrix.swap_rows(4, 0).is_err());
        assert!(matrix.swap_rows(0, 4).is_err());
    }
}

#[cfg(test)]
mod test_reverses {
    use super::MatZq;
    use std::str::FromStr;

    /// Ensures that reversing columns works fine for small entries
    #[test]
    fn columns_small_entries() {
        let mut matrix = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 7").unwrap();
        let cmp_vec_0 = MatZq::from_str("[[1],[4]] mod 7").unwrap();
        let cmp_vec_1 = MatZq::from_str("[[2],[5]] mod 7").unwrap();
        let cmp_vec_2 = MatZq::from_str("[[3],[6]] mod 7").unwrap();

        matrix.reverse_columns();

        assert_eq!(cmp_vec_2, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_column(2).unwrap());
    }

    /// Ensures that reversing columns works fine for large entries
    #[test]
    fn columns_large_entries() {
        let mut matrix = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[{}, 4, {}, 5],[7, 6, 8, 9]] mod {}",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 = MatZq::from_str(&format!(
            "[[{}],[{}],[7]] mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_1 = MatZq::from_str(&format!("[[1],[4],[6]] mod {}", u64::MAX)).unwrap();
        let cmp_vec_2 =
            MatZq::from_str(&format!("[[3],[{}],[8]] mod {}", i64::MAX, u64::MAX)).unwrap();
        let cmp_vec_3 = MatZq::from_str(&format!("[[4],[5],[9]] mod {}", u64::MAX)).unwrap();

        matrix.reverse_columns();

        assert_eq!(cmp_vec_3, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(2).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_column(3).unwrap());
    }

    /// Ensures that reversing rows works fine for small entries
    #[test]
    fn rows_small_entries() {
        let mut matrix = MatZq::from_str("[[1, 2],[3, 4]] mod 6").unwrap();
        let cmp_vec_0 = MatZq::from_str("[[1, 2]] mod 6").unwrap();
        let cmp_vec_1 = MatZq::from_str("[[3, 4]] mod 6").unwrap();

        matrix.reverse_rows();

        assert_eq!(cmp_vec_1, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(1).unwrap());
    }

    /// Ensures that reversing rows works fine for large entries
    #[test]
    fn rows_large_entries() {
        let mut matrix = MatZq::from_str(&format!(
            "[[{}, 1, 3, 4],[7, 6, 8, 9],[{}, 4, {}, 5]] mod {}",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 =
            MatZq::from_str(&format!("[[{}, 1, 3, 4]] mod {}", i64::MIN, u64::MAX)).unwrap();
        let cmp_vec_1 = MatZq::from_str(&format!("[[7, 6, 8, 9]] mod {}", u64::MAX)).unwrap();
        let cmp_vec_2 = MatZq::from_str(&format!(
            "[[{}, 4, {}, 5]] mod {}",
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();

        matrix.reverse_rows();

        assert_eq!(cmp_vec_2, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(2).unwrap());
    }
}

#[cfg(test)]
mod test_change_modulus {
    use super::MatZq;
    use crate::integer_mod_q::Modulus;
    use std::str::FromStr;

    /// Ensures that the modulus is changed correctly.
    #[test]
    fn modulus_correct() {
        let mut matrix = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 7").unwrap();
        let modulus = Modulus::from(8);

        matrix.change_modulus(&modulus);

        assert_eq!("[[1, 2, 3],[4, 5, 6]] mod 8", matrix.to_string());
    }

    /// Ensures that the modulus is changed correctly, if the modulus is big.
    #[test]
    fn big_modulus_correct() {
        let mut matrix =
            MatZq::from_str(&format!("[[1, 2, 3],[4, 5, 6]] mod {}", i64::MAX)).unwrap();
        let modulus = Modulus::from(u64::MAX);

        matrix.change_modulus(&modulus);

        assert_eq!(
            format!("[[1, 2, 3],[4, 5, 6]] mod {}", u64::MAX),
            matrix.to_string()
        );
    }

    /// Ensures that the matrix is reduced correctly.
    #[test]
    fn reduced_correct() {
        let mut matrix = MatZq::from_str("[[1, 2, 3],[4, 5, 6]] mod 7").unwrap();
        let modulus = Modulus::from(2);

        matrix.change_modulus(&modulus);

        assert_eq!("[[1, 0, 1],[0, 1, 0]] mod 2", matrix.to_string());
    }
}
