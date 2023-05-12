// Copyright © 2023 Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation to set entries from a [`MatZq`] matrix.

use crate::{
    error::MathError,
    integer::Z,
    integer_mod_q::{MatZq, Zq},
    macros::for_others::{implement_for_others, implement_for_owned},
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::index::{evaluate_index, evaluate_indices},
};
use flint_sys::{
    fmpz_mat::{
        fmpz_mat_invert_cols, fmpz_mat_invert_rows, fmpz_mat_swap_cols, fmpz_mat_swap_rows,
    },
    fmpz_mod_mat::fmpz_mod_mat_set_entry,
};
use std::{
    fmt::Display,
    ptr::{null, null_mut},
};

impl SetEntry<&Z> for MatZq {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`Z`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    /// use qfall_math::traits::*;
    ///
    /// let mut matrix = MatZq::new(5, 10, 7).unwrap();
    /// let value = Z::from(5);
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
        value: &Z,
    ) -> Result<(), MathError> {
        // Calculate mod q before adding the entry to the matrix.
        let value: Zq = Zq::from_z_modulus(value, &self.get_mod());

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
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::traits::SetEntry;
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZq::new(5, 10, 7).unwrap();
    /// let value = Zq::from_str("5 mod 7").unwrap();
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
        value: &Zq,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_indices(self, row, column)?;

        if self.get_mod() != value.modulus {
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

implement_for_owned!(Z, MatZq, SetEntry);
implement_for_owned!(Zq, MatZq, SetEntry);

implement_for_others!(Z, MatZq, SetEntry for i8 i16 i32 i64 u8 u16 u32 u64);

impl MatZq {
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
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mut matrix = MatZq::new(4, 3, 5).unwrap();
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
        unsafe { fmpz_mat_swap_cols(&mut self.matrix.mat[0], null(), col0, col1) }
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
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mut matrix = MatZq::new(4, 3, 5).unwrap();
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
        unsafe { fmpz_mat_swap_rows(&mut self.matrix.mat[0], null(), row0, row1) }
        Ok(())
    }

    /// Reverses all columns of the specified matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mut matrix = MatZq::new(4, 3, 5).unwrap();
    /// matrix.reverse_columns();
    /// ```
    pub fn reverse_columns(&mut self) {
        unsafe { fmpz_mat_invert_cols(&mut self.matrix.mat[0], null_mut()) }
    }

    /// Reverses all rows of the specified matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mut matrix = MatZq::new(4, 3, 5).unwrap();
    /// matrix.reverse_rows();
    /// ```
    pub fn reverse_rows(&mut self) {
        unsafe { fmpz_mat_invert_rows(&mut self.matrix.mat[0], null_mut()) }
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
        let mut matrix = MatZq::new(5, 10, u64::MAX).unwrap();
        let value = Z::from(i64::MAX);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from(i64::MAX), entry);
    }

    /// Ensure that setting entries works with large numbers (larger than [`i64`]).
    #[test]
    fn big_positive() {
        let mut matrix = MatZq::new(5, 10, u64::MAX).unwrap();
        let value = Z::from(u64::MAX - 1);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from(u64::MAX - 1), entry);
    }

    /// Ensure that setting entries works with large numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatZq::new(5, 10, u64::MAX).unwrap();
        let value = Z::from(-i64::MAX);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from((u64::MAX as i128 - i64::MAX as i128) as u64), entry);
    }

    /// Ensure that setting entries works with large numbers (larger than [`i64`]).
    #[test]
    fn big_negative() {
        let mut matrix = MatZq::new(5, 10, u64::MAX).unwrap();
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
        let mut matrix = MatZq::new(5, 10, 7).unwrap();

        assert!(matrix.set_entry(5, 1, 3).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let mut matrix = MatZq::new(5, 10, 7).unwrap();

        assert!(matrix.set_entry(1, 100, 3).is_err());
    }

    /// Ensure that setting entries works with different types.
    #[test]
    fn diff_types() {
        let mut matrix = MatZq::new(5, 10, 56).unwrap();

        matrix.set_entry(0, 0, Z::default()).unwrap();
        matrix
            .set_entry(0, 0, Zq::from_str("12 mod 56").unwrap())
            .unwrap();
        matrix.set_entry(0, 0, 3).unwrap();
        matrix.set_entry(0, 0, &Z::default()).unwrap();
        matrix
            .set_entry(0, 0, &Zq::from_str("12 mod 56").unwrap())
            .unwrap();
    }

    /// Ensure that value is correctly reduced.
    #[test]
    fn set_entry_reduce() {
        let mut matrix = MatZq::new(5, 10, 3).unwrap();
        matrix.set_entry(1, 1, Z::from(u64::MAX)).unwrap();

        let entry: Z = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from(0));
    }

    /// Ensure that differing moduli result in an error.
    #[test]
    fn modulus_error() {
        let mut matrix = MatZq::new(5, 10, 3).unwrap();
        assert!(matrix
            .set_entry(1, 1, Zq::from_str("2 mod 5").unwrap())
            .is_err());
    }
}

#[cfg(test)]
mod test_swaps {
    use super::MatZq;
    use std::str::FromStr;

    /// Ensures that swapping columns works fine for small entries
    #[test]
    fn columns_small_entries() {
        let mut matrix = MatZq::from_str("[[1,2,3],[4,5,6]] mod 17").unwrap();
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
            "[[{},1,3, 4],[{},4,{},5],[7,6,8,9]] mod {}",
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

    /// Ensures that `swap_columns` returns an error if one of the specified columns is out of bounds
    #[test]
    fn column_out_of_bounds() {
        let mut matrix = MatZq::new(5, 2, 5).unwrap();

        assert!(matrix.swap_columns(-1, 0).is_err());
        assert!(matrix.swap_columns(0, -1).is_err());
        assert!(matrix.swap_columns(5, 0).is_err());
        assert!(matrix.swap_columns(0, 5).is_err());
    }

    /// Ensures that swapping rows works fine for small entries
    #[test]
    fn rows_small_entries() {
        let mut matrix = MatZq::from_str("[[1,2],[3,4]] mod 12").unwrap();
        let cmp_vec_0 = MatZq::from_str("[[3,4]] mod 12").unwrap();
        let cmp_vec_1 = MatZq::from_str("[[1,2]] mod 12").unwrap();

        let _ = matrix.swap_rows(1, 0);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
    }

    /// Ensures that swapping rows works fine for large entries
    #[test]
    fn rows_large_entries() {
        let mut matrix = MatZq::from_str(&format!(
            "[[{},1,3, 4],[7,6,8,9],[{},4,{},5]] mod {}",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 = MatZq::from_str(&format!(
            "[[{},4,{},5]] mod {}",
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_1 = MatZq::from_str(&format!("[[7,6,8,9]] mod {}", u64::MAX)).unwrap();
        let cmp_vec_2 =
            MatZq::from_str(&format!("[[{},1,3, 4]] mod {}", i64::MIN, u64::MAX)).unwrap();

        let _ = matrix.swap_rows(0, 2);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_row(2).unwrap());
    }

    /// Ensures that `swap_rows` returns an error if one of the specified rows is out of bounds
    #[test]
    fn row_out_of_bounds() {
        let mut matrix = MatZq::new(2, 4, 5).unwrap();

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
        let mut matrix = MatZq::from_str("[[1,2,3],[4,5,6]] mod 7").unwrap();
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
            "[[{},1,3, 4],[{},4,{},5],[7,6,8,9]] mod {}",
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

        let _ = matrix.reverse_columns();

        assert_eq!(cmp_vec_3, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(2).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_column(3).unwrap());
    }

    /// Ensures that reversing rows works fine for small entries
    #[test]
    fn rows_small_entries() {
        let mut matrix = MatZq::from_str("[[1,2],[3,4]] mod 6").unwrap();
        let cmp_vec_0 = MatZq::from_str("[[1,2]] mod 6").unwrap();
        let cmp_vec_1 = MatZq::from_str("[[3,4]] mod 6").unwrap();

        let _ = matrix.reverse_rows();

        assert_eq!(cmp_vec_1, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(1).unwrap());
    }

    /// Ensures that reversing rows works fine for large entries
    #[test]
    fn rows_large_entries() {
        let mut matrix = MatZq::from_str(&format!(
            "[[{},1,3, 4],[7,6,8,9],[{},4,{},5]] mod {}",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_0 =
            MatZq::from_str(&format!("[[{},1,3, 4]] mod {}", i64::MIN, u64::MAX)).unwrap();
        let cmp_vec_1 = MatZq::from_str(&format!("[[7,6,8,9]] mod {}", u64::MAX)).unwrap();
        let cmp_vec_2 = MatZq::from_str(&format!(
            "[[{},4,{},5]] mod {}",
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();

        let _ = matrix.reverse_rows();

        assert_eq!(cmp_vec_2, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(2).unwrap());
    }
}
