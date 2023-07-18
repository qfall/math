// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`MatZq`] matrix.

use super::MatZq;
use crate::{
    error::MathError,
    integer::Z,
    integer_mod_q::{fmpz_mod_helpers::length, Modulus, Zq},
    traits::{GetEntry, GetNumColumns, GetNumRows},
    utils::index::{evaluate_index, evaluate_indices_for_matrix},
};
use flint_sys::{
    fmpz::{fmpz, fmpz_set},
    fmpz_mat::fmpz_mat_entry,
    fmpz_mod_mat::fmpz_mod_mat_entry,
};
use std::fmt::Display;

impl MatZq {
    /// Returns the modulus of the matrix as a [`Modulus`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::new(5, 10, 7);
    /// let entry = matrix.get_mod();
    /// ```
    pub fn get_mod(&self) -> Modulus {
        self.modulus.clone()
    }
}

impl GetNumRows for MatZq {
    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatZq::new(5, 6, 7);
    /// let rows = matrix.get_num_rows();
    /// ```
    fn get_num_rows(&self) -> i64 {
        self.matrix.mat[0].r
    }
}

impl GetNumColumns for MatZq {
    /// Returns the number of columns of the matrix as a [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatZq::new(5, 6, 7);
    /// let rows = matrix.get_num_columns();
    /// ```
    fn get_num_columns(&self) -> i64 {
        self.matrix.mat[0].c
    }
}

impl GetEntry<Z> for MatZq {
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
    /// ```rust
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::traits::GetEntry;
    /// use qfall_math::integer::Z;
    ///
    /// let matrix = MatZq::new(5, 10, 7);
    /// let entry: Z = matrix.get_entry(0, 1).unwrap();
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

        let mut out = Z::default();
        let entry = unsafe { fmpz_mod_mat_entry(&self.matrix, row_i64, column_i64) };
        unsafe { fmpz_set(&mut out.value, entry) };
        Ok(out)
    }
}

impl GetEntry<Zq> for MatZq {
    /// Outputs the [`Zq`] value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Returns the [`Zq`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::traits::GetEntry;
    /// use qfall_math::integer::Z;
    ///
    /// let matrix = MatZq::new(5, 10, 7);
    /// let entry: Z = matrix.get_entry(0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    fn get_entry(
        &self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
    ) -> Result<Zq, MathError> {
        let value: Z = self.get_entry(row, column)?;

        Ok(Zq::from((value, &self.modulus)))
    }
}

impl MatZq {
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
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 4").unwrap();
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

        let out = MatZq::new(1, self.get_num_columns(), self.get_mod());
        for column in 0..self.get_num_columns() {
            unsafe {
                fmpz_set(
                    fmpz_mat_entry(&out.matrix.mat[0], 0, column),
                    fmpz_mod_mat_entry(&self.matrix, row_i64, column),
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
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 4").unwrap();
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

        let out = MatZq::new(self.get_num_rows(), 1, self.get_mod());
        for row in 0..self.get_num_rows() {
            unsafe {
                fmpz_set(
                    fmpz_mat_entry(&out.matrix.mat[0], row, 0),
                    fmpz_mod_mat_entry(&self.matrix, row, column_i64),
                )
            };
        }
        Ok(out)
    }

    /// Efficiently collects all [`fmpz`]s in a [`MatZq`] without cloning them.
    ///
    /// Hence, the values on the returned [`Vec`] are intended for short-term use
    /// as the access to [`fmpz`] values could lead to memory leaks or modified values
    /// once the [`MatZq`] instance was modified or dropped.
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mat = MatZq::from_str("[[1,2],[3,4],[5,6]] mod 3").unwrap();
    ///
    /// let fmpz_entries = mat.collect_entries();
    /// ```
    pub(crate) fn collect_entries(&self) -> Vec<fmpz> {
        let mut entries: Vec<fmpz> = vec![];

        for row in 0..self.get_num_rows() {
            for col in 0..self.get_num_columns() {
                // efficiently get entry without cloning the entry itself
                let entry = unsafe { *fmpz_mod_mat_entry(&self.matrix, row, col) };
                entries.push(entry);
            }
        }

        entries
    }

    /// Computes the lengths of a given vector of [`Z`] values
    /// considering the [`Modulus`](crate::integer_mod_q::Modulus) of `self`.
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mat = MatZq::from_str("[[1,2],[3,4]] mod 3").unwrap();
    ///
    /// let lengths = mat.collect_lengths();
    /// ```
    pub(crate) fn collect_lengths(&self) -> Vec<Z> {
        let entries_fmpz = self.collect_entries();

        let modulus_fmpz = self.matrix.mod_[0];
        let mut entry_lengths = vec![];
        for value in entries_fmpz {
            entry_lengths.push(length(&value, &modulus_fmpz));
        }

        entry_lengths
    }
}

#[cfg(test)]
mod test_get_entry {
    use super::Zq;
    use crate::{
        error::MathError,
        integer::Z,
        integer_mod_q::MatZq,
        traits::{GetEntry, SetEntry},
    };

    /// Ensure that getting entries works on the edge.
    #[test]
    fn get_edges() {
        let matrix = MatZq::new(5, 10, u64::MAX);

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(4, 9).unwrap();

        assert_eq!(Z::default(), entry1);
        assert_eq!(Z::default(), entry2);
    }

    /// Ensure that getting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatZq::new(5, 10, u64::MAX);
        let value = Z::from(i64::MAX);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from(i64::MAX), entry);
    }

    /// Ensure that getting entries works with large numbers (larger than [`i64`]).
    #[test]
    fn big_positive() {
        let mut matrix = MatZq::new(5, 10, u64::MAX);
        let value = Z::from(u64::MAX - 1);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from(u64::MAX - 1), entry);
    }

    /// Ensure that getting entries works with large numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatZq::new(5, 10, u64::MAX);
        let value = Z::from(-i64::MAX);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from((u64::MAX as i128 - i64::MAX as i128) as u64), entry);
    }

    /// Ensure that getting entries works with large numbers (larger than [`i64`]).
    #[test]
    fn big_negative() {
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
        let matrix = MatZq::new(5, 10, 7);
        let entry1: Result<Zq, MathError> = matrix.get_entry(5, 1);
        let entry2: Result<Zq, MathError> = matrix.get_entry(5, 10);

        assert!(entry1.is_err());
        assert!(entry2.is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatZq::new(5, 10, 7);
        let entry: Result<Zq, MathError> = matrix.get_entry(1, 100);

        assert!(entry.is_err());
    }

    /// Ensure that the entry is a deep copy and not just a clone of the reference.
    #[test]
    fn memory_test() {
        let mut matrix = MatZq::new(5, 10, u64::MAX);
        let value = Zq::from((u64::MAX - 1, u64::MAX));
        matrix.set_entry(1, 1, value).unwrap();
        let entry = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(1, 1, Z::ONE).unwrap();

        assert_eq!(Z::from(u64::MAX - 1), entry);
    }

    /// Ensure that no memory leak occurs in get_entry with ['Z'](crate::integer::Z).
    #[test]
    fn get_entry_z_memory() {
        let mut matrix = MatZq::new(5, 10, u64::MAX);
        matrix.set_entry(1, 1, Z::from(u64::MAX - 3)).unwrap();
        let _: Z = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(2, 2, Z::from(u64::MAX - 10)).unwrap();

        let entry: Z = matrix.get_entry(1, 1).unwrap();
        let _z = Z::from(u64::MAX);

        assert_eq!(entry, Z::from(u64::MAX - 3));
    }

    /// Ensure that no memory leak occurs in get_entry with ['Zq'](crate::integer_mod_q::Zq).
    #[test]
    fn get_entry_zq_memory() {
        let mut matrix = MatZq::new(5, 10, u64::MAX);
        matrix.set_entry(1, 1, Z::from(u64::MAX - 3)).unwrap();
        let _: Zq = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(2, 2, Z::from(u64::MAX - 10)).unwrap();

        let entry: Z = matrix.get_entry(1, 1).unwrap();
        let _z = Z::from(u64::MAX);

        assert_eq!(entry, Z::from(u64::MAX - 3));
    }

    /// Ensure that getting entries works with different types.
    #[test]
    fn diff_types() {
        let matrix = MatZq::new(5, 10, u64::MAX);

        let _: Z = matrix.get_entry(0, 0).unwrap();
        let _: Zq = matrix.get_entry(0, 0).unwrap();
    }
}

#[cfg(test)]
mod test_get_num {
    use crate::{
        integer_mod_q::MatZq,
        traits::{GetNumColumns, GetNumRows},
    };

    /// Ensure that the getter for number of rows works correctly.
    #[test]
    fn num_rows() {
        let matrix = MatZq::new(5, 10, 7);

        assert_eq!(matrix.get_num_rows(), 5);
    }

    /// Ensure that the getter for number of columns works correctly.
    #[test]
    fn num_columns() {
        let matrix = MatZq::new(5, 10, 7);

        assert_eq!(matrix.get_num_columns(), 10);
    }
}

#[cfg(test)]
mod test_mod {
    use crate::integer_mod_q::{MatZq, Modulus};

    /// Ensure that the getter for modulus works correctly.
    #[test]
    fn get_mod() {
        let matrix = MatZq::new(5, 10, 7);

        assert_eq!(matrix.get_mod(), Modulus::from(7));
    }

    /// Ensure that the getter for modulus works with large numbers.
    #[test]
    fn get_mod_large() {
        let matrix = MatZq::new(5, 10, u64::MAX);

        assert_eq!(matrix.get_mod(), Modulus::from(u64::MAX));
    }

    /// Ensure that no memory leak occurs in get_mod.
    #[test]
    fn get_mod_memory() {
        let matrix = MatZq::new(5, 10, u64::MAX);
        let _ = matrix.get_mod();
        let _ = Modulus::from(u64::MAX - 1);

        let modulus = matrix.get_mod();

        assert_eq!(modulus, Modulus::from(u64::MAX));
    }
}

#[cfg(test)]
mod test_get_vec {
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Ensure that getting a row works
    #[test]
    fn get_row_works() {
        let matrix = MatZq::from_str(&format!(
            "[[0,0,0],[4,{},{}]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let row1 = matrix.get_row(0).unwrap();
        let row2 = matrix.get_row(1).unwrap();

        let cmp1 = MatZq::from_str(&format!("[[0,0,0]] mod {}", u64::MAX)).unwrap();
        let cmp2 =
            MatZq::from_str(&format!("[[4,{},{}]] mod {}", i64::MAX, i64::MIN, u64::MAX)).unwrap();

        assert_eq!(cmp1, row1);
        assert_eq!(cmp2, row2);
    }

    /// Ensure that getting a column works
    #[test]
    fn get_column_works() {
        let matrix = MatZq::from_str(&format!(
            "[[1,0,3],[{},0,5],[{},0,7]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let column1 = matrix.get_column(0).unwrap();
        let column2 = matrix.get_column(1).unwrap();
        let column3 = matrix.get_column(2).unwrap();

        let cmp1 = MatZq::from_str(&format!(
            "[[1],[{}],[{}]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let cmp2 = MatZq::from_str(&format!("[[0],[0],[0]] mod {}", u64::MAX)).unwrap();
        let cmp3 = MatZq::from_str(&format!("[[3],[5],[7]] mod {}", u64::MAX)).unwrap();

        assert_eq!(cmp1, column1);
        assert_eq!(cmp2, column2);
        assert_eq!(cmp3, column3);
    }

    /// Ensure that wrong row and column dimensions yields an error
    #[test]
    fn wrong_dim_error() {
        let matrix = MatZq::from_str(&format!(
            "[[1,2,3],[{},4,5],[{},6,7]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
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
    use super::MatZq;
    use std::str::FromStr;

    #[test]
    fn all_entries_collected() {
        let mat_1 = MatZq::from_str(&format!(
            "[[1,2],[{},{}],[3,4]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatZq::from_str("[[-1,2]] mod 2").unwrap();

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
        assert_eq!(entries_2[0].0, 1);
        assert_eq!(entries_2[1].0, 0);
    }
}

#[cfg(test)]
mod test_collect_lengths {
    use super::{MatZq, Z};
    use std::str::FromStr;

    #[test]
    fn lengths_correctly_computed() {
        let mat_1 = MatZq::from_str(&format!(
            "[[1,2],[{},{}],[3,4]] mod {}",
            i64::MAX - 2,
            i64::MIN,
            i64::MAX - 1
        ))
        .unwrap();
        let mat_2 = MatZq::from_str("[[-1,2]] mod 2").unwrap();

        let lengths_1 = mat_1.collect_lengths();
        let lengths_2 = mat_2.collect_lengths();

        assert_eq!(lengths_1.len(), 6);
        assert_eq!(lengths_1[0], Z::ONE);
        assert_eq!(lengths_1[1], Z::from(2));
        assert_eq!(lengths_1[2], Z::ONE);
        assert_eq!(lengths_1[3], Z::from(2));
        assert_eq!(lengths_1[4], Z::from(3));
        assert_eq!(lengths_1[5], Z::from(4));

        assert_eq!(lengths_2.len(), 2);
        assert_eq!(lengths_2[0], Z::ONE);
        assert_eq!(lengths_2[1], Z::ZERO);
    }
}
