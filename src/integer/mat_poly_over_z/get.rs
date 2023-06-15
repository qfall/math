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
    fmpz_poly_mat::fmpz_poly_mat_entry,
};
use std::fmt::Display;

impl GetNumRows for MatPolyOverZ {
    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatPolyOverZ::new(5,6);
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
    /// let matrix = MatPolyOverZ::new(5,6);
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
    /// Returns the [`PolyOverZ`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatPolyOverZ::new(5, 10);
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
    /// row or an error, if the number of rows is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  1, 0],[1  3, 1  4],[0,1  6]]").unwrap();
    ///
    /// let row0 = matrix.get_row(0).unwrap(); // first row
    /// let row1 = matrix.get_row(1).unwrap(); // second row
    /// let row2 = matrix.get_row(2).unwrap(); // third row
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

        let out = MatPolyOverZ::new(1, self.get_num_columns());
        for column in 0..self.get_num_columns() {
            unsafe {
                fmpz_poly_set(
                    fmpz_poly_mat_entry(&out.matrix, 0, column),
                    fmpz_poly_mat_entry(&self.matrix, row_i64, column),
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
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  1, 0],[1  3, 1  4],[0,1  6]]").unwrap();
    ///
    /// let col0 = matrix.get_column(0).unwrap(); // first column
    /// let col1 = matrix.get_column(1).unwrap(); // second column
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

        let out = MatPolyOverZ::new(self.get_num_rows(), 1);
        for row in 0..self.get_num_rows() {
            unsafe {
                fmpz_poly_set(
                    fmpz_poly_mat_entry(&out.matrix, row, 0),
                    fmpz_poly_mat_entry(&self.matrix, row, column_i64),
                )
            };
        }
        Ok(out)
    }

    #[allow(dead_code)]
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
    /// let mat = MatPolyOverZ::from_str("[[1  1, 0],[1  3, 1  4],[0,1  6]]").unwrap();
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
    fn big_positive() {
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
    fn big_negative() {
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

    /// Ensure that getting entries at (0,0) works.
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
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatPolyOverZ::new(5, 10);

        assert!(matrix.get_entry(1, 100).is_err());
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
            "[[0,0,0],[1  42,1  {},1  {}]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let row1 = matrix.get_row(0).unwrap();
        let row2 = matrix.get_row(1).unwrap();

        let cmp1 = MatPolyOverZ::from_str("[[0,0,0]]").unwrap();
        let cmp2 =
            MatPolyOverZ::from_str(&format!("[[1  42,1  {},1  {}]]", i64::MAX, i64::MIN)).unwrap();

        assert_eq!(cmp1, row1);
        assert_eq!(cmp2, row2);
    }

    /// Ensure that getting a column works
    #[test]
    fn get_column_works() {
        let matrix = MatPolyOverZ::from_str(&format!(
            "[[1  42,0,2  17 42],[1  {},0,2  17 42],[1  {},0,2  17 42]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let column1 = matrix.get_column(0).unwrap();
        let column2 = matrix.get_column(1).unwrap();
        let column3 = matrix.get_column(2).unwrap();

        let cmp1 =
            MatPolyOverZ::from_str(&format!("[[1  42],[1  {}],[1  {}]]", i64::MAX, i64::MIN))
                .unwrap();
        let cmp2 = MatPolyOverZ::from_str("[[0],[0],[0]]").unwrap();
        let cmp3 = MatPolyOverZ::from_str("[[2  17 42],[2  17 42],[2  17 42]]").unwrap();

        assert_eq!(cmp1, column1);
        assert_eq!(cmp2, column2);
        assert_eq!(cmp3, column3);
    }

    /// Ensure that wrong row and column dimensions yields an error
    #[test]
    fn wrong_dim_error() {
        let matrix = MatPolyOverZ::from_str(&format!(
            "[[1  17,2  17 42,3  1 1 1],[1  {},1  1,2  2 3],[1  {},1  142,1  1]]",
            i64::MAX,
            i64::MIN
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
    use super::MatPolyOverZ;
    use std::str::FromStr;

    #[test]
    fn all_entries_collected() {
        let mat_1 = MatPolyOverZ::from_str(&format!(
            "[[1  1,0],[1  {},1  {}],[1  -3, 0]]",
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
