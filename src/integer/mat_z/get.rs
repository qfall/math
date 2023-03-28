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
    utils::coordinate::evaluate_coordinates,
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
    /// use math::integer::MatZ;
    /// use math::traits::GetNumRows;
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
    /// use math::integer::MatZ;
    /// use math::traits::GetNumColumns;
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
    /// use math::integer::MatZ;
    /// use crate::math::traits::GetEntry;
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
        let (row_i64, column_i64) = evaluate_coordinates(self, row, column)?;

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

#[cfg(test)]
mod test_get_entry {

    use super::Z;
    use crate::{integer::MatZ, traits::GetEntry};
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
        let value = Z::from_str(&"1".repeat(65)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from_str(&"1".repeat(65)).unwrap(), entry);
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
        let mut value = "-".to_string();
        value.push_str(&"1".repeat(65));
        matrix
            .set_entry(1, 1, Z::from_str(&value).unwrap())
            .unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        let mut test_entry = "-".to_string();
        test_entry.push_str(&"1".repeat(65));

        assert_eq!(Z::from_str(&test_entry).unwrap(), entry);
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
        let value = Z::from_str(&"1".repeat(65)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();
        let entry = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(1, 1, Z::from_i64(0)).unwrap();

        assert_eq!(Z::from_str(&"1".repeat(65)).unwrap(), entry);
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
