// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get entries from a [`MatPolyOverZ`] matrix.

use super::MatPolyOverZ;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    traits::{GetEntry, GetNumColumns, GetNumRows},
    utils::coordinate::evaluate_coordinates,
};
use flint_sys::{fmpz_poly::fmpz_poly_set, fmpz_poly_mat::fmpz_poly_mat_entry};
use std::fmt::Display;

impl GetNumRows for MatPolyOverZ {
    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Example
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use math::traits::GetNumRows;
    ///
    /// let matrix = MatPolyOverZ::new(5,6).unwrap();
    /// let rows = matrix.get_num_rows();
    /// ```
    fn get_num_rows(&self) -> i64 {
        self.matrix.r
    }
}

impl GetNumColumns for MatPolyOverZ {
    /// Returns the number of columns of the matrix as a [`i64`].
    ///
    /// # Example
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use math::traits::GetNumColumns;
    ///
    /// let matrix = MatPolyOverZ::new(5,6).unwrap();
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
    /// # Example
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use math::traits::GetEntry;
    ///
    /// let matrix = MatPolyOverZ::new(5, 10).unwrap();
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
    ) -> Result<PolyOverZ, MathError> {
        let (row_i64, column_i64) = evaluate_coordinates(self, row, column)?;

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

#[cfg(test)]
mod test_get_entry {

    use crate::{
        integer::{MatPolyOverZ, PolyOverZ},
        traits::GetEntry,
    };
    use std::str::FromStr;

    /// Ensure that getting entries works with large polynomials.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MAX)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(format!("2  {} 1", i64::MAX), entry.to_string());
    }

    /// Ensure that getting entries works with large polynomials (larger than [`i64`]).
    #[test]
    fn big_positive() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry.to_string());
    }

    /// Ensure that getting entries works with large negative polynomials.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MIN)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(format!("2  {} 1", i64::MIN), entry.to_string());
    }

    /// Ensure that getting entries works with large negative polynomials (larger than [`i64`]).
    #[test]
    fn big_negative() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  -{} 1", u64::MAX)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(format!("2  -{} 1", u64::MAX), entry.to_string());
    }

    /// Ensure that polynomials with many entries are correctly retrieved
    #[test]
    fn large_poly() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
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
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MAX)).unwrap();
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(format!("2  {} 1", i64::MAX), entry.to_string());
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let matrix = MatPolyOverZ::new(5, 10).unwrap();

        assert!(matrix.get_entry(5, 1).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatPolyOverZ::new(5, 10).unwrap();

        assert!(matrix.get_entry(1, 100).is_err());
    }

    /// Ensure that the entry is a deep copy and not just a clone of the reference.
    #[test]
    fn memory_test() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
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

    /// Ensure that the getter for rows works correctly.
    #[test]
    fn num_rows() {
        let matrix = MatPolyOverZ::new(5, 10).unwrap();

        assert_eq!(matrix.get_num_rows(), 5);
    }

    /// Ensure that the getter for columns works correctly.
    #[test]
    fn num_columns() {
        let matrix = MatPolyOverZ::new(5, 10).unwrap();

        assert_eq!(matrix.get_num_columns(), 10);
    }
}
