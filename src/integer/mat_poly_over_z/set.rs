// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation to set entries from a [`MatPolyOverZ`] matrix.

use super::MatPolyOverZ;
use crate::{
    error::MathError, integer::PolyOverZ, traits::SetEntry, utils::coordinate::evaluate_coordinates,
};
use flint_sys::fmpz_poly::fmpz_poly_swap;
use flint_sys::{fmpz_poly::fmpz_poly_set, fmpz_poly_mat::fmpz_poly_mat_entry};
use std::fmt::Display;

impl SetEntry<&PolyOverZ> for MatPolyOverZ {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use math::integer::PolyOverZ;
    /// use math::traits::*;
    ///
    /// let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
    /// let value = PolyOverZ::default();
    /// matrix.set_entry(1, 1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
        value: &PolyOverZ,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_coordinates(self, row, column)?;

        // since `self` is a correct matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpz_set` can successfully clone the
        // value inside the matrix. Therefore no memory leaks can appear.
        unsafe {
            let entry = fmpz_poly_mat_entry(&self.matrix, row_i64, column_i64);
            fmpz_poly_set(entry, &value.poly)
        };

        Ok(())
    }
}

impl SetEntry<PolyOverZ> for MatPolyOverZ {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use math::integer::PolyOverZ;
    /// use math::traits::*;
    ///
    /// let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
    /// let value = PolyOverZ::default();
    /// matrix.set_entry(1, 1, value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
        mut value: PolyOverZ,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_coordinates(self, row, column)?;

        // swapping the content of the entry with the given value since ownership
        // of the input is provided.
        unsafe {
            let entry = fmpz_poly_mat_entry(&self.matrix, row_i64, column_i64);
            fmpz_poly_swap(entry, &mut value.poly)
        }
        Ok(())
    }
}

#[cfg(test)]
mod test_setter {
    use crate::{
        integer::{MatPolyOverZ, PolyOverZ},
        traits::{GetEntry, SetEntry},
    };
    use std::str::FromStr;

    /// Ensure that setting entries works with standard numbers.
    #[test]
    fn standard_value() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", 889)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", 889), entry.to_string());
    }

    /// Ensure that setting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MAX)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", i64::MAX), entry.to_string());
    }

    /// Ensure that setting entries works with large numbers (larger than i64).
    #[test]
    fn big_positive() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry.to_string());
    }

    /// Ensure that setting entries works with referenced large numbers (larger than i64).
    #[test]
    fn big_positive_ref() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value1 = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        let value2 = PolyOverZ::from_str(&format!("2  {} 1", 8)).unwrap();
        matrix.set_entry(1, 1, &value1).unwrap();
        matrix.set_entry(0, 0, value2).unwrap();

        let entry1 = matrix.get_entry(1, 1).unwrap();
        let entry2 = matrix.get_entry(0, 0).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry1.to_string());
        assert_eq!(format!("2  {} 1", 8), entry2.to_string());
    }

    /// Ensure that setting entries works with large negative numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", i64::MIN)).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(format!("2  {} 1", i64::MIN), entry.to_string());
    }

    /// Ensure that setting entries works with large negative numbers (larger than i64).
    #[test]
    fn big_negative() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value_str = &format!("2  -{} 1", u64::MAX);
        let value = PolyOverZ::from_str(value_str).unwrap();
        matrix.set_entry(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(PolyOverZ::from_str(value_str).unwrap(), entry);
    }

    /// Ensure that setting entries at (0,0) works.
    #[test]
    fn setting_at_zero() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();
        matrix.set_entry(0, 0, &value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(format!("2  {} 1", u64::MAX), entry.to_string());
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::default();

        assert!(matrix.set_entry(5, 1, value).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let mut matrix = MatPolyOverZ::new(5, 10).unwrap();
        let value = PolyOverZ::default();

        assert!(matrix.set_entry(1, 100, value).is_err());
    }
}
