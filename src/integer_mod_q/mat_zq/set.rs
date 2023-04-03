// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation to set entries from a [`MatZq`] matrix.

use super::MatZq;
use crate::error::MathError;
use crate::integer::Z;
use crate::integer_mod_q::Zq;
use crate::macros::for_others::{implement_for_others, implement_for_owned};
use crate::traits::SetEntry;
use crate::utils::coordinate::evaluate_coordinates;
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_set_entry;
use std::fmt::Display;

impl SetEntry<&Z> for MatZq {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`Z`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
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
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
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
    /// # Example
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
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
        value: &Zq,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_coordinates(self, row, column)?;

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
