// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation to set entries from a [`VecZ`] vector.

use super::VecZ;
use crate::{error::MathError, integer::Z};
use std::fmt::Display;

impl VecZ {
    /// Sets the value of a specific vector entry according to a given `value` of type [`Z`](crate::integer::Z).
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    /// use math::integer::Z;
    ///
    /// let mut vector = VecZ::new(5).unwrap();
    /// let value = Z::from_i64(5);
    /// vector.set_entry(1, value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the given row is greater than the matrix or negative.
    pub fn set_entry<S: TryInto<i64> + Display + Copy, T: Into<Z>>(
        &mut self,
        row: S,
        value: T,
    ) -> Result<(), MathError> {
        self.set_entry_ref_z(row, &value.into())
    }

    /// Sets the value of a specific matrix entry according to a given `value` of type [`Z`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    /// use math::integer::Z;
    ///
    /// let mut vector = VecZ::new(5).unwrap();
    /// let value = Z::from_i64(5);
    /// vector.set_entry_ref_z(1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the given row is greater than the matrix or negative.
    pub fn set_entry_ref_z<S: TryInto<i64> + Display + Copy>(
        &mut self,
        row: S,
        value: &Z,
    ) -> Result<(), MathError> {
        self.matrix.set_entry_ref_z(row, 0, value)?;
        Ok(())
    }
}

#[cfg(test)]
mod test_setter {
    use super::Z;
    use crate::integer::VecZ;

    /// Ensure that setting the correct entries works fine
    #[test]
    fn correct_entry_set() {
        let mut vector = VecZ::new(5).unwrap();
        vector.set_entry(4, 869).unwrap();

        let entry = vector.get_entry(4).unwrap();

        assert_eq!(entry, Z::from_i64(869));
    }

    /// Ensure that a wrong given row returns a [`MathError`](crate::error::MathError)
    #[test]
    fn error_wrong_row() {
        let mut vector = VecZ::new(5).unwrap();
        let value = Z::from_i64(i64::MAX);

        assert!(vector.set_entry_ref_z(5, &value).is_err());
        assert!(vector.set_entry_ref_z(-1, &value).is_err());
    }
}
