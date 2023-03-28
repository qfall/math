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
    /// - `entry`: specifies the entry in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```
    /// use math::integer::{VecZ, Z};
    /// use math::utils::VectorDirection;
    ///
    /// let mut vector = VecZ::new(5, VectorDirection::ColumnVector).unwrap();
    /// let value = Z::from_i64(5);
    /// vector.set_entry(1, value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the given entry outside the vector or negative.
    pub fn set_entry<S: TryInto<i64> + Display + Copy, T: Into<Z>>(
        &mut self,
        entry: S,
        value: T,
    ) -> Result<(), MathError> {
        self.set_entry_ref_z(entry, &value.into())
    }

    /// Sets the value of a specific matrix entry according to a given `value` of type [`Z`].
    ///
    /// Parameters:
    /// - `entry`: specifies the entry in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```
    /// use math::integer::{VecZ, Z};
    /// use math::utils::VectorDirection;
    ///
    /// let mut vector = VecZ::new(5, VectorDirection::ColumnVector).unwrap();
    /// let value = Z::from_i64(5);
    /// vector.set_entry_ref_z(1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the given entry outside the vector or negative.
    pub fn set_entry_ref_z<S: TryInto<i64> + Display + Copy>(
        &mut self,
        entry: S,
        value: &Z,
    ) -> Result<(), MathError> {
        if self.is_column_vector() {
            self.vector.set_entry_ref_z(entry, 0, value)?;
        } else {
            self.vector.set_entry_ref_z(0, entry, value)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test_setter {
    use super::Z;
    use crate::integer::VecZ;
    use crate::utils::VectorDirection;

    /// Ensure that setting the correct entries works fine
    #[test]
    fn correct_entry_set() {
        let mut col = VecZ::new(5, VectorDirection::ColumnVector).unwrap();
        let mut row = VecZ::new(5, VectorDirection::RowVector).unwrap();

        col.set_entry(4, 869).unwrap();
        row.set_entry(3, 869).unwrap();

        assert_eq!(col.get_entry(4).unwrap(), Z::from_i64(869));
        assert_eq!(row.get_entry(3).unwrap(), Z::from_i64(869));
    }

    /// Ensure that a wrong given row returns a [`MathError`](crate::error::MathError)
    #[test]
    fn error_wrong_row() {
        let mut col = VecZ::new(5, VectorDirection::ColumnVector).unwrap();
        let mut row = VecZ::new(5, VectorDirection::RowVector).unwrap();
        let value = Z::from_i64(i64::MAX);

        assert!(col.set_entry_ref_z(5, &value).is_err());
        assert!(col.set_entry_ref_z(-1, &value).is_err());
        assert!(row.set_entry_ref_z(5, &value).is_err());
        assert!(row.set_entry_ref_z(-1, &value).is_err());
    }
}
