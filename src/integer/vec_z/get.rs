// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get entries from a [`VecZ`] matrix.

use super::VecZ;
use crate::{error::MathError, integer::Z, traits::GetEntry};
use std::fmt::Display;

impl VecZ {
    /// Outputs the [`Z`] value of a specific vector entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    ///
    /// Returns the [`Z`] value of the vector at the position of the given
    /// row or an error, if the given row is greater than the vector or negative.
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    ///
    /// let matrix = VecZ::new(5).unwrap();
    /// let entry = matrix.get_entry(1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the given row is greater than the matrix or negative.
    pub fn get_entry(&self, row: impl TryInto<i64> + Display + Copy) -> Result<Z, MathError> {
        self.matrix.get_entry(row, 0)
    }
}

#[cfg(test)]
mod test_get_entry {

    use super::VecZ;
    use super::Z;
    use std::str::FromStr;

    /// Ensure that getting the correct entries works fine
    #[test]
    fn correct_entry_fetched() {
        let vector = VecZ::from_str(&format!("[0, 10, -10, {}, {}]", i64::MAX, i64::MIN)).unwrap();
        let zero: Z = 0.into();
        let ten: Z = 10.into();
        let minus_ten: Z = (-10).into();
        let max: Z = i64::MAX.into();
        let min: Z = i64::MIN.into();

        assert_eq!(zero, vector.get_entry(0).unwrap());
        assert_eq!(ten, vector.get_entry(1).unwrap());
        assert_eq!(minus_ten, vector.get_entry(2).unwrap());
        assert_eq!(max, vector.get_entry(3).unwrap());
        assert_eq!(min, vector.get_entry(4).unwrap());
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_out_bounds() {
        let matrix = VecZ::new(5).unwrap();

        assert!(matrix.get_entry(5).is_err());
        assert!(matrix.get_entry(-1).is_err());
    }
}
