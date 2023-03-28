// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get entries from a [`VecZ`] matrix.

use super::VecZ;
use crate::{
    error::MathError,
    integer::Z,
    traits::{GetEntry, GetNumColumns, GetNumRows},
    utils::VectorDirection,
};
use std::fmt::Display;

impl VecZ {
    /// Outputs the [`Z`] value of a specific vector entry.
    ///
    /// Parameters:
    /// - `entry`: specifies the entry in which the entry is located
    ///
    /// Returns the [`Z`] value of the vector at the position of the given
    /// entry or an error, if the given entry is greater than the vector or negative.
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    /// use math::utils::VectorDirection;
    ///
    /// let matrix = VecZ::new(5, VectorDirection::ColumnVector).unwrap();
    /// let entry = matrix.get_entry(1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the given entry is outside the vector or negative.
    pub fn get_entry(&self, entry: impl TryInto<i64> + Display + Copy) -> Result<Z, MathError> {
        if self.is_column_vector() {
            self.vector.get_entry(entry, 0)
        } else {
            self.vector.get_entry(0, entry)
        }
    }

    /// Returns `true` if the vector has only one row.
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    /// use std::str::FromStr;
    ///
    /// let row = VecZ::from_str("[[1,2,3]]").unwrap();
    ///
    /// assert!(row.is_row_vector());
    /// ```
    pub fn is_row_vector(&self) -> bool {
        self.vector.get_num_rows() == 1
    }

    /// Returns `true` if the vector has only one column.
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    /// use std::str::FromStr;
    ///
    /// let col = VecZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// assert!(col.is_column_vector());
    /// ```
    pub fn is_column_vector(&self) -> bool {
        self.vector.get_num_columns() == 1
    }

    /// Returns [`VectorDirection::RowVector`] if the vector has only one row.
    /// Otherwise, returns [`VectorDirection::ColumnVector`].
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    /// use std::str::FromStr;
    /// use math::utils::VectorDirection;
    ///
    /// let row = VecZ::from_str("[[1,2,3]]").unwrap();
    /// let col = VecZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// assert_eq!(VectorDirection::RowVector, row.get_direction());
    /// assert_eq!(VectorDirection::ColumnVector, col.get_direction());
    /// ```
    pub fn get_direction(&self) -> VectorDirection {
        if self.is_row_vector() {
            VectorDirection::RowVector
        } else {
            VectorDirection::ColumnVector
        }
    }
}

#[cfg(test)]
mod test_get_entry {

    use super::VecZ;
    use super::Z;
    use crate::utils::VectorDirection;
    use std::str::FromStr;

    /// Ensure that getting the correct entries works fine for row vectors
    #[test]
    fn correct_entry_fetched_row() {
        let vector =
            VecZ::from_str(&format!("[[0, 10, -10, {}, {}]]", i64::MAX, i64::MIN)).unwrap();
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

    /// Ensure that getting the correct entries works fine for column vectors
    #[test]
    fn correct_entry_fetched_col() {
        let vector =
            VecZ::from_str(&format!("[[0],[10],[-10],[{}],[{}]]", i64::MAX, i64::MIN)).unwrap();
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
        let vector = VecZ::new(5, VectorDirection::ColumnVector).unwrap();

        assert!(vector.get_entry(5).is_err());
        assert!(vector.get_entry(-1).is_err());
    }
}

#[cfg(test)]
mod test_directions {

    use super::VecZ;
    use crate::utils::VectorDirection;

    /// Check whether a row vector is correctly detected
    #[test]
    fn row_detected() {
        let vec = VecZ::new(5, VectorDirection::RowVector).unwrap();

        assert!(vec.is_row_vector());
        assert!(!vec.is_column_vector());
        assert_eq!(vec.get_direction(), VectorDirection::RowVector);
    }

    /// Check whether a column vector is correctly detected
    #[test]
    fn column_detected() {
        let vec = VecZ::new(5, VectorDirection::ColumnVector).unwrap();

        assert!(!vec.is_row_vector());
        assert!(vec.is_column_vector());
        assert_eq!(vec.get_direction(), VectorDirection::ColumnVector);
    }

    /// Check whether a 1x1 vector is neither of both
    #[test]
    fn one_by_one_detection() {
        let vec = VecZ::new(1, VectorDirection::ColumnVector).unwrap();

        assert!(vec.is_row_vector());
        assert!(vec.is_column_vector());
        assert_eq!(vec.get_direction(), VectorDirection::RowVector);
        // returns RowVector as standard as this answer is not wrong for a one times one matrix
    }
}
