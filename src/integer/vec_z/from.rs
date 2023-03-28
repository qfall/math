// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`VecZ`](crate::integer::VecZ) vector from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::{MatZ, VecZ};
use crate::error::MathError;
use crate::traits::{GetNumColumns, GetNumRows};
use crate::utils::VectorDirection;
use std::{fmt::Display, str::FromStr};

impl VecZ {
    /// Creates a new vector with `num_entries` entries and
    /// zeros as entries.
    ///
    /// Parameters:
    /// - `num_entries`: number of rows or columns the new vector should have.
    /// - `orientation`: defines the orientation the vector should have.
    /// [`VectorDirection::ColumnVector`] and [`VectorDirection::RowVector`]
    /// are valid inputs.
    ///
    /// Returns a [`VecZ`] or an error, if the number of entries is
    /// less or equal to `0`.
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    /// use math::utils::VectorDirection;
    ///
    /// let vector = VecZ::new(5, VectorDirection::ColumnVector).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the number of rows/columns is `0`.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows/columns is negative or it does not fit into an [`i64`].
    pub fn new(
        num_entries: impl TryInto<i64> + Display + Copy,
        orientation: VectorDirection,
    ) -> Result<Self, MathError> {
        match orientation {
            VectorDirection::RowVector => Ok(VecZ {
                vector: MatZ::new(1, num_entries)?,
            }),
            VectorDirection::ColumnVector => Ok(VecZ {
                vector: MatZ::new(num_entries, 1)?,
            }),
        }
    }
}

impl FromStr for VecZ {
    type Err = MathError;

    /// Creates a [`VecZ`] vector with entries in [`Z`] from a [`String`].
    /// The format of that string looks like this `[[1],[2],[3]]` for a column vector
    /// with three entries (`1` in the first row, `2` in the second one, ...).
    /// `[[1,2,3]]` is the correct format for a row vector.
    ///
    /// Parameters:
    /// - `string`: the vector representation as a string
    ///
    /// Returns a [`VecZ`] or an error, if the vector is not formatted in a suitable way,
    /// the number of entries is too big (must fit into [`i64`]), or if the regular expression
    /// inside of the function could not be processed.
    ///
    /// # Examples
    /// Column Vector
    /// ```
    /// use math::integer::VecZ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1],[2],[3]]");
    /// let vector = VecZ::from_str(&string).unwrap();
    /// ```
    /// Row Vector
    /// ```
    /// use math::integer::VecZ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1,2,3]]");
    /// let vector = VecZ::from_str(&string).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the vector is not formatted in a suitable way,
    /// the number of rows/columns is too big (must fit into [`i64`]).
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if an entry contains a Nul byte.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToVectorInput`](MathError::InvalidStringToVectorInput)
    /// if no dimension or the matrix is `1`.
    /// [`InvalidStringToZInput`](MathError::InvalidStringToZInput)
    /// if an entry is not formatted correctly.
    fn from_str(string: &str) -> Result<Self, MathError> {
        let matrix = MatZ::from_str(string)?;

        if matrix.get_num_rows() == 1 || matrix.get_num_columns() == 1 {
            Ok(VecZ { vector: matrix })
        } else {
            Err(MathError::InvalidStringToVectorInput(String::from(
                "The string either contained more than one column and row, or included zero entries",
            )))
        }
    }
}

#[cfg(test)]
mod test_new {

    use crate::integer::{VecZ, Z};
    use crate::utils::VectorDirection;

    /// Ensure that entries of a new vector are `0`.
    #[test]
    fn entry_zero() {
        let matrix = VecZ::new(2, VectorDirection::ColumnVector).unwrap();

        let entry1 = matrix.get_entry(0).unwrap();
        let entry2 = matrix.get_entry(0).unwrap();

        assert_eq!(Z::ZERO, entry1);
        assert_eq!(Z::ZERO, entry2);
    }

    /// Ensure that a new zero vector fails with `0` or a negative value as input.
    #[test]
    fn error_zero_negative() {
        let matrix1 = VecZ::new(0, VectorDirection::ColumnVector);
        let matrix2 = VecZ::new(-1, VectorDirection::ColumnVector);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
    }
}

#[cfg(test)]
mod test_from_str {

    use crate::integer::{VecZ, Z};
    use crate::utils::VectorDirection;
    use std::str::FromStr;

    /// Ensure that initialization works in both directions
    #[test]
    fn directions() {
        let row = VecZ::from_str("[[1, 2, 3]]").unwrap();
        let col = VecZ::from_str("[[1],[2],[3]]").unwrap();

        assert_eq!(Z::ONE, row.get_entry(0).unwrap());
        assert!(row.is_row_vector());
        assert_eq!(VectorDirection::RowVector, row.get_direction());

        assert_eq!(Z::ONE, col.get_entry(0).unwrap());
        assert!(col.is_column_vector());
        assert_eq!(VectorDirection::ColumnVector, col.get_direction());
    }

    /// Ensure that initialization with positive numbers that are larger than [`i64`] works.
    #[test]
    fn large_numbers() {
        let vector_string = format!("[[{}, 2, 3]]", u64::MAX);

        assert_eq!(
            Z::from(u64::MAX),
            VecZ::from_str(&vector_string)
                .unwrap()
                .get_entry(0)
                .unwrap()
        );
    }

    /// Ensure that initialization with negative numbers that are larger than [`i64`] works.
    #[test]
    fn small_numbers() {
        let vector_string = format!("[[{}, 2, 3]]", i64::MIN);

        assert_eq!(
            Z::from(i64::MIN),
            VecZ::from_str(&vector_string)
                .unwrap()
                .get_entry(0)
                .unwrap()
        );
    }

    /// Ensure that entries can have leading and trailing whitespaces.
    #[test]
    fn whitespaces_in_entries_works() {
        let vector_string = String::from("[[  1],[2 ],[  3  ]]");

        assert_eq!(
            Z::ONE,
            VecZ::from_str(&vector_string)
                .unwrap()
                .get_entry(0)
                .unwrap()
        );
    }

    /// Ensure that entries are set correctly for a row vector
    #[test]
    fn entries_set_correctly_row() {
        let vector_string = format!("[[0,{},{}, -10, 10]]", i64::MIN, i64::MAX);

        let vector = VecZ::from_str(&vector_string).unwrap();

        assert_eq!(vector.get_entry(0).unwrap(), 0.into());
        assert_eq!(vector.get_entry(1).unwrap(), i64::MIN.into());
        assert_eq!(vector.get_entry(2).unwrap(), i64::MAX.into());
        assert_eq!(vector.get_entry(3).unwrap(), (-10).into());
        assert_eq!(vector.get_entry(4).unwrap(), 10.into());
    }

    /// Ensure that entries are set correctly for a column vector
    #[test]
    fn entries_set_correctly_col() {
        let vector_string = format!("[[0],[{}],[{}],[-10],[10]]", i64::MIN, i64::MAX);

        let vector = VecZ::from_str(&vector_string).unwrap();

        assert_eq!(vector.get_entry(0).unwrap(), 0.into());
        assert_eq!(vector.get_entry(1).unwrap(), i64::MIN.into());
        assert_eq!(vector.get_entry(2).unwrap(), i64::MAX.into());
        assert_eq!(vector.get_entry(3).unwrap(), (-10).into());
        assert_eq!(vector.get_entry(4).unwrap(), 10.into());
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let vector_string1 = String::from("[1, 2, 3],");
        let vector_string2 = String::from("[1, 2, 3]]");
        let vector_string3 = String::from("[[1, 2, 3],3, 4, 5]");
        let vector_string4 = String::from("[1, 2, 3, 4,, 5]");
        let vector_string5 = String::from("[[1, 2, 3],[3, 4, 5]]");
        let vector_string6 = String::from("[[1, 2, 38,]");
        let vector_string7 = String::from("");
        let vector_string8 = String::from("[]");
        let vector_string9 = String::from("[[]]");

        assert!(VecZ::from_str(&vector_string1).is_err());
        assert!(VecZ::from_str(&vector_string2).is_err());
        assert!(VecZ::from_str(&vector_string3).is_err());
        assert!(VecZ::from_str(&vector_string4).is_err());
        assert!(VecZ::from_str(&vector_string5).is_err());
        assert!(VecZ::from_str(&vector_string6).is_err());
        assert!(VecZ::from_str(&vector_string7).is_err());
        assert!(VecZ::from_str(&vector_string8).is_err());
        assert!(VecZ::from_str(&vector_string9).is_err());
    }
}
