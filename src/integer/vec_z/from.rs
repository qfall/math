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
use crate::integer::Z;
use crate::utils::parse::parse_vector_string;
use std::{fmt::Display, str::FromStr};

impl VecZ {
    /// Creates a new row-vector with `num_rows` rows and
    /// zeros as entries.
    ///
    /// Parameters:
    /// - `num_rows`: number of columns the new vector should have
    ///
    /// Returns a [`VecZ`] or an error, if the number of rows is
    /// less or equal to `0`.
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    ///
    /// let vector = VecZ::new(5).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the number of rows is `0`.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows is negative or it does not fit into an [`i64`].
    pub fn new(num_rows: impl TryInto<i64> + Display + Copy) -> Result<Self, MathError> {
        Ok(VecZ {
            matrix: MatZ::new(num_rows, 1)?,
        })
    }
}

impl FromStr for VecZ {
    type Err = MathError;

    /// Creates a [`VecZ`] row-vector with entries in [`Z`] from a [`String`].
    /// The format of that string looks like this `[1,2,3]` for a row vector
    /// with three entries (`1` in the first row, `2` in the second one, ...)
    ///
    /// Parameters:
    /// - `string`: the vector representation as a string
    ///
    /// Returns a [`VecZ`] or an error, if the vector is not formatted in a suitable way,
    /// the number of rows is too big (must fit into [`i64`]), or if the regular expression
    /// inside of the function could not be processed.
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[1, 2, 3]");
    /// let matrix = VecZ::from_str(&string).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the vector is not formatted in a suitable way,
    /// the number of rows is too big (must fit into [`i64`]).
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if an entry contains a Nul byte.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToZInput`](MathError::InvalidStringToZInput)
    /// if an entry is not formatted correctly.
    fn from_str(string: &str) -> Result<Self, MathError> {
        let entries = parse_vector_string(string)?;
        let num_rows = entries.len();
        let mut vector = VecZ::new(num_rows)?;

        // fill entries of matrix according to entries in string_matrix
        for (row_num, entry) in entries.iter().enumerate() {
            let z_entry = Z::from_str(entry)?;
            vector.set_entry(row_num, z_entry)?;
        }
        Ok(vector)
    }
}

#[cfg(test)]
mod test_new {
    use crate::integer::{VecZ, Z};

    /// Ensure that entries of a new vector are `0`.
    #[test]
    fn entry_zero() {
        let matrix = VecZ::new(2).unwrap();

        let entry1 = matrix.get_entry(0).unwrap();
        let entry2 = matrix.get_entry(0).unwrap();

        assert_eq!(Z::from_i64(0), entry1);
        assert_eq!(Z::from_i64(0), entry2);
    }

    /// Ensure that a new zero vector fails with `0` or a negative value as input.
    #[test]
    fn error_zero_negative() {
        let matrix1 = VecZ::new(0);
        let matrix2 = VecZ::new(-1);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
    }
}

#[cfg(test)]
mod test_from_str {
    use crate::integer::{VecZ, Z};
    use std::str::FromStr;

    /// Ensure that initialization works
    #[test]
    fn init_works() {
        let vector_string = String::from("[1, 2, 3]");

        assert_eq!(
            Z::from_i64(1),
            VecZ::from_str(&vector_string)
                .unwrap()
                .get_entry(0)
                .unwrap()
        );
    }

    /// Ensure that initialization with positive numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_large_numbers() {
        let vector_string = format!("[{}, 2, 3]", "1".repeat(65));

        assert_eq!(
            Z::from_str(&"1".repeat(65)).unwrap(),
            VecZ::from_str(&vector_string)
                .unwrap()
                .get_entry(0)
                .unwrap()
        );
    }

    /// Ensure that initialization with negative numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_small_numbers() {
        let vector_string = format!("[-{}, 2, 3]", "1".repeat(65));

        let entry = format!("-{}", "1".repeat(65));

        assert_eq!(
            Z::from_str(&entry).unwrap(),
            VecZ::from_str(&vector_string)
                .unwrap()
                .get_entry(0)
                .unwrap()
        );
    }

    /// Ensure that entries can have leading and trailing whitespaces.
    #[test]
    fn whitespaces_in_entries_works() {
        let vector_string = String::from("[  1, 2 ,  3  ]");

        assert_eq!(
            Z::from_i64(1),
            VecZ::from_str(&vector_string)
                .unwrap()
                .get_entry(0)
                .unwrap()
        );
    }

    /// Ensure that entries are set correctly.
    #[test]
    fn entries_set_correctly() {
        let vector_string = format!("[0,{},{}, -10, 10]", i64::MIN, i64::MAX);

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
        let vector_string2 = String::from("[[1, 2, 3]]");
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
