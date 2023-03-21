//! Implementations to create a [`MatZ`](crate::integer::MatZ) matrix from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::MatZ;
use crate::{
    error::MathError,
    integer::Z,
    utils::{
        coordinate::evaluate_coordinate, dimensions::find_matrix_dimensions,
        parse::parse_matrix_string,
    },
};
use flint_sys::fmpz_mat::fmpz_mat_init;
use std::{fmt::Display, mem::MaybeUninit, str::FromStr};

impl MatZ {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns and
    /// zeros as entries.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    ///
    /// Returns a [`MatZ`] or an error, if the number of rows or columns is
    /// less or equal to 0.
    ///
    /// # Example
    /// ```
    /// use math::integer::MatZ;
    ///
    /// let matrix = MatZ::new(5, 10).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the number of rows or columns is 0.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is negative or it does not fit into an [`i64`].
    pub fn new(
        num_rows: impl TryInto<i64> + Display + Copy,
        num_cols: impl TryInto<i64> + Display + Copy,
    ) -> Result<Self, MathError> {
        let num_rows_i64 = evaluate_coordinate(num_rows)?;
        let num_cols_i64 = evaluate_coordinate(num_cols)?;

        if num_rows_i64 == 0 || num_cols_i64 == 0 {
            return Err(MathError::InvalidMatrix(
                "A matrix can not contain 0 rows or 0 columns".to_string(),
            ));
        }

        // initialize variable with MaybeUn-initialized value to check
        // correctness of initialization later
        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_mat_init(matrix.as_mut_ptr(), num_rows_i64, num_cols_i64);

            // Construct MatZ from previously initialized fmpz_mat
            Ok(MatZ {
                matrix: matrix.assume_init(),
            })
        }
    }
}

impl FromStr for MatZ {
    type Err = MathError;

    /// Creates a [`MatZ`] matrix with entries in [`Z`] from a [`String`].
    /// The format of that string looks like this `[[1,2,3],[4,5,6]]` for a 2x3 matrix
    /// with entries 1, 2, 3 in the first row and 4, 5, 6 in the second row.
    ///
    /// Parameters:
    /// - `string`: the matrix as a string
    ///
    /// Returns a [`MatZ`] or an error, if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too big (must fit into [`i64`]),
    /// the number of entries in rows is unequal or if the regular expression
    /// inside of the function could not be processed.
    ///
    /// # Example
    /// ```
    /// use math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1, 2, 3],[3, 4, 5]]");
    /// let matrix = MatZ::from_str(&string).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too big (must fit into [`i64`]) or
    /// if the number of entries in rows is unequal.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if an entry contains a Nul byte.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToZInput`](MathError::InvalidStringToZInput)
    /// if an entry is not formatted correctly.
    fn from_str(string: &str) -> Result<Self, MathError> {
        let string_matrix = parse_matrix_string(string)?;
        let (num_rows, num_cols) = find_matrix_dimensions(&string_matrix)?;
        let mut matrix = MatZ::new(num_rows, num_cols)?;

        // fill entries of matrix according to entries in string_matrix
        for (row_num, row) in string_matrix.iter().enumerate() {
            for (col_num, entry) in row.iter().enumerate() {
                let z_entry = Z::from_str(entry)?;
                matrix.set_entry(row_num, col_num, z_entry)?;
            }
        }
        Ok(matrix)
    }
}

#[cfg(test)]
mod test_new {
    use crate::integer::{MatZ, Z};

    /// Ensure that entries of a new matrix are 0.
    #[test]
    fn entry_zero() {
        let matrix = MatZ::new(2, 2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(0, 1).unwrap();
        let entry3 = matrix.get_entry(1, 0).unwrap();
        let entry4 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from_i64(0), entry1);
        assert_eq!(Z::from_i64(0), entry2);
        assert_eq!(Z::from_i64(0), entry3);
        assert_eq!(Z::from_i64(0), entry4);
    }

    /// Ensure that a new zero matrix fails with 0 as input.
    #[test]
    fn error_zero() {
        let matrix1 = MatZ::new(1, 0);
        let matrix2 = MatZ::new(0, 1);
        let matrix3 = MatZ::new(0, 0);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
        assert!(matrix3.is_err());
    }
}

#[cfg(test)]
mod test_from_str {
    use crate::integer::{MatZ, Z};
    use std::str::FromStr;

    /// Ensure that initialization works.
    #[test]
    fn init_works() {
        let matrix_string1 = String::from("[[1, 2, 3],[3, 4, 5]]");

        assert_eq!(
            Z::from_i64(1),
            MatZ::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that initialization with positive numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_large_numbers() {
        let matrix_string = format!("[[{}, 2, 3],[3, 4, 5]]", "1".repeat(65));

        assert_eq!(
            Z::from_str(&"1".repeat(65)).unwrap(),
            MatZ::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that initialization with negative numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_small_numbers() {
        let matrix_string = format!("[[-{}, 2, 3],[3, 4, 5]]", "1".repeat(65));

        let entry = format!("-{}", "1".repeat(65));

        assert_eq!(
            Z::from_str(&entry).unwrap(),
            MatZ::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that entries can have leading and trailing whitespaces.
    #[test]
    fn whitespaces_in_entries_works() {
        let matrix_string1 = String::from("[[  1, 2 ,  3  ],[3 ,4,5 ]]");

        assert_eq!(
            Z::from_i64(1),
            MatZ::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_string1 = String::from("[1, 2, 3],[3, 4, 5]]");
        let matrix_string2 = String::from("[[1, 2, 3][3, 4, 5]]");
        let matrix_string3 = String::from("[[1, 2, 3],3, 4, 5]");
        let matrix_string4 = String::from("[1, 2, 3, 4, 5]");
        let matrix_string5 = String::from("[ [1, 2, 3],[3, 4, 5]]");
        let matrix_string6 = String::from("[[1, 2, 3],[3, 4, 5]8]");
        let matrix_string7 = String::from("");
        let matrix_string8 = String::from("[]");
        let matrix_string9 = String::from("[[]]");

        assert!(MatZ::from_str(&matrix_string1).is_err());
        assert!(MatZ::from_str(&matrix_string2).is_err());
        assert!(MatZ::from_str(&matrix_string3).is_err());
        assert!(MatZ::from_str(&matrix_string4).is_err());
        assert!(MatZ::from_str(&matrix_string5).is_err());
        assert!(MatZ::from_str(&matrix_string6).is_err());
        assert!(MatZ::from_str(&matrix_string7).is_err());
        assert!(MatZ::from_str(&matrix_string8).is_err());
        assert!(MatZ::from_str(&matrix_string9).is_err());
    }
}
