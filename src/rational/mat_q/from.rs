//! Implementations to create a [`MatQ`](crate::rational::MatQ) value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::MatQ;
use crate::{
    error::MathError,
    rational::Q,
    utils::{
        coordinate::evaluate_coordinate, dimensions::find_matrix_dimensions,
        parse::parse_matrix_string,
    },
};
use flint_sys::fmpq_mat::fmpq_mat_init;
use std::{fmt::Display, mem::MaybeUninit, str::FromStr};

impl MatQ {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns and
    /// zeros as entries.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    ///
    /// Returns a [`MatQ`] or an error, if the number of rows or columns is
    /// less or equal to 0.
    ///
    /// # Example
    /// ```rust
    /// use math::rational::MatQ;
    ///
    /// let matrix = MatQ::new(5, 10).unwrap();
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
            return Err(MathError::InvalidMatrix(format!(
                "({},{})",
                num_rows, num_cols,
            )));
        }

        // initialize variable with MaybeUn-initialized value to check
        // correctness of initialization later
        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpq_mat_init(matrix.as_mut_ptr(), num_rows_i64, num_cols_i64);

            // Construct MatQ from previously initialized fmpq_mat
            Ok(MatQ {
                matrix: matrix.assume_init(),
            })
        }
    }
}

impl FromStr for MatQ {
    type Err = MathError;

    /// Creates a [`MatQ`] matrix with entries in [`Q`] from a [`String`].
    /// The format of that string looks like this `[[1/2,2/3,3/4],[4/5,5/6,6/7]]` for a 2x3 matrix
    /// with entries 1/2,2/3,3/4 in the first row and 4/5,5/6,6/7 in the second row.
    ///
    /// Parameters:
    /// - `string`: the matrix as a string
    ///
    /// Returns a [`MatQ`] or an error, if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too big (must fit into [`i64`]),
    /// the number of entries in rows is unequal or if the regular expression
    /// inside of the function could not be processed.
    ///
    /// # Example
    /// ```rust
    /// use math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1/2,2/3,3/4],[4/5,5/6,6/7]]");
    /// let matrix = MatQ::from_str(&string).unwrap();
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
        let mut matrix = MatQ::new(num_rows, num_cols)?;

        // fill entries of matrix according to entries in string_matrix
        for (row_num, row) in string_matrix.iter().enumerate() {
            for (col_num, entry) in row.iter().enumerate() {
                let z_entry = Q::from_str(entry)?;
                matrix.set_entry(row_num, col_num, z_entry)?;
            }
        }
        Ok(matrix)
    }
}

#[cfg(test)]
mod test_new {
    use crate::rational::MatQ;

    /// Ensure that initialization works.
    #[test]
    fn initialization() {
        assert!(MatQ::new(2, 2).is_ok());
    }

    /// Ensure that a new zero matrix fails with 0 as input.
    #[test]
    fn error_zero() {
        let matrix1 = MatQ::new(1, 0);
        let matrix2 = MatQ::new(0, 1);
        let matrix3 = MatQ::new(0, 0);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
        assert!(matrix3.is_err());
    }
    // TODO add test for zero entries
}

#[cfg(test)]
mod test_from_str {
    use crate::{
        integer::Z,
        rational::{MatQ, Q},
    };
    use std::str::FromStr;

    /// Ensure that initialization works.
    #[test]
    fn init_works() {
        let matrix_string1 = String::from("[[1/2,2/3,3/4],[4/5,5/6,6/7]]");

        assert_eq!(
            Q::from_str("1/2").unwrap(),
            MatQ::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that initialization works with integers.
    #[test]
    fn init_integer_works() {
        let matrix_string1 = String::from("[[1, 2, 3],[3, 4, 5]]");

        assert_eq!(
            Z::from_i64(1),
            Z {
                value: MatQ::from_str(&matrix_string1)
                    .unwrap()
                    .get_entry(0, 0)
                    .unwrap()
                    .value
                    .num
            }
        );

        assert_eq!(
            Z::from_i64(1),
            Z {
                value: MatQ::from_str(&matrix_string1)
                    .unwrap()
                    .get_entry(0, 0)
                    .unwrap()
                    .value
                    .den
            }
        );
    }

    /// Ensure that initialization with positive numerators and denominators
    /// that are larger than [`i64`] works.
    #[test]
    fn init_works_large_numbers() {
        let matrix_string = format!("[[{}/1, 1/{}, 3],[3, 4, 5]]", u64::MAX, u64::MAX);

        assert_eq!(
            Z::from_str(&format!("{}", u64::MAX)).unwrap(),
            Z {
                value: MatQ::from_str(&matrix_string)
                    .unwrap()
                    .get_entry(0, 0)
                    .unwrap()
                    .value
                    .num
            }
        );

        assert_eq!(
            Z::from_str(&format!("{}", u64::MAX)).unwrap(),
            Z {
                value: MatQ::from_str(&matrix_string)
                    .unwrap()
                    .get_entry(0, 1)
                    .unwrap()
                    .value
                    .den
            }
        );
    }

    /// Ensure that initialization with negative large numerators and denominators
    /// that are larger than [`i64`] works.
    #[test]
    fn init_works_small_numbers() {
        let matrix_string = format!("[[-{}/1, 1/-{}, 3],[3, 4, 5]]", u64::MAX, u64::MAX);

        assert_eq!(
            Q::from_str(&format!("-{}", u64::MAX)).unwrap(),
            MatQ::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );

        assert_eq!(
            Q::from_str(&format!("1/-{}", u64::MAX)).unwrap(),
            MatQ::from_str(&matrix_string)
                .unwrap()
                .get_entry(0, 1)
                .unwrap()
        );
    }

    /// Ensure that entries can have leading and trailing whitespaces.
    #[test]
    fn whitespaces_in_entries_works() {
        let matrix_string1 = String::from("[[  1/2, 2/3 ,  3/4  ],[3/4 ,4/5,5/6 ]]");

        assert_eq!(
            Q::from_str("1/2").unwrap(),
            MatQ::from_str(&matrix_string1)
                .unwrap()
                .get_entry(0, 0)
                .unwrap()
        );
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_string1 = String::from("[1/2, 2, 3],[3, 4/7, 5]]");
        let matrix_string2 = String::from("[[1, 2/9, 3][3, 4, 5/5]]");
        let matrix_string3 = String::from("[[1, 2, 3/2],3, 4, 5]");
        let matrix_string4 = String::from("[1, 2, 3, 4/5, 5]");
        let matrix_string5 = String::from("[ [1, 2/8, 3],[3, 4, 5]]");
        let matrix_string6 = String::from("[[1, 2, 3],[3, 4/9, 5]8]");
        let matrix_string7 = String::from("");
        let matrix_string8 = String::from("[]");
        let matrix_string9 = String::from("[[]]");

        assert!(MatQ::from_str(&matrix_string1).is_err());
        assert!(MatQ::from_str(&matrix_string2).is_err());
        assert!(MatQ::from_str(&matrix_string3).is_err());
        assert!(MatQ::from_str(&matrix_string4).is_err());
        assert!(MatQ::from_str(&matrix_string5).is_err());
        assert!(MatQ::from_str(&matrix_string6).is_err());
        assert!(MatQ::from_str(&matrix_string7).is_err());
        assert!(MatQ::from_str(&matrix_string8).is_err());
        assert!(MatQ::from_str(&matrix_string9).is_err());
    }
}
