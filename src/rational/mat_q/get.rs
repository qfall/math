//! Implementations to get entries from a [`MatQ`] matrix.

use super::MatQ;
use crate::traits::{GetNumColumns, GetNumRows};
use crate::utils::coordinate::evaluate_coordinates;
use crate::{error::MathError, rational::Q};
use flint_sys::{fmpq::fmpq_set, fmpq_mat::fmpq_mat_entry};
use std::fmt::Display;

impl MatQ {
    /// Outputs the [`Q`] value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Returns the [`Q`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// # Example
    /// ```rust
    /// use math::rational::MatQ;
    ///
    /// let matrix = MatQ::new(5, 10).unwrap();
    /// let entry = matrix.get_entry(0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    pub fn get_entry(
        &self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
    ) -> Result<Q, MathError> {
        let (row_i64, column_i64) = evaluate_coordinates(self, row, column)?;

        // since `self.matrix` is a correct fmpq matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpq_set` can successfully clone the
        // entry of the matrix. Therefore no memory leaks can appear.
        let mut copy = Q::default();
        let entry = unsafe { fmpq_mat_entry(&self.matrix, row_i64, column_i64) };
        unsafe { fmpq_set(&mut copy.value, entry) };

        Ok(copy)
    }
}

impl GetNumRows for MatQ {
    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Example
    /// ```rust
    /// use math::rational::MatQ;
    /// use math::traits::GetNumRows;
    ///
    /// let matrix = MatQ::new(5,6).unwrap();
    /// let rows = matrix.get_num_rows();
    /// ```
    fn get_num_rows(&self) -> i64 {
        self.matrix.r
    }
}

impl GetNumColumns for MatQ {
    /// Returns the number of columns of the matrix as a [`i64`].
    ///
    /// # Example
    /// ```rust
    /// use math::rational::MatQ;
    /// use math::traits::GetNumColumns;
    ///
    /// let matrix = MatQ::new(5,6).unwrap();
    /// let columns = matrix.get_num_columns();
    /// ```
    fn get_num_columns(&self) -> i64 {
        self.matrix.c
    }
}

#[cfg(test)]
mod test_get_entry {
    use super::Q;
    use crate::rational::MatQ;
    use std::str::FromStr;

    /// Ensure that getting entries works with large large numerators and denominators.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatQ::new(5, 10).unwrap();
        let value1 = Q::from_str(&format!("{}/1", i64::MAX)).unwrap();
        let value2 = Q::from_str(&format!("1/{}", i64::MAX)).unwrap();
        matrix.set_entry(0, 0, value1).unwrap();
        matrix.set_entry(1, 1, value2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Q::from_str(&format!("{}", i64::MAX)).unwrap(), entry1);
        assert_eq!(Q::from_str(&format!("1/{}", i64::MAX)).unwrap(), entry2);
    }

    /// Ensure that getting entries works with large numerators and denominators (larger than [`i64`]).
    #[test]
    fn big_positive() {
        let mut matrix = MatQ::new(5, 10).unwrap();
        let value1 = Q::from_str(&format!("{}", u64::MAX)).unwrap();
        let value2 = Q::from_str(&format!("1/{}", u64::MAX)).unwrap();
        matrix.set_entry(0, 0, value1).unwrap();
        matrix.set_entry(1, 1, value2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Q::from_str(&format!("{}", u64::MAX)).unwrap(), entry1);
        assert_eq!(Q::from_str(&format!("1/{}", u64::MAX)).unwrap(), entry2);
    }

    /// Ensure that getting entries works with large negative numerators and denominators.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatQ::new(5, 10).unwrap();
        let value1 = Q::from_str(&format!("{}", i64::MIN)).unwrap();
        let value2 = Q::from_str(&format!("1/{}", i64::MIN)).unwrap();
        matrix.set_entry(0, 0, value1).unwrap();
        matrix.set_entry(1, 1, value2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Q::from_str(&format!("{}", i64::MIN)).unwrap(), entry1);
        assert_eq!(Q::from_str(&format!("1/{}", i64::MIN)).unwrap(), entry2);
    }

    /// Ensure that getting entries works with large negative numerators and denominators (larger than [`i64`]).
    #[test]
    fn big_negative() {
        let mut matrix = MatQ::new(5, 10).unwrap();
        let value1 = format!("-{}", u64::MAX);
        let value2 = format!("1/-{}", u64::MAX);
        matrix
            .set_entry(0, 0, Q::from_str(&value1).unwrap())
            .unwrap();
        matrix
            .set_entry(1, 1, Q::from_str(&value2).unwrap())
            .unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Q::from_str(&format!("-{}", u64::MAX)).unwrap(), entry1);
        assert_eq!(Q::from_str(&format!("1/-{}", u64::MAX)).unwrap(), entry2);
    }

    /// Ensure that getting entries at (0,0) works.
    #[test]
    fn getting_at_zero() {
        let mut matrix = MatQ::new(5, 10).unwrap();
        let value = Q::from_str(&format!("{}", i64::MIN)).unwrap();
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(entry, Q::from_str(&format!("{}", i64::MIN)).unwrap());
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let matrix = MatQ::new(5, 10).unwrap();

        assert!(matrix.get_entry(5, 1).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatQ::new(5, 10).unwrap();

        assert!(matrix.get_entry(1, 100).is_err());
    }

    /// Ensure that the entry is a deep copy and not just a clone of the reference.
    #[test]
    fn memory_test() {
        let mut matrix = MatQ::new(5, 10).unwrap();
        let value = Q::from_str(&format!("{}", u64::MAX)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();
        let entry = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(1, 1, Q::from_str("0/1").unwrap()).unwrap();

        assert_eq!(Q::from_str(&format!("{}", u64::MAX)).unwrap(), entry);
    }
}

#[cfg(test)]
mod test_get_num {

    use crate::{
        rational::MatQ,
        traits::{GetNumColumns, GetNumRows},
    };

    /// Ensure that the getter for rows works correctly.
    #[test]
    fn num_rows() {
        let matrix = MatQ::new(5, 10).unwrap();

        assert_eq!(matrix.get_num_rows(), 5);
    }

    /// Ensure that the getter for columns works correctly.
    #[test]
    fn num_columns() {
        let matrix = MatQ::new(5, 10).unwrap();

        assert_eq!(matrix.get_num_columns(), 10);
    }
}
