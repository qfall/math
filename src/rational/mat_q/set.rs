//! Implementation to set entries from a [`MatZ`] matrix.

use super::MatQ;
use crate::{error::MathError, rational::Q, utils::coordinate::evaluate_coordinate};
use flint_sys::{fmpq::fmpq_set, fmpq_mat::fmpq_mat_entry};
use std::fmt::Display;

impl MatQ {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`Q`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```rust
    /// use math::rational::MatQ;
    /// use math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatQ::new(5, 10).unwrap();
    /// let value = Q::from_str("5/2").unwrap();
    /// matrix.set_entry(1, 1, value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    pub fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
        value: impl Into<Q>,
    ) -> Result<(), MathError> {
        self.set_entry_ref_q(row, column, &value.into())
    }

    /// Sets the value of a specific matrix entry according to a given `value` of type [`Q`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```rust
    /// use math::rational::MatQ;
    /// use math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatQ::new(5, 10).unwrap();
    /// let value = Q::from_str("5/2").unwrap();
    /// matrix.set_entry_ref_q(1, 1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    pub fn set_entry_ref_q(
        &mut self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
        value: &Q,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = self.evaluate_coordinates(row, column)?;

        // since `self` is a correct matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpq_set` can successfully clone the
        // value inside the matrix. Therefore no memory leaks can appear.
        unsafe {
            let entry = fmpq_mat_entry(&self.matrix, row_i64, column_i64);
            fmpq_set(entry, &value.value)
        };

        Ok(())
    }

    /// Evaluates whether the provided coordinates are referencing an entry in the matrix.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Returns the coordinates as a pair of [`i64`] if they reference an entry and return
    /// an error otherwise.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    pub(super) fn evaluate_coordinates(
        &self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
    ) -> Result<(i64, i64), MathError> {
        let row_i64 = evaluate_coordinate(row)?;
        let column_i64 = evaluate_coordinate(column)?;
        if self.get_num_rows() <= row_i64 || self.get_num_columns() <= column_i64 {
            return Err(MathError::OutOfBounds(
                format!(
                    "be smaller than ({},{})",
                    self.get_num_rows(),
                    self.get_num_columns()
                ),
                format!("({},{})", row_i64, column_i64),
            ));
        }
        Ok((row_i64, column_i64))
    }
}

#[cfg(test)]
mod test_setter {
    use super::Q;
    use crate::rational::MatQ;
    use std::str::FromStr;

    /// Ensure that setting entries works with standard numbers.
    #[test]
    fn standard_value() {
        let mut matrix = MatQ::new(5, 10).unwrap();
        let value = Q::from_str("869").unwrap();
        matrix.set_entry_ref_q(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(Q::from_str("869").unwrap(), entry);
    }

    /// Ensure that setting entries works with large large numerators and denominators.
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

    /// Ensure that setting entries works with large numerators and denominators (larger than [`i64`]).
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

    /// Ensure that setting entries works with large negative numerators and denominators.
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

    /// Ensure that setting entries works with large negative numerators and denominators (larger than [`i64`]).
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

    /// Ensure that setting entries at (0,0) works.
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
}
