//! Implementation to set entries from a [`MatZ`] matrix.

use super::MatZ;
use crate::{error::MathError, integer::Z, utils::coordinate::evaluate_coordinate};
use flint_sys::{fmpz::fmpz_set, fmpz_mat::fmpz_mat_entry};
use std::fmt::Display;

impl MatZ {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`Z`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```rust
    /// use math::integer::MatZ;
    /// use math::integer::Z;
    ///
    /// let mut matrix = MatZ::new(5, 10).unwrap();
    /// let value = Z::from_i64(5);
    /// matrix.set_entry(1, 1, value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    pub fn set_entry<
        S: TryInto<i64> + Display + Copy,
        T: TryInto<i64> + Display + Copy,
        U: Into<Z>,
    >(
        &mut self,
        row: S,
        column: T,
        value: U,
    ) -> Result<(), MathError> {
        self.set_entry_ref_z(row, column, &value.into())
    }

    /// Sets the value of a specific matrix entry according to a given `value` of type [`Z`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```rust
    /// use math::integer::MatZ;
    /// use math::integer::Z;
    ///
    /// let mut matrix = MatZ::new(5, 10).unwrap();
    /// let value = Z::from_i64(5);
    /// matrix.set_entry_ref_z(1, 1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    pub fn set_entry_ref_z<S: TryInto<i64> + Display + Copy, T: TryInto<i64> + Display + Copy>(
        &mut self,
        row: S,
        column: T,
        value: &Z,
    ) -> Result<(), MathError> {
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

        // since `self` is a correct matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpz_set` can successfully clone the
        // value inside the matrix. Therefore no memory leaks can appear.
        unsafe {
            let entry = fmpz_mat_entry(&self.matrix, row_i64, column_i64);
            fmpz_set(entry, &value.value)
        };

        Ok(())
    }
}

#[cfg(test)]
mod test_setter {
    use super::Z;
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensure that setting entries works with standard numbers.
    #[test]
    fn standard_value() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(869);
        matrix.set_entry_ref_z(4, 7, &value).unwrap();

        let entry = matrix.get_entry(4, 7).unwrap();

        assert_eq!(entry, Z::from_i64(869));
    }

    /// Ensure that setting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MAX);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from_i64(i64::MAX));
    }

    /// Ensure that setting entries works with large numbers (larger than i64).
    #[test]
    fn big_positive() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_str(&"1".repeat(65)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from_str(&"1".repeat(65)).unwrap());
    }

    /// Ensure that setting entries works with referenced large numbers (larger than i64).
    #[test]
    fn big_positive_ref() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value1 = Z::from_str(&"1".repeat(65)).unwrap();
        let value2 = Z::from_i64(8);
        matrix.set_entry_ref_z(1, 1, &value1).unwrap();
        matrix.set_entry(0, 0, value2).unwrap();

        let entry1 = matrix.get_entry(1, 1).unwrap();
        let entry2 = matrix.get_entry(0, 0).unwrap();

        assert_eq!(entry1, Z::from_str(&"1".repeat(65)).unwrap());
        assert_eq!(entry2, Z::from_i64(8));
    }

    /// Ensure that setting entries works with large negative numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MIN);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from_i64(i64::MIN));
    }

    /// Ensure that setting entries works with large negative numbers (larger than i64).
    #[test]
    fn big_negative() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let mut value = "-".to_string();
        value.push_str(&"1".repeat(65));
        matrix
            .set_entry(1, 1, Z::from_str(&value).unwrap())
            .unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        let mut test_entry = "-".to_string();
        test_entry.push_str(&"1".repeat(65));

        assert_eq!(entry, Z::from_str(&test_entry).unwrap());
    }

    /// Ensure that setting entries at (0,0) works.
    #[test]
    fn setting_at_zero() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MIN);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(entry, Z::from_i64(i64::MIN));
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MAX);

        assert!(matrix.set_entry(5, 1, value).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MAX);

        assert!(matrix.set_entry(1, 100, value).is_err());
    }
}
