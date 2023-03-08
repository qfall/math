//! Implementations to get entries from a [`MatZ`] matrix.

use super::MatZ;
use crate::{error::MathError, integer::Z, utils::coordinate::evaluate_coordinate};
use flint_sys::{
    fmpz::{fmpz, fmpz_set},
    fmpz_mat::fmpz_mat_entry,
};
use std::fmt::Display;

impl MatZ {
    /// Outputs the [`Z`] value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Returns the [`Z`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// # Example
    /// ```rust
    /// use math::integer::MatZ;
    ///
    /// let matrix = MatZ::new(5, 10).unwrap();
    /// let entry = matrix.get_entry(0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    pub fn get_entry<S: TryInto<i64> + Display + Copy, T: TryInto<i64> + Display + Copy>(
        &self,
        row: S,
        column: T,
    ) -> Result<Z, MathError> {
        let row_i64 = evaluate_coordinate(row)?;
        let column_i64 = evaluate_coordinate(column)?;

        if self.get_num_rows() <= row_i64 || self.get_num_columns() <= column_i64 {
            return Err(MathError::OutOfBounds(
                format!(
                    "be smaller than ({},{})",
                    self.get_num_rows(),
                    self.get_num_columns()
                ),
                format!("({},{})", row_i64, column_i64,),
            ));
        }

        // since `self.matrix` is a correct fmpz matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpz_set` can successfully clone the
        // entry of the matrix. Therefore no memory leaks can appear.
        let mut copy = fmpz(0);
        let entry = unsafe { fmpz_mat_entry(&self.matrix, row_i64, column_i64) };
        unsafe { fmpz_set(&mut copy, entry) };

        Ok(Z { value: copy })
    }

    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Example
    /// ```rust
    /// use math::integer::MatZ;
    ///
    /// let matrix = MatZ::new(5,6).unwrap();
    /// let rows = matrix.get_num_rows();
    /// ```
    pub fn get_num_rows(&self) -> i64 {
        self.matrix.r
    }

    /// Returns the number of columns of the matrix as a [`i64`].
    ///
    /// # Example
    /// ```rust
    /// use math::integer::MatZ;
    ///
    /// let matrix = MatZ::new(5,6).unwrap();
    /// let columns = matrix.get_num_columns();
    /// ```
    pub fn get_num_columns(&self) -> i64 {
        self.matrix.c
    }
}

#[cfg(test)]
mod test_get_entry {
    use std::str::FromStr;

    use crate::integer::MatZ;

    use super::Z;

    // Ensure that getting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MAX);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from_i64(i64::MAX), entry);
    }

    // Ensure that getting entries works with large numbers (larger than i64).
    #[test]
    fn big_positive() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_str(&"1".repeat(65)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from_str(&"1".repeat(65)).unwrap(), entry);
    }

    // Ensure that getting entries works with large negative numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MIN);
        matrix.set_entry(1, 1, value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::from_i64(i64::MIN), entry);
    }

    // Ensure that getting entries works with large negative numbers (larger than i64).
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

        assert_eq!(Z::from_str(&test_entry).unwrap(), entry);
    }

    // Ensure that getting entries at (0,0) works.
    #[test]
    fn getting_at_zero() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MIN);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(entry, Z::from_i64(i64::MIN));
    }

    // Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let matrix = MatZ::new(5, 10).unwrap();

        assert!(matrix.get_entry(5, 1).is_err());
    }

    // Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatZ::new(5, 10).unwrap();

        assert!(matrix.get_entry(1, 100).is_err());
    }

    // Ensure that the entry is a deep copy and not just a clone of the reference.
    #[test]
    fn memory_test() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_str(&"1".repeat(65)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();
        let entry = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(1, 1, Z::from_i64(0)).unwrap();

        assert_eq!(Z::from_str(&"1".repeat(65)).unwrap(), entry);
    }
}

#[cfg(test)]
mod test_get_num {
    use crate::integer::MatZ;

    // Ensure that the getter for rows works correctly.
    #[test]
    fn num_rows() {
        let matrix = MatZ::new(5, 10).unwrap();

        assert_eq!(matrix.get_num_rows(), 5);
    }

    // Ensure that the getter for columns works correctly.
    #[test]
    fn num_columns() {
        let matrix = MatZ::new(5, 10).unwrap();

        assert_eq!(matrix.get_num_columns(), 10);
    }
}
