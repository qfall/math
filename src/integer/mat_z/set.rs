//! Implementation to set entries from a [`MatZ`] matrix.

use flint_sys::{fmpz::fmpz_set, fmpz_mat::fmpz_mat_entry};

use crate::{error::MathError, integer::Z};

use super::MatZ;

impl MatZ {
    /// Sets the value of a specific matrix entry according to a given `value` of type [Z].
    ///
    /// Input parameters:
    /// * `row`: specifies the row in which the entry is located
    /// * `column`: specifies the column in which the entry is located
    /// * `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```rust
    /// use math::integer::MatZ;
    /// use math::integer::Z;
    ///
    /// let mut matrix = MatZ::new(5, 10).unwrap();
    /// let value = Z::from_i64(5);
    /// matrix.set_entry(1, 1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [MathError::OutOfBounds]
    /// if the number of rows or columns is greater than the matrix.
    pub fn set_entry(&mut self, row: u32, column: u32, value: &Z) -> Result<(), MathError> {
        if self.get_num_rows() <= row || self.get_num_columns() <= column {
            return Err(MathError::OutOfBounds(
                format!(
                    "be smaller than ({},{})",
                    self.get_num_rows(),
                    self.get_num_columns()
                ),
                format!("({},{})", row, column,),
            ));
        }

        // since `self` is a correct matrix and both row and column
        // are previously checked to be inside of the matrix, no errors
        // appear inside of `unsafe` and `fmpz_set` can successfully clone the
        // value inside the matrix. Therefore no memory leaks can appear.
        unsafe {
            let entry = fmpz_mat_entry(&self.matrix, row as i64, column as i64);
            fmpz_set(entry, &value.value)
        };

        Ok(())
    }
}

#[cfg(test)]
mod tests_setter {
    use std::str::FromStr;

    use crate::integer::MatZ;

    use super::Z;

    // Ensure that setting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MAX);
        matrix.set_entry(1, 1, &value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from_i64(i64::MAX));
    }

    // Ensure that setting entries works with large numbers (larger than i64).
    #[test]
    fn big_positive() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_str(&"1".repeat(65)).unwrap();
        matrix.set_entry(1, 1, &value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from_str(&"1".repeat(65)).unwrap());
    }

    // Ensure that setting entries works with large negative numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MIN);
        matrix.set_entry(1, 1, &value).unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry, Z::from_i64(i64::MIN));
    }

    // Ensure that setting entries works with large negative numbers (larger than i64).
    #[test]
    fn big_negative() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let mut value = "-".to_string();
        value.push_str(&"1".repeat(65));
        matrix
            .set_entry(1, 1, &Z::from_str(&value).unwrap())
            .unwrap();

        let entry = matrix.get_entry(1, 1).unwrap();

        let mut test_entry = "-".to_string();
        test_entry.push_str(&"1".repeat(65));

        assert_eq!(entry, Z::from_str(&test_entry).unwrap());
    }

    // Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MAX);

        assert!(matrix.set_entry(5, 1, &value).is_err());
    }

    // Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_i64(i64::MAX);

        assert!(matrix.set_entry(1, 100, &value).is_err());
    }

    // Ensure that the entry is correctly cloned.
    #[test]
    fn memory_test() {
        let mut matrix = MatZ::new(5, 10).unwrap();
        let value = Z::from_str(&"1".repeat(65)).unwrap();
        matrix.set_entry(1, 1, &value).unwrap();

        drop(value);

        assert_eq!(
            matrix.get_entry(1, 1).unwrap(),
            Z::from_str(&"1".repeat(65)).unwrap()
        );
    }
}
