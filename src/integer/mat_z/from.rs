//! Implementations to create a [`Z`](crate::integer::Z) value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::MatZ;
use crate::{error::MathError, utils::coordinate::evaluate_coordinate};
use flint_sys::fmpz_mat::fmpz_mat_init;
use std::{fmt::Display, mem::MaybeUninit};

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
    /// ```rust
    /// use math::integer::MatZ;
    ///
    /// let matrix = MatZ::new(5, 10).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidInitMatZInput`](MathError::InvalidInitMatZInput)
    /// if the number of rows or columns is 0.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is negative or it does not fit into an [`i64`].
    pub fn new<S: TryInto<i64> + Display + Copy, T: TryInto<i64> + Display + Copy>(
        num_rows: S,
        num_cols: T,
    ) -> Result<Self, MathError> {
        let num_rows_i64 = evaluate_coordinate(num_rows)?;
        let num_cols_i64 = evaluate_coordinate(num_cols)?;

        if num_rows_i64 == 0 || num_cols_i64 == 0 {
            return Err(MathError::InvalidInitMatZInput(format!(
                "({},{})",
                num_rows, num_cols,
            )));
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

#[cfg(test)]
mod test_new {
    use crate::integer::{MatZ, Z};

    // Ensure that entries of a new matrix are 0.
    #[test]
    fn entry_zero() {
        let matrix = MatZ::new(2, 2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(0, 1).unwrap();
        let entry3 = matrix.get_entry(1, 0).unwrap();
        let entry4 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(entry1, Z::from_i64(0));
        assert_eq!(entry2, Z::from_i64(0));
        assert_eq!(entry3, Z::from_i64(0));
        assert_eq!(entry4, Z::from_i64(0));
    }

    // Ensure that a new zero matrix fails with 0 as input.
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
