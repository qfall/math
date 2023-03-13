//! Implementations to create a [`MatQ`](crate::rational::MatQ) value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::MatQ;
use crate::{error::MathError, utils::coordinate::evaluate_coordinate};
use flint_sys::fmpq_mat::fmpq_mat_init;
use std::{fmt::Display, mem::MaybeUninit};

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
