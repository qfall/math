//! Implementations to create a [`MatPolyOverZ`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::MatPolyOverZ;
use crate::{error::MathError, utils::coordinate::evaluate_coordinate};
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_init;
use std::{fmt::Display, mem::MaybeUninit};

impl MatPolyOverZ {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns and
    /// zeros as entries.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    ///
    /// Returns a [`MatPolyOverZ`] or an error, if the number of rows or columns is
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
    /// [`InvalidInitMatInput`](MathError::InvalidInitMatInput)
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
            return Err(MathError::InvalidInitMatInput(format!(
                "({},{})",
                num_rows, num_cols,
            )));
        }

        // initialize variable with MaybeUn-initialized value to check
        // correctness of initialization later
        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_poly_mat_init(matrix.as_mut_ptr(), num_rows_i64, num_cols_i64);

            // Construct MatZ from previously initialized fmpz_mat
            Ok(MatPolyOverZ {
                matrix: matrix.assume_init(),
            })
        }
    }
}

#[cfg(test)]
mod test_new {
    use crate::integer::MatPolyOverZ;

    /// Ensure that entries of a new matrix are 0.
    #[test]
    fn entry_zero() {
        let matrix = MatPolyOverZ::new(2, 2).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(0, 1).unwrap();
        let entry3 = matrix.get_entry(1, 0).unwrap();
        let entry4 = matrix.get_entry(1, 1).unwrap();

        assert_eq!("0", entry1.to_string());
        assert_eq!("0", entry2.to_string());
        assert_eq!("0", entry3.to_string());
        assert_eq!("0", entry4.to_string());
    }

    /// Ensure that a new zero matrix fails with 0 as input.
    #[test]
    fn error_zero() {
        let matrix1 = MatPolyOverZ::new(1, 0);
        let matrix2 = MatPolyOverZ::new(0, 1);
        let matrix3 = MatPolyOverZ::new(0, 0);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
        assert!(matrix3.is_err());
    }
}
