//! Implementations to create a [`Z`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use crate::error::MathError;

use super::MatZ;

use flint_sys::fmpz_mat::fmpz_mat_init;

use std::mem::MaybeUninit;

impl MatZ {
    /// Creates a new zero matrix.
    ///
    /// Input parameters:
    /// * `num_rows`: number of rows the new matrix should have
    /// * `num_cols`: number of columns the new matrix should have
    ///
    /// # Example
    /// ```rust
    /// use math::integer::MatZ;
    ///
    /// let matrix = MatZ::new(5, 10).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [MathError::InvalidIntInput]
    /// if the number of rows or columns is 0.
    pub fn new(num_rows: u32, num_cols: u32) -> Result<Self, MathError> {
        if num_rows == 0 || num_cols == 0 {
            return Err(MathError::InvalidIntInput(format!(
                "({},{})",
                num_rows, num_cols,
            )));
        }

        // initialize variable with MaybeUn-initialized value to check
        // correctness of initialization later
        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_mat_init(matrix.as_mut_ptr(), num_rows as i64, num_cols as i64);

            // Construct MatZ from previously initialized fmpz_mat
            Ok(MatZ {
                matrix: matrix.assume_init(),
            })
        }
    }
}

#[cfg(test)]
mod tests_new {
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
}
