//! Implementations to create a [`MatZq`](crate::integer_mod_q::MatZq) value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//! Furthermore, an instantiation of a zero matrix is implemented.
//!
//! The explicit functions contain the documentation.

use super::MatZq;
use crate::{error::MathError, integer::Z, utils::coordinate::evaluate_coordinate};
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_init;
use std::{fmt::Display, mem::MaybeUninit};

impl MatZq {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns,
    /// zeros as entries and `modulus` as the modulus.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    /// - `modulus`: the common modulus of the matrix entries
    ///
    /// Returns a [`MatZq`] or an error, if the number of rows or columns is
    /// less or equal to 0.
    ///
    /// # Example
    /// ```rust
    /// use math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::new(5, 10, 7).unwrap();
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
        modulus: impl Into<Z>,
    ) -> Result<Self, MathError> {
        let num_rows_i64 = evaluate_coordinate(num_rows)?;
        let num_cols_i64 = evaluate_coordinate(num_cols)?;

        if num_rows_i64 == 0 || num_cols_i64 == 0 {
            return Err(MathError::InvalidMatrix(format!(
                "({},{})",
                num_rows, num_cols,
            )));
        }

        let modulus = std::convert::Into::<Z>::into(modulus);

        if modulus < Z::from_i64(1) {
            return Err(MathError::InvalidIntToModulus(format!("{}", modulus)));
        }

        // initialize variable with MaybeUn-initialized value to check
        // correctness of initialization later
        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_mod_mat_init(
                matrix.as_mut_ptr(),
                num_rows_i64,
                num_cols_i64,
                &modulus.value,
            );

            Ok(MatZq {
                matrix: matrix.assume_init(),
            })
        }
    }
}

#[cfg(test)]
mod test_new {
    use crate::integer_mod_q::MatZq;

    /// Ensure that initialization works.
    #[test]
    fn initialization() {
        assert!(MatZq::new(2, 2, 3).is_ok());
    }

    /// Ensure that a new zero matrix fails with 0 as input.
    #[test]
    fn error_zero() {
        let matrix1 = MatZq::new(1, 0, 3);
        let matrix2 = MatZq::new(0, 1, 3);
        let matrix3 = MatZq::new(0, 0, 3);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
        assert!(matrix3.is_err());
    }

    /// Ensure that an invalid modulus yields an error.
    #[test]
    fn invalid_modulus_error() {
        assert!(MatZq::new(2, 2, -3).is_err());
        assert!(MatZq::new(2, 2, 0).is_err());
    }

    // TODO add test for zero entries
}
