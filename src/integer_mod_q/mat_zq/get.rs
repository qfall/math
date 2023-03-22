//! Implementations to get entries from a [`MatZq`] matrix.

use super::MatZq;
use crate::integer::Z;
use crate::integer_mod_q::Modulus;
use crate::traits::{GetEntry, GetNumColumns, GetNumRows};
use crate::utils::coordinate::evaluate_coordinates;
use crate::{error::MathError, integer_mod_q::Zq};
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_entry;
use std::fmt::Display;

impl MatZq {
    /// Returns the modulus of the matrix as a [`Modulus`] value
    ///
    /// # Example
    /// ```rust
    /// use math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::new(5, 10, 7).unwrap();
    /// let entry = matrix.get_mod().unwrap();
    /// ```
    pub fn get_mod(&self) -> Result<Modulus, MathError> {
        Modulus::try_from_z(&Z {
            value: self.matrix.mod_[0],
        })
    }
}

impl GetNumRows for MatZq {
    /// Returns the number of rows of the matrix as a [`i64`].
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::MatZq;
    /// use math::traits::GetNumRows;
    ///
    /// let matrix = MatZq::new(5, 6, 7).unwrap();
    /// let rows = matrix.get_num_rows();
    /// ```
    fn get_num_rows(&self) -> i64 {
        self.matrix.mat[0].r
    }
}

impl GetNumColumns for MatZq {
    /// Returns the number of columns of the matrix as a [`i64`].
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::MatZq;
    /// use math::traits::GetNumColumns;
    ///
    /// let matrix = MatZq::new(5, 6, 7).unwrap();
    /// let rows = matrix.get_num_columns();
    /// ```
    fn get_num_columns(&self) -> i64 {
        self.matrix.mat[0].c
    }
}

impl GetEntry<Z> for MatZq {
    /// Outputs the [`Zq`] value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Returns the [`Zq`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// # Example
    /// ```rust
    /// use math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::new(5, 10, 7).unwrap();
    /// let entry = matrix.get_entry(0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    fn get_entry(
        &self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
    ) -> Result<Z, MathError> {
        let (row_i64, column_i64) = evaluate_coordinates(self, row, column)?;

        Ok(Z {
            value: unsafe { *fmpz_mod_mat_entry(&self.matrix, row_i64, column_i64) },
        })
    }
}

impl GetEntry<Zq> for MatZq {
    /// Outputs the [`Zq`] value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Returns the [`Zq`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// # Example
    /// ```rust
    /// use math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::new(5, 10, 7).unwrap();
    /// let entry = matrix.get_entry(0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
    fn get_entry(
        &self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
    ) -> Result<Zq, MathError> {
        let (row_i64, column_i64) = evaluate_coordinates(self, row, column)?;

        let value = unsafe { *fmpz_mod_mat_entry(&self.matrix, row_i64, column_i64) };
        let modulus = self.get_mod()?;

        Ok(Zq::from_z_modulus(&Z { value }, &modulus))
    }
}
