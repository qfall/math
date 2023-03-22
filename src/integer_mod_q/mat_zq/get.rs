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

#[cfg(test)]
mod test_get_entry {
    use super::Zq;
    use crate::{
        error::MathError,
        integer::Z,
        integer_mod_q::MatZq,
        traits::{GetEntry, SetEntry},
    };
    use std::str::FromStr;

    /// Ensure that getting entries works with large numbers.
    #[test]
    fn max_int_positive() {
        let mut matrix = MatZq::new(5, 10, u64::MAX).unwrap();
        let value = Z::from(i64::MAX);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from(i64::MAX), entry);
    }

    /// Ensure that getting entries works with large numerators and denominators (larger than [`i64`]).
    #[test]
    fn big_positive() {
        let mut matrix = MatZq::new(5, 10, u64::MAX).unwrap();
        let value = Z::from(u64::MAX - 1);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from(u64::MAX - 1), entry);
    }

    /// Ensure that getting entries works with large numbers.
    #[test]
    fn max_int_negative() {
        let mut matrix = MatZq::new(5, 10, u64::MAX).unwrap();
        let value = Z::from(-i64::MAX);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(Z::from((u64::MAX as i128 - i64::MAX as i128) as u64), entry);
    }

    /// Ensure that getting entries works with large numerators and denominators (larger than [`i64`]).
    #[test]
    fn big_negative() {
        let mut matrix = MatZq::new(5, 10, u64::MAX).unwrap();
        let value = Z::from(-i64::MAX - 1);
        matrix.set_entry(0, 0, value).unwrap();

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(
            Z::from((u64::MAX as i128 - i64::MAX as i128) as u64 - 1),
            entry
        );
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let matrix = MatZq::new(5, 10, 7).unwrap();
        let entry: Result<Zq, MathError> = matrix.get_entry(5, 1);

        assert!(entry.is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let matrix = MatZq::new(5, 10, 7).unwrap();
        let entry: Result<Zq, MathError> = matrix.get_entry(1, 100);

        assert!(entry.is_err());
    }

    /// Ensure that the entry is a deep copy and not just a clone of the reference.
    #[test]
    fn memory_test() {
        let mut matrix = MatZq::new(5, 10, u64::MAX).unwrap();
        let value = Zq::from_str(&format!("{} mod {}", u64::MAX - 1, u64::MAX)).unwrap();
        matrix.set_entry(1, 1, value).unwrap();
        let entry = matrix.get_entry(1, 1).unwrap();
        matrix.set_entry(1, 1, Z::from_str("1").unwrap()).unwrap();

        assert_eq!(Z::from_str(&format!("{}", u64::MAX - 1)).unwrap(), entry);
    }

    /// Ensure that getting entries works with different types.
    #[test]
    fn diff_types() {
        let matrix = MatZq::new(5, 10, u64::MAX).unwrap();

        let _: Z = matrix.get_entry(0, 0).unwrap();
        let _: Zq = matrix.get_entry(0, 0).unwrap();
    }
}

#[cfg(test)]
mod test_get_num {
    use crate::{
        integer_mod_q::MatZq,
        traits::{GetNumColumns, GetNumRows},
    };

    /// Ensure that the getter for rows works correctly.
    #[test]
    fn num_rows() {
        let matrix = MatZq::new(5, 10, 7).unwrap();

        assert_eq!(matrix.get_num_rows(), 5);
    }

    /// Ensure that the getter for columns works correctly.
    #[test]
    fn num_columns() {
        let matrix = MatZq::new(5, 10, 7).unwrap();

        assert_eq!(matrix.get_num_columns(), 10);
    }
}

#[cfg(test)]
mod test_mod {
    use std::str::FromStr;

    use crate::integer_mod_q::{MatZq, Modulus};

    /// Ensure that the getter for columns works correctly.
    #[test]
    fn get_mod() {
        let matrix = MatZq::new(5, 10, 7).unwrap();

        assert_eq!(matrix.get_mod().unwrap(), Modulus::from_str("7").unwrap());
    }
}
