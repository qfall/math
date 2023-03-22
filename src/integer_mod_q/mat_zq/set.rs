//! Implementation to set entries from a [`MatZq`] matrix.

use super::MatZq;
use crate::error::MathError;
use crate::integer::Z;
use crate::integer_mod_q::Zq;
use crate::macros::for_others::{
    implement_for_others_set_entry, implement_set_entry_borrowed_to_owned,
};
use crate::traits::SetEntry;
use crate::utils::coordinate::evaluate_coordinates;
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_set_entry;
use std::fmt::Display;

impl SetEntry<&Z> for MatZq {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`Z`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::MatZq;
    /// use math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZq::new(5, 10, 7).unwrap();
    /// let value = Z::from(5);
    /// matrix.set_entry_ref_z(1, 1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
        value: &Z,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_coordinates(self, row, column)?;

        // Calculate mod q before adding the entry to the matrix.
        let value: Zq = Zq::from_z_modulus(value, &self.get_mod()?);

        unsafe {
            // get entry and replace the pointed at value with the specified value
            fmpz_mod_mat_set_entry(&mut self.matrix, row_i64, column_i64, &value.value.value)
        }

        Ok(())
    }
}

impl SetEntry<&Zq> for MatZq {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`Z`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::MatZq;
    /// use math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZq::new(5, 10, 7).unwrap();
    /// let value = Z::from(5);
    /// matrix.set_entry_ref_z(1, 1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display + Copy,
        column: impl TryInto<i64> + Display + Copy,
        value: &Zq,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_coordinates(self, row, column)?;

        // TODO error when modulus not equal

        unsafe {
            // get entry and replace the pointed at value with the specified value
            fmpz_mod_mat_set_entry(&mut self.matrix, row_i64, column_i64, &value.value.value)
        }

        Ok(())
    }
}

implement_set_entry_borrowed_to_owned!(Z, MatZq);
implement_set_entry_borrowed_to_owned!(Zq, MatZq);

implement_for_others_set_entry!(i64, Z, MatZq);
implement_for_others_set_entry!(i32, Z, MatZq);
implement_for_others_set_entry!(i16, Z, MatZq);
implement_for_others_set_entry!(i8, Z, MatZq);
implement_for_others_set_entry!(u64, Z, MatZq);
implement_for_others_set_entry!(u32, Z, MatZq);
implement_for_others_set_entry!(u16, Z, MatZq);
implement_for_others_set_entry!(u8, Z, MatZq);

#[cfg(test)]
mod test_setter {
    use crate::{integer::Z, integer_mod_q::MatZq, traits::SetEntry};
    use std::str::FromStr;

    /// Ensure that setting entries works with standard numbers.
    #[test]
    fn standard_value() {
        let mut matrix = MatZq::new(5, 10, 7).unwrap();
        let value = Z::from_str("869").unwrap();
        matrix.set_entry(4, 7, value).unwrap();
    }
}
