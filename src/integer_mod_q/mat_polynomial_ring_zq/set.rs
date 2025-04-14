// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation to set elements of a [`MatPolynomialRingZq`] matrix.

use super::MatPolynomialRingZq;
use crate::integer_mod_q::PolynomialRingZq;
use crate::macros::for_others::implement_for_owned;
use crate::traits::{MatrixSetSubmatrix, MatrixSwaps};
use crate::utils::index::evaluate_indices_for_matrix;
use crate::{error::MathError, integer::PolyOverZ, traits::MatrixSetEntry};
use flint_sys::fmpz_poly_mat::{
    fmpz_poly_mat_set, fmpz_poly_mat_window_clear, fmpz_poly_mat_window_init,
};
use flint_sys::{fmpz_poly::fmpz_poly_set, fmpz_poly_mat::fmpz_poly_mat_entry};
use std::fmt::Display;
use std::mem::MaybeUninit;

impl MatrixSetEntry<&PolyOverZ> for MatPolynomialRingZq {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if the specified entry is
    /// not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::{MatPolyOverZ, PolyOverZ};
    /// use crate::qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[0, 1  42],[0, 2  1 2]]").unwrap();
    /// let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    /// let value = PolyOverZ::default();
    ///
    /// poly_ring_mat.set_entry(0, 1, &value).unwrap();
    /// poly_ring_mat.set_entry(-1, -1, &value).unwrap();
    ///
    /// let mat_cmp = MatPolynomialRingZq::from((&MatPolyOverZ::new(2, 2), &modulus));
    /// assert_eq!(poly_ring_mat, mat_cmp);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///   if `row` or `column` are greater than the matrix size.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        value: &PolyOverZ,
    ) -> Result<(), MathError> {
        let value = PolynomialRingZq::from((value, self.get_mod()));

        self.set_entry(row, column, value)
    }

    /// Sets the value of a specific matrix entry according to a given `value` of type [`PolyOverZ`]
    /// without checking whether the coordinate is part of the matrix, if the moduli match
    /// or if the entry is reduced.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Safety
    /// To use this function safely, make sure that the selected entry is part
    /// of the matrix. If it is not, memory leaks, unexpected panics, etc. might
    /// occur.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::{MatPolyOverZ, PolyOverZ};
    /// use crate::qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[0, 1  42],[0, 2  1 2]]").unwrap();
    /// let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    /// let value = PolyOverZ::default();
    ///
    /// unsafe {
    ///     poly_ring_mat.set_entry_unchecked(0, 1, &value);
    ///     poly_ring_mat.set_entry_unchecked(1, 1, &value);
    /// }
    ///
    /// let mat_cmp = MatPolynomialRingZq::from((&MatPolyOverZ::new(2, 2), &modulus));
    /// assert_eq!(poly_ring_mat, mat_cmp);
    /// ```
    unsafe fn set_entry_unchecked(&mut self, row: i64, column: i64, value: &PolyOverZ) {
        unsafe {
            let entry = fmpz_poly_mat_entry(&self.matrix.matrix, row, column);
            fmpz_poly_set(entry, &value.poly)
        };
    }
}

impl MatrixSetEntry<&PolynomialRingZq> for MatPolynomialRingZq {
    /// Sets the value of a specific matrix entry according to a given `value` of type [`PolynomialRingZq`].
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if the specified entry is
    /// not part of the matrix or the moduli are different.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolynomialRingZq};
    /// use qfall_math::integer::{MatPolyOverZ, PolyOverZ};
    /// use crate::qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[0, 1  42],[0, 2  1 2]]").unwrap();
    /// let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    /// let value = PolynomialRingZq::from((&PolyOverZ::default(), &modulus));
    ///
    /// poly_ring_mat.set_entry(0, 1, &value).unwrap();
    /// poly_ring_mat.set_entry(-1, -1, &value).unwrap();
    ///
    /// let mat_cmp = MatPolynomialRingZq::from((&MatPolyOverZ::new(2, 2), &modulus));
    /// assert_eq!(poly_ring_mat, mat_cmp);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///   if `row` or `column` are greater than the matrix size.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`]
    ///   if the moduli are different.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        value: &PolynomialRingZq,
    ) -> Result<(), MathError> {
        if self.modulus != value.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Modulus of matrix: '{}'. Modulus of value: '{}'.
                If the modulus should be ignored please convert into a Z beforehand.",
                self.modulus, value.modulus
            )));
        }

        let (row_i64, column_i64) = evaluate_indices_for_matrix(self, row, column)?;

        unsafe { self.set_entry_unchecked(row_i64, column_i64, value) };

        Ok(())
    }

    /// Sets the value of a specific matrix entry according to a given `value` of type [`PolynomialRingZq`]
    /// without checking whether the coordinate is part of the matrix or if the moduli match.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    /// - `value`: specifies the value to which the entry is set
    ///
    /// # Safety
    /// To use this function safely, make sure that the selected entry is part
    /// of the matrix. If it is not, memory leaks, unexpected panics, etc. might
    /// occur.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolynomialRingZq};
    /// use qfall_math::integer::{MatPolyOverZ, PolyOverZ};
    /// use crate::qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[0, 1  42],[0, 2  1 2]]").unwrap();
    /// let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    /// let value = PolynomialRingZq::from((&PolyOverZ::default(), &modulus));
    ///
    /// unsafe {
    ///     poly_ring_mat.set_entry_unchecked(0, 1, &value);
    ///     poly_ring_mat.set_entry_unchecked(1, 1, &value);
    /// }
    ///
    /// let mat_cmp = MatPolynomialRingZq::from((&MatPolyOverZ::new(2, 2), &modulus));
    /// assert_eq!(poly_ring_mat, mat_cmp);
    /// ```
    unsafe fn set_entry_unchecked(&mut self, row: i64, column: i64, value: &PolynomialRingZq) {
        unsafe {
            let entry = fmpz_poly_mat_entry(&self.matrix.matrix, row, column);
            fmpz_poly_set(entry, &value.poly.poly)
        };
    }
}

implement_for_owned!(PolyOverZ, MatPolynomialRingZq, MatrixSetEntry);
implement_for_owned!(PolynomialRingZq, MatPolynomialRingZq, MatrixSetEntry);

impl MatrixSetSubmatrix for MatPolynomialRingZq {
    unsafe fn set_submatrix_unchecked(
        &mut self,
        row_self_start: i64,
        col_self_start: i64,
        row_self_end: i64,
        col_self_end: i64,
        other: &Self,
        row_other_start: i64,
        col_other_start: i64,
        row_other_end: i64,
        col_other_end: i64,
    ) {
        {
            let mut window_self = MaybeUninit::uninit();
            // The memory for the elements of window is shared with self.
            unsafe {
                fmpz_poly_mat_window_init(
                    window_self.as_mut_ptr(),
                    &self.matrix.matrix,
                    row_self_start,
                    col_self_start,
                    row_self_end,
                    col_self_end,
                )
            };
            let mut window_other = MaybeUninit::uninit();
            // The memory for the elements of window is shared with other.
            unsafe {
                fmpz_poly_mat_window_init(
                    window_other.as_mut_ptr(),
                    &other.matrix.matrix,
                    row_other_start,
                    col_other_start,
                    row_other_end,
                    col_other_end,
                )
            };
            unsafe {
                // TODO: this should not be mutable for the other window
                fmpz_poly_mat_set(window_self.as_mut_ptr(), window_other.as_mut_ptr());

                // Clears the matrix window and releases any memory that it uses. Note that
                // the memory to the underlying matrix that window points to is not freed
                fmpz_poly_mat_window_clear(window_self.as_mut_ptr());
                fmpz_poly_mat_window_clear(window_other.as_mut_ptr());
            }
        }
    }
}

impl MatrixSwaps for MatPolynomialRingZq {
    /// Swaps two entries of the specified matrix.
    ///
    /// Parameters:
    /// - `row_0`: specifies the row, in which the first entry is located
    /// - `col_0`: specifies the column, in which the first entry is located
    /// - `row_1`: specifies the row, in which the second entry is located
    /// - `col_1`: specifies the column, in which the second entry is located
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified entries is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::traits::MatrixSwaps;
    ///
    /// let mut matrix = MatPolynomialRingZq::new(4, 3, ModulusPolynomialRingZq::from((3, 17)));
    /// matrix.swap_entries(0, 0, 2, 1);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    ///   if row or column are greater than the matrix size.
    fn swap_entries(
        &mut self,
        row_0: impl TryInto<i64> + Display,
        col_0: impl TryInto<i64> + Display,
        row_1: impl TryInto<i64> + Display,
        col_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        self.matrix.swap_entries(row_0, col_0, row_1, col_1)
    }

    /// Swaps two columns of the specified matrix.
    ///
    /// Parameters:
    /// - `col_0`: specifies the first column which is swapped with the second one
    /// - `col_1`: specifies the second column which is swapped with the first one
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified columns is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::traits::MatrixSwaps;
    ///
    /// let mut matrix = MatPolynomialRingZq::new(4, 3, ModulusPolynomialRingZq::from((3, 17)));
    /// matrix.swap_columns(0, 2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///   if one of the given columns is not in the matrix.
    fn swap_columns(
        &mut self,
        col_0: impl TryInto<i64> + Display,
        col_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        self.matrix.swap_columns(col_0, col_1)
    }

    /// Swaps two rows of the specified matrix.
    ///
    /// Parameters:
    /// - `row_0`: specifies the first row which is swapped with the second one
    /// - `row_1`: specifies the second row which is swapped with the first one
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if one of the specified rows is not part of the matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::traits::MatrixSwaps;
    ///
    /// let mut matrix = MatPolynomialRingZq::new(4, 3, ModulusPolynomialRingZq::from((3, 17)));
    /// matrix.swap_rows(0, 2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    ///   if one of the given rows is not in the matrix.
    fn swap_rows(
        &mut self,
        row_0: impl TryInto<i64> + Display,
        row_1: impl TryInto<i64> + Display,
    ) -> Result<(), MathError> {
        self.matrix.swap_rows(row_0, row_1)
    }
}

impl MatPolynomialRingZq {
    /// Swaps the `i`-th column with the `n-i`-th column for all `i <= n/2`
    /// of the specified matrix with `n` columns.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    ///
    /// let mut matrix = MatPolynomialRingZq::new(4, 3, ModulusPolynomialRingZq::from((3, 17)));
    /// matrix.reverse_columns();
    /// ```
    pub fn reverse_columns(&mut self) {
        self.matrix.reverse_columns()
    }

    /// Swaps the `i`-th row with the `n-i`-th row for all `i <= n/2`
    /// of the specified matrix with `n` rows.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    ///
    /// let mut matrix = MatPolynomialRingZq::new(4, 3, ModulusPolynomialRingZq::from((3, 17)));
    /// matrix.reverse_rows();
    /// ```
    pub fn reverse_rows(&mut self) {
        self.matrix.reverse_rows()
    }
}

#[cfg(test)]
mod test_setter {
    use crate::{
        integer::{MatPolyOverZ, PolyOverZ},
        integer_mod_q::{
            MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq,
        },
        traits::{MatrixGetEntry, MatrixSetEntry, MatrixSetSubmatrix},
    };
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Ensure that setting entries works with standard numbers.
    #[test]
    fn standard_value() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let value = PolyOverZ::default();

        poly_ring_mat.set_entry(1, 1, value).unwrap();

        let entry_z: PolyOverZ = poly_ring_mat.get_entry(1, 1).unwrap();
        let entry_zq: PolynomialRingZq = poly_ring_mat.get_entry(1, 1).unwrap();

        assert_eq!("0", entry_z.to_string());
        assert_eq!("0", entry_zq.poly.to_string());
        assert_eq!("4  1 0 0 1 mod 17", entry_zq.modulus.to_string());
    }

    /// Ensure that when using a [`PolyOverZ`] the set entry is actually reduced by the
    /// modulus.
    #[test]
    fn set_entry_reduced() {
        let id_mat = MatPolyOverZ::identity(2, 2);
        let modulus = PolyOverZq::from_str("5  1 0 0 0 1 mod 17").unwrap();

        let mut poly_mat = MatPolynomialRingZq::from((id_mat, modulus));

        poly_mat
            .set_entry(0, 0, PolyOverZ::from_str("5  -1 0 0 0 16").unwrap())
            .unwrap();

        let entry: PolyOverZ = poly_mat.get_entry(0, 0).unwrap();
        assert!(entry.is_zero());
    }

    /// Ensure that setting entries works with large numbers.
    #[test]
    fn large_positive() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly_mat =
            MatPolyOverZ::from_str(&format!("[[2  1 1, 1  42],[0, 2  {} 2]]", i64::MAX)).unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let value = PolyOverZ::from_str(&format!("3  1 {} 1", i64::MAX)).unwrap();

        poly_ring_mat.set_entry(0, 0, value).unwrap();

        let entry_z: PolyOverZ = poly_ring_mat.get_entry(0, 0).unwrap();
        let entry_zq: PolynomialRingZq = poly_ring_mat.get_entry(0, 0).unwrap();

        assert_eq!(format!("3  1 {} 1", i64::MAX), entry_z.to_string());
        assert_eq!(format!("3  1 {} 1", i64::MAX), entry_zq.poly.to_string());
        assert_eq!(
            format!("4  1 0 0 1 mod {LARGE_PRIME}"),
            entry_zq.modulus.to_string()
        );
    }

    /// Ensure that setting entries works with referenced large numbers.
    #[test]
    fn large_positive_ref() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly_mat = MatPolyOverZ::from_str(&format!(
            "[[2  1 1, 1  42, 0],[0, 2  {} 2, 1  1]]",
            i64::MAX
        ))
        .unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let value = PolyOverZ::from_str(&format!("3  1 {} 1", i64::MAX)).unwrap();

        poly_ring_mat.set_entry(0, 0, &value).unwrap();

        let entry_z: PolyOverZ = poly_ring_mat.get_entry(0, 0).unwrap();
        let entry_zq: PolynomialRingZq = poly_ring_mat.get_entry(0, 0).unwrap();

        assert_eq!(format!("3  1 {} 1", i64::MAX), entry_z.to_string());
        assert_eq!(format!("3  1 {} 1", i64::MAX), entry_zq.poly.to_string());
        assert_eq!(
            format!("4  1 0 0 1 mod {LARGE_PRIME}"),
            entry_zq.modulus.to_string()
        );
    }

    /// Ensure that setting entries works with large negative numbers.
    #[test]
    fn large_negative() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly_mat = MatPolyOverZ::from_str(&format!(
            "[[2  1 1, 1  42],[0, 2  {} 2],[1  2, 0]]",
            i64::MAX
        ))
        .unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let value = PolyOverZ::from_str(&format!("3  1 {} 1", i64::MIN)).unwrap();

        poly_ring_mat.set_entry(0, 1, value).unwrap();

        let entry_z: PolyOverZ = poly_ring_mat.get_entry(0, 1).unwrap();
        let entry_zq: PolynomialRingZq = poly_ring_mat.get_entry(0, 1).unwrap();

        assert_eq!(
            format!("3  1 {} 1", LARGE_PRIME - i64::MIN as u64),
            entry_z.to_string()
        );
        assert_eq!(
            format!("3  1 {} 1", LARGE_PRIME - i64::MIN as u64),
            entry_zq.poly.to_string()
        );
        assert_eq!(
            format!("4  1 0 0 1 mod {LARGE_PRIME}"),
            entry_zq.modulus.to_string()
        );
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let value = PolyOverZ::default();

        assert!(poly_ring_mat.set_entry(2, 0, &value).is_err());
        assert!(poly_ring_mat.set_entry(-3, 0, value).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat =
            MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42, 0],[0, 2  1 2, 1  17]]").unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let value = PolyOverZ::default();

        assert!(poly_ring_mat.set_entry(0, 3, &value).is_err());
        assert!(poly_ring_mat.set_entry(0, -4, value).is_err());
    }

    /// Ensure that differing moduli result in an error.
    #[test]
    fn modulus_error() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let modulus_2 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus_1));
        let value = PolynomialRingZq::from((&PolyOverZ::default(), &modulus_2));

        assert!(poly_ring_mat.set_entry(1, 1, value).is_err());
    }

    /// Ensures that setting columns works fine for small entries.
    #[test]
    fn column_small_entries() {
        let mut mat_1 =
            MatPolynomialRingZq::from_str("[[0, 1  2, 0],[0, 1  5, 1  6]] / 2  1 1 mod 6").unwrap();
        let mat_2 = MatPolynomialRingZq::from_str("[[0],[1  -1]] / 2  1 1 mod 6").unwrap();
        let cmp =
            MatPolynomialRingZq::from_str("[[0, 0, 0],[0, 1  -1, 1  6]] / 2  1 1 mod 6").unwrap();

        mat_1.set_column(1, &mat_2, 0).unwrap();

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting columns works fine for large entries.
    #[test]
    fn column_large_entries() {
        let mut mat_1 = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]] / 2  1 1 mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX-1,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 1  {}],[1  {}, 0],[1  7, 1  -1]] / 2  1 1 mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[0, 1  4, 1  {}, 1  5],[1  -1, 1  6, 2  8 9, 0]] / 2  1 1 mod {}",
            i64::MIN,
            u64::MAX-1,
            u64::MAX
        ))
        .unwrap();

        mat_1.set_column(0, &mat_2, 1).unwrap();

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting the column to itself does not change anything.
    #[test]
    fn column_swap_same_entry() {
        let mut mat_1 = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]] / 2  1 1 mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX-1,
            u64::MAX
        ))
        .unwrap();
        let cmp = mat_1.clone();

        mat_1.set_column(0, &cmp, 0).unwrap();
        mat_1.set_column(1, &cmp, 1).unwrap();

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that `set_column` returns an error if one of the specified columns is out of bounds.
    #[test]
    fn column_out_of_bounds() {
        let mut mat_1 =
            MatPolynomialRingZq::from_str("[[0, 0],[0, 0],[0, 0],[0, 0],[0, 0]] / 2  1 1 mod 6")
                .unwrap();
        let mat_2 = mat_1.clone();

        assert!(mat_1.set_column(-3, &mat_2, 0).is_err());
        assert!(mat_1.set_column(2, &mat_2, 0).is_err());
        assert!(mat_1.set_column(1, &mat_2, -3).is_err());
        assert!(mat_1.set_column(1, &mat_2, 2).is_err());
    }

    /// Ensures that mismatching row dimensions result in an error.
    #[test]
    fn column_mismatching_columns() {
        let mut mat_1 =
            MatPolynomialRingZq::from_str("[[0, 0],[0, 0],[0, 0],[0, 0],[0, 0]] / 2  1 1 mod 6")
                .unwrap();
        let mat_2 = MatPolynomialRingZq::from_str("[[0, 0],[0, 0]] / 2  1 1 mod 6").unwrap();

        assert!(mat_1.set_column(0, &mat_2, 0).is_err());
        assert!(mat_1.set_column(1, &mat_2, 1).is_err());
    }

    /// Ensures that mismatching moduli result in an error.
    #[test]
    fn column_mismatching_moduli() {
        let mut mat_1 =
            MatPolynomialRingZq::from_str("[[0, 0],[0, 0],[0, 0]] / 2  1 1 mod 6").unwrap();
        let mat_2 = MatPolynomialRingZq::from_str("[[0, 0],[0, 0],[0, 0]] / 2  1 1 mod 7").unwrap();

        assert!(mat_1.set_column(0, &mat_2, 0).is_err());
        assert!(mat_1.set_column(1, &mat_2, 1).is_err());
    }

    /// Ensures that setting rows works fine for small entries.
    #[test]
    fn row_small_entries() {
        let mut mat_1 =
            MatPolynomialRingZq::from_str("[[0, 1  2, 0],[0, 2  5 6, 0]] / 2  1 1 mod 6").unwrap();
        let mat_2 = MatPolynomialRingZq::from_str("[[0, 1  -1, 1  2]] / 2  1 1 mod 6").unwrap();
        let cmp = MatPolynomialRingZq::from_str("[[0, 1  2, 0],[0, 1  -1, 1  2]] / 2  1 1 mod 6")
            .unwrap();

        let _ = mat_1.set_row(1, &mat_2, 0);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting rows works fine for large entries.
    #[test]
    fn row_large_entries() {
        let mut mat_1 = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]] / 2  1 1 mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX-1,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatPolynomialRingZq::from_str(&format!(
            "[[0, 0, 0, 0],[1  {}, 0, 1  {}, 0]] / 2  1 1 mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}, 0, 1  {}, 0],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]] / 2  1 1 mod {}",
            i64::MIN,
            i64::MAX,
            i64::MAX,
            u64::MAX-1,
            u64::MAX
        ))
        .unwrap();

        let _ = mat_1.set_row(0, &mat_2, 1);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that setting the rows to itself does not change anything.
    #[test]
    fn row_swap_same_entry() {
        let mut mat_1 = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}, 1  1, 1  3, 1  4],[1  {}, 1  4, 1  {}, 1  5],[1  7, 1  6, 2  8 9, 0]] / 2  1 1 mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX-1,
            u64::MAX
        ))
        .unwrap();
        let cmp = mat_1.clone();

        let _ = mat_1.set_row(0, &cmp, 0);
        let _ = mat_1.set_row(1, &cmp, 1);

        assert_eq!(cmp, mat_1);
    }

    /// Ensures that `set_row` returns an error if one of the specified rows is out of bounds.
    #[test]
    fn row_out_of_bounds() {
        let mut mat_1 =
            MatPolynomialRingZq::from_str("[[0, 0],[0, 0],[0, 0],[0, 0],[0, 0]] / 2  1 1 mod 6")
                .unwrap();
        let mat_2 = mat_1.clone();

        assert!(mat_1.set_row(-6, &mat_2, 0).is_err());
        assert!(mat_1.set_row(5, &mat_2, 0).is_err());
        assert!(mat_1.set_row(2, &mat_2, -6).is_err());
        assert!(mat_1.set_row(2, &mat_2, 5).is_err());
    }

    /// Ensures that mismatching column dimensions result in an error.
    #[test]
    fn row_mismatching_columns() {
        let mut mat_1 =
            MatPolynomialRingZq::from_str("[[0, 0],[0, 0],[0, 0]] / 2  1 1 mod 6").unwrap();
        let mat_2 = MatPolynomialRingZq::from_str("[[0, 0, 0],[0, 0, 0],[0, 0, 0]] / 2  1 1 mod 6")
            .unwrap();

        assert!(mat_1.set_row(0, &mat_2, 0).is_err());
        assert!(mat_1.set_row(1, &mat_2, 1).is_err());
    }

    /// Ensures that mismatching moduli result in an error.
    #[test]
    fn row_mismatching_moduli() {
        let mut mat_1 =
            MatPolynomialRingZq::from_str("[[0, 0],[0, 0],[0, 0]] / 2  1 1 mod 6").unwrap();
        let mat_2 = MatPolynomialRingZq::from_str("[[0, 0],[0, 0],[0, 0]] / 2  1 1 mod 7").unwrap();

        assert!(mat_1.set_row(0, &mat_2, 0).is_err());
        assert!(mat_1.set_row(1, &mat_2, 1).is_err());
    }
}

#[cfg(test)]
mod test_swaps {
    use super::MatPolynomialRingZq;
    use crate::{
        integer_mod_q::ModulusPolynomialRingZq,
        traits::{MatrixGetSubmatrix, MatrixSwaps},
    };
    use std::str::FromStr;

    // Since swapping functions only call the existing tested functions for [`MatPolyOverZ`](crate::integer::MatPolyOverZ),
    // we omit some tests that are already covered.

    /// Ensures that swapping entries works
    #[test]
    fn entries_swapping() {
        let mut matrix = MatPolynomialRingZq::from_str(
            "[[1  1, 1  2, 1  3],[1  4, 2  5 6, 0]] / 3  1 2 3 mod 17",
        )
        .unwrap();
        let cmp = MatPolynomialRingZq::from_str(
            "[[1  1, 2  5 6, 1  3],[1  4, 1  2, 0]] / 3  1 2 3 mod 17",
        )
        .unwrap();

        let _ = matrix.swap_entries(1, 1, 0, 1);

        assert_eq!(cmp, matrix);
    }

    /// Ensures that `swap_entries` returns an error if one of the specified entries is out of bounds
    #[test]
    fn entries_out_of_bounds() {
        let mut matrix = MatPolynomialRingZq::new(5, 2, ModulusPolynomialRingZq::from((3, 17)));

        assert!(matrix.swap_entries(-6, 0, 0, 0).is_err());
        assert!(matrix.swap_entries(0, -3, 0, 0).is_err());
        assert!(matrix.swap_entries(0, 0, 5, 0).is_err());
        assert!(matrix.swap_entries(0, 5, 0, 0).is_err());
    }

    /// Ensure that `swap_entries` can properly handle negative indexing.
    #[test]
    fn entries_negative_indexing() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let mut matrix = MatPolynomialRingZq::identity(2, 2, modulus);

        matrix.swap_entries(-2, -2, -2, -1).unwrap();
        assert_eq!(
            "[[0, 1  1],[0, 1  1]] / 3  1 0 1 mod 17",
            matrix.to_string()
        );
    }

    /// Ensures that swapping columns works fine for small entries
    #[test]
    fn columns_swapping() {
        let mut matrix = MatPolynomialRingZq::from_str(
            "[[1  1, 1  2, 1  3],[1  4, 1  5, 1  6]] / 3  1 2 3 mod 17",
        )
        .unwrap();
        let cmp_vec_0 = MatPolynomialRingZq::from_str("[[1  1],[1  4]] / 3  1 2 3 mod 17").unwrap();
        let cmp_vec_1 = MatPolynomialRingZq::from_str("[[1  3],[1  6]] / 3  1 2 3 mod 17").unwrap();
        let cmp_vec_2 = MatPolynomialRingZq::from_str("[[1  2],[1  5]] / 3  1 2 3 mod 17").unwrap();

        let _ = matrix.swap_columns(1, 2);

        assert_eq!(cmp_vec_0, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_2, matrix.get_column(2).unwrap());
    }

    /// Ensures that `swap_columns` returns an error if one of the specified columns is out of bounds
    #[test]
    fn column_out_of_bounds() {
        let mut matrix = MatPolynomialRingZq::new(5, 2, ModulusPolynomialRingZq::from((3, 17)));

        assert!(matrix.swap_columns(-6, 0).is_err());
        assert!(matrix.swap_columns(0, -6).is_err());
        assert!(matrix.swap_columns(5, 0).is_err());
        assert!(matrix.swap_columns(0, 5).is_err());
    }

    /// Ensures that swapping rows works
    #[test]
    fn rows_swapping() {
        let mut matrix =
            MatPolynomialRingZq::from_str("[[1  1, 1  2],[1  3, 2  4 5]] / 3  1 2 3 mod 17")
                .unwrap();
        let cmp_vec_0 =
            MatPolynomialRingZq::from_str("[[1  3, 2  4 5]] / 3  1 2 3 mod 17").unwrap();
        let cmp_vec_1 = MatPolynomialRingZq::from_str("[[1  1, 1  2]] / 3  1 2 3 mod 17").unwrap();

        let _ = matrix.swap_rows(1, 0);

        assert_eq!(cmp_vec_0, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_row(1).unwrap());
    }

    /// Ensures that `swap_rows` returns an error if one of the specified rows is out of bounds
    #[test]
    fn row_out_of_bounds() {
        let mut matrix = MatPolynomialRingZq::new(2, 4, ModulusPolynomialRingZq::from((3, 17)));

        assert!(matrix.swap_rows(-3, 0).is_err());
        assert!(matrix.swap_rows(0, -3).is_err());
        assert!(matrix.swap_rows(4, 0).is_err());
        assert!(matrix.swap_rows(0, 4).is_err());
    }
}

#[cfg(test)]
mod test_reverses {
    use super::MatPolynomialRingZq;
    use crate::traits::MatrixGetSubmatrix;
    use std::str::FromStr;

    // Since reversing functions only call the existing tested functions for [`MatPolyOverZ`](crate::integer::MatPolyOverZ),
    // we omit some tests that are already covered.

    /// Ensures that reversing columns works fine for small entries
    #[test]
    fn columns_reversing() {
        let mut matrix = MatPolynomialRingZq::from_str(
            "[[1  1, 1  2, 2  3 4],[0, 1  5, 1  6]] / 3  1 2 3 mod 17",
        )
        .unwrap();
        let cmp_vec_0 = MatPolynomialRingZq::from_str("[[1  1],[0]] / 3  1 2 3 mod 17").unwrap();
        let cmp_vec_1 = MatPolynomialRingZq::from_str("[[1  2],[1  5]] / 3  1 2 3 mod 17").unwrap();
        let cmp_vec_2 =
            MatPolynomialRingZq::from_str("[[2  3 4],[1  6]] / 3  1 2 3 mod 17").unwrap();

        matrix.reverse_columns();

        assert_eq!(cmp_vec_2, matrix.get_column(0).unwrap());
        assert_eq!(cmp_vec_1, matrix.get_column(1).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_column(2).unwrap());
    }

    /// Ensures that reversing rows works fine for small entries
    #[test]
    fn rows_reversing() {
        let mut matrix =
            MatPolynomialRingZq::from_str("[[1  1, 1  2],[2  3 4, 0]] / 3  1 2 3 mod 17").unwrap();
        let cmp_vec_0 = MatPolynomialRingZq::from_str("[[1  1, 1  2]] / 3  1 2 3 mod 17").unwrap();
        let cmp_vec_1 = MatPolynomialRingZq::from_str("[[2  3 4, 0]] / 3  1 2 3 mod 17").unwrap();

        matrix.reverse_rows();

        assert_eq!(cmp_vec_1, matrix.get_row(0).unwrap());
        assert_eq!(cmp_vec_0, matrix.get_row(1).unwrap());
    }
}
