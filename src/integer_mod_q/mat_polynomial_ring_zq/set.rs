// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation to set entries of a [`MatPolynomialRingZq`] matrix.

use super::MatPolynomialRingZq;
use crate::integer_mod_q::PolynomialRingZq;
use crate::macros::for_others::implement_for_owned;
use crate::utils::index::evaluate_indices_for_matrix;
use crate::{error::MathError, integer::PolyOverZ, traits::SetEntry};
use flint_sys::{fmpz_poly::fmpz_poly_set, fmpz_poly_mat::fmpz_poly_mat_entry};
use std::fmt::Display;

impl SetEntry<&PolyOverZ> for MatPolynomialRingZq {
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
    ///     if `row` or `column` are greater than the matrix size.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        value: &PolyOverZ,
    ) -> Result<(), MathError> {
        let value = PolynomialRingZq::from((value, self.get_mod()));

        self.set_entry(row, column, value)
    }
}

impl SetEntry<&PolynomialRingZq> for MatPolynomialRingZq {
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
    ///     if `row` or `column` are greater than the matrix size.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`]
    ///     if the moduli are different.
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

        unsafe {
            let entry = fmpz_poly_mat_entry(&self.matrix.matrix, row_i64, column_i64);
            fmpz_poly_set(entry, &value.poly.poly)
        };

        Ok(())
    }
}

implement_for_owned!(PolyOverZ, MatPolynomialRingZq, SetEntry);
implement_for_owned!(PolynomialRingZq, MatPolynomialRingZq, SetEntry);

#[cfg(test)]
mod test_setter {
    use crate::{
        integer::{MatPolyOverZ, PolyOverZ},
        integer_mod_q::{
            MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq,
        },
        traits::{GetEntry, SetEntry},
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
}
