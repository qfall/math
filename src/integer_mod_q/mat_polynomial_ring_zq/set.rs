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
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    /// let value = PolyOverZ::default();
    ///
    /// poly_ring_mat.set_entry(1, 1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    fn set_entry(
        &mut self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
        value: &PolyOverZ,
    ) -> Result<(), MathError> {
        let (row_i64, column_i64) = evaluate_indices_for_matrix(self, row, column)?;

        unsafe {
            let entry = fmpz_poly_mat_entry(&self.matrix.matrix, row_i64, column_i64);
            fmpz_poly_set(entry, &value.poly)
        };

        Ok(())
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
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    /// let value = PolynomialRingZq::from((&PolyOverZ::default(), &modulus));
    ///
    /// poly_ring_mat.set_entry(1, 1, &value).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if the number of rows or columns is greater than the matrix or negative.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`]
    /// if the moduli are different.
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
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolynomialRingZq},
        traits::{GetEntry, SetEntry},
    };
    use std::str::FromStr;

    const BITPRIME64: u64 = u64::MAX - 58;

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

    /// Ensure that setting entries works with large numbers.
    #[test]
    fn big_positive() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", BITPRIME64)).unwrap();
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
            format!("4  1 0 0 1 mod {}", BITPRIME64),
            entry_zq.modulus.to_string()
        );
    }

    /// Ensure that setting entries works with referenced large numbers.
    #[test]
    fn big_positive_ref() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", BITPRIME64)).unwrap();
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
            format!("4  1 0 0 1 mod {}", BITPRIME64),
            entry_zq.modulus.to_string()
        );
    }

    /// Ensure that setting entries works with large negative numbers.
    #[test]
    fn big_negative() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", BITPRIME64)).unwrap();
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

        assert_eq!(format!("3  1 {} 1", i64::MIN), entry_z.to_string());
        assert_eq!(format!("3  1 {} 1", i64::MIN), entry_zq.poly.to_string());
        assert_eq!(
            format!("4  1 0 0 1 mod {}", BITPRIME64),
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
        assert!(poly_ring_mat.set_entry(-1, 0, value).is_err());
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
        assert!(poly_ring_mat.set_entry(0, -1, value).is_err());
    }

    /// Ensure that differing moduli result in an error.
    #[test]
    fn modulus_error() {
        let modulus1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let modulus2 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus1));
        let value = PolynomialRingZq::from((&PolyOverZ::default(), &modulus2));

        assert!(poly_ring_mat.set_entry(1, 1, value).is_err());
    }
}
