// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatPolynomialRingZq`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::MatPolynomialRingZq;
use crate::{error::MathError, integer::MatPolyOverZ, integer_mod_q::ModulusPolynomialRingZq};
use std::fmt::Display;

impl MatPolynomialRingZq {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns,
    /// zeros as entries and `modulus` as the modulus.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    /// - `modulus`: the common modulus of the matrix entries
    ///
    /// Returns a [`MatPolynomialRingZq`] or an error, if the number of rows or columns is
    /// less than `1`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
    ///
    /// let matrix = MatPolynomialRingZq::new(5, 10, &modulus).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the number of rows or columns is `0`.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is negative or it does not fit into an [`i64`].
    #[allow(dead_code)]
    pub fn new(
        num_rows: impl TryInto<i64> + Display + Copy,
        num_cols: impl TryInto<i64> + Display + Copy,
        modulus: &ModulusPolynomialRingZq,
    ) -> Result<Self, MathError> {
        let matrix = MatPolyOverZ::new(num_rows, num_cols)?;

        Ok(MatPolynomialRingZq {
            matrix,
            modulus: modulus.clone(),
        })
    }
}

#[cfg(test)]
mod test_new {
    use crate::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq};
    use std::str::FromStr;

    const BITPRIME64: u64 = 18446744073709551557;

    /// Ensure that initialization works.
    #[test]
    fn initialization() {
        let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();

        assert!(MatPolynomialRingZq::new(2, 2, &modulus).is_ok());
    }

    // TODO: add a test for zero entries

    /// Ensure that a new zero matrix fails with `0` as input.
    #[test]
    fn error_zero() {
        let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();

        let matrix1 = MatPolynomialRingZq::new(0, 1, &modulus);
        let matrix2 = MatPolynomialRingZq::new(1, 0, &modulus);
        let matrix3 = MatPolynomialRingZq::new(0, 0, &modulus);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
        assert!(matrix3.is_err());
    }

    /// Ensure that the modulus can be large.
    #[test]
    fn large_modulus() {
        let poly_mod =
            PolyOverZq::from_str(&format!("3  1 {} 1 mod {}", i64::MAX, BITPRIME64)).unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();

        assert!(MatPolynomialRingZq::new(2, 2, &modulus).is_ok());
    }
}
