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
use crate::{integer::MatPolyOverZ, integer_mod_q::ModulusPolynomialRingZq};

impl From<(&MatPolyOverZ, &ModulusPolynomialRingZq)> for MatPolynomialRingZq {
    /// Create a new polynomial ring matrix of type [`MatPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `value`: is a tuple of `(matrix, modulus)`
    ///     - `matrix`: defines the polynomial matrix
    ///     - `modulus`: the modulus which defines the ring
    ///
    /// Returns a new polynomial ring matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    /// ```
    fn from(value: (&MatPolyOverZ, &ModulusPolynomialRingZq)) -> Self {
        Self::from_poly_over_z_modulus_polynomial_ring_zq(value.0, value.1)
    }
}

impl MatPolynomialRingZq {
    /// Create a new polynomial ring matrix of type [`MatPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `matrix`: the polynomial matrix
    /// - `modulus`: the modulus which defines the ring
    ///
    /// Returns a new polynomial ring matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_mat, &modulus);
    /// ```
    pub fn from_poly_over_z_modulus_polynomial_ring_zq(
        matrix: &MatPolyOverZ,
        modulus: &ModulusPolynomialRingZq,
    ) -> Self {
        let mut out = Self {
            matrix: matrix.clone(),
            modulus: modulus.clone(),
        };
        out.reduce();
        out
    }
}

#[cfg(test)]
mod test_from_poly_over_z_modulus_polynomial_ring_zq {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    const BITPRIME64: u64 = 18446744073709551557;

    /// ensure that the modulus is applied with a large prime and large coefficients
    #[test]
    fn is_reduced_large() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", BITPRIME64)).unwrap();

        let poly_mat = MatPolyOverZ::from_str(&format!(
            "[[4  {} {} 1 1, 1  42],[0, 2  1 2]]",
            BITPRIME64 + 2,
            u64::MAX
        ))
        .unwrap();
        let poly_ring_mat =
            MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_mat, &modulus);

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  1 58 1, 1  42],[0, 2  1 2]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(
            &cmp_poly_mat,
            &modulus,
        );

        assert_eq!(poly_ring_mat, cmp_poly_ring_mat);
    }

    /// ensure that two ring elements that are instantiated the same way are equal
    #[test]
    fn same_instantiation() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", BITPRIME64)).unwrap();
        let poly_mat = MatPolyOverZ::from_str(&format!(
            "[[4  {} {} 1 1, 1  42],[0, 2  1 2]]",
            BITPRIME64 + 2,
            u64::MAX
        ))
        .unwrap();

        let poly_ring_mat_1 =
            MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_mat, &modulus);
        let poly_ring_mat_2 =
            MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_mat, &modulus);

        assert_eq!(poly_ring_mat_1, poly_ring_mat_2);
    }
}
