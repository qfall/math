// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatPolynomialRingZq`] value from other types.
//!
//! The explicit functions contain the documentation.

use super::MatPolynomialRingZq;
use crate::{integer::MatPolyOverZ, integer_mod_q::ModulusPolynomialRingZq};

impl<Mod: Into<ModulusPolynomialRingZq>> From<(&MatPolyOverZ, Mod)> for MatPolynomialRingZq {
    /// Creates a polynomial ring matrix of type [`MatPolynomialRingZq`] from
    /// a [`MatPolyOverZ`] and a [`ModulusPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `matrix`:the polynomial matrix defining each entry.
    /// - `modulus`:the modulus that is applied to each polynomial.
    ///
    /// Returns a [`ModulusPolynomialRingZq`].
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
    fn from((matrix, modulus): (&MatPolyOverZ, Mod)) -> Self {
        let mut out = Self {
            matrix: matrix.clone(),
            modulus: modulus.into(),
        };
        out.reduce();
        out
    }
}

impl<Mod: Into<ModulusPolynomialRingZq>> From<(MatPolyOverZ, Mod)> for MatPolynomialRingZq {
    /// Creates a polynomial ring matrix of type [`MatPolynomialRingZq`] from
    /// a [`MatPolyOverZ`] and a [`ModulusPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `matrix`:the polynomial matrix defining each entry.
    /// - `modulus`:the modulus that is applied to each polynomial.
    ///
    /// Returns a [`ModulusPolynomialRingZq`].
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
    /// let poly_ring_mat = MatPolynomialRingZq::from((poly_mat, &modulus));
    /// ```
    fn from((matrix, modulus): (MatPolyOverZ, Mod)) -> Self {
        let mut out = MatPolynomialRingZq {
            matrix,
            modulus: modulus.into(),
        };
        out.reduce();
        out
    }
}

impl From<&MatPolynomialRingZq> for MatPolynomialRingZq {
    /// Alias for [`MatPolynomialRingZq::clone`].
    fn from(value: &MatPolynomialRingZq) -> Self {
        value.clone()
    }
}

#[cfg(test)]
mod test_from {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Ensure that the modulus is applied with a large prime and large coefficients
    #[test]
    fn is_reduced_large() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();

        let poly_mat = MatPolyOverZ::from_str(&format!(
            "[[4  {} {} 1 1, 1  42],[0, 2  1 2]]",
            LARGE_PRIME + 2,
            u64::MAX
        ))
        .unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  1 58 1, 1  42],[0, 2  1 2]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));

        assert_eq!(poly_ring_mat, cmp_poly_ring_mat);
    }

    /// Ensure that two ring elements that are instantiated the same way are equal
    #[test]
    fn same_instantiation() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly_mat = MatPolyOverZ::from_str(&format!(
            "[[4  {} {} 1 1, 1  42],[0, 2  1 2]]",
            LARGE_PRIME + 2,
            u64::MAX
        ))
        .unwrap();

        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat, &modulus));

        assert_eq!(poly_ring_mat_1, poly_ring_mat_2);
    }

    /// Ensure that from works for different dimensions
    #[test]
    fn different_dimensions() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("3  1 9 12 mod {LARGE_PRIME}")).unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[2  1 8],[2  1 2]]").unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str("[[2  1 8, 1  42, 0],[0, 2  1 2, 1  17]]").unwrap();
        let poly_mat_3 = MatPolyOverZ::from_str("[[2  1 8]]").unwrap();

        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
        let poly_ring_mat_3 = MatPolynomialRingZq::from((&poly_mat_3, &modulus));

        assert_eq!(poly_ring_mat_1.matrix, poly_mat_1);
        assert_eq!(poly_ring_mat_2.matrix, poly_mat_2);
        assert_eq!(poly_ring_mat_3.matrix, poly_mat_3);
    }
}
