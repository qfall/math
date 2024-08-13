// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`MatPolynomialRingZq`] values.

use super::super::MatPolynomialRingZq;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use std::ops::Mul;

impl Mul for &MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;

    /// Implements the [`Mul`] trait for two [`MatPolynomialRingZq`] values.
    ///
    /// [`Mul`] is implemented for any combination of owned and borrowed [`MatPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
    /// let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
    /// let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
    ///
    /// let poly_ring_mat_3: MatPolynomialRingZq = &poly_ring_mat_1 * &poly_ring_mat_2;
    /// let poly_ring_mat_4: MatPolynomialRingZq = poly_ring_mat_1 * poly_ring_mat_2;
    /// let poly_ring_mat_5: MatPolynomialRingZq = &poly_ring_mat_3 * poly_ring_mat_4;
    /// let poly_ring_mat_6: MatPolynomialRingZq = poly_ring_mat_3 * &poly_ring_mat_5;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    /// - if the moduli mismatch.
    fn mul(self, other: Self) -> Self::Output {
        self.mul_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(
    Mul,
    mul,
    MatPolynomialRingZq,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Mul,
    mul,
    MatPolynomialRingZq,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);

impl MatPolynomialRingZq {
    /// Implements multiplication for two [`MatPolynomialRingZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
    /// let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
    /// let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
    ///
    /// let poly_ring_mat_3: MatPolynomialRingZq = poly_ring_mat_1.mul_safe(&poly_ring_mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`MathError::MismatchingMatrixDimension`] if the dimensions of `self`
    ///      and `other` do not match for multiplication.
    /// - Returns a [`MathError`] of type
    ///     [`MathError::MismatchingModulus`] if the moduli mismatch.
    pub fn mul_safe(&self, other: &Self) -> Result<Self, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                "Tried to multiply matrices with moduli '{}' and '{}'.",
                self.get_mod(),
                other.get_mod()
            )));
        }

        let mut new =
            MatPolynomialRingZq::from((&self.matrix.mul_safe(&other.matrix)?, &self.modulus));

        new.reduce();

        Ok(new)
    }
}

#[cfg(test)]
mod test_mul {
    use super::MatPolynomialRingZq;
    use crate::{integer::MatPolyOverZ, integer_mod_q::ModulusPolynomialRingZq};
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Checks if matrix multiplication works fine for squared matrices.
    #[test]
    fn square_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));

        let poly_ring_mat_3 = &poly_ring_mat_1 * &poly_ring_mat_2;

        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  11 16 1, 3  1 0 8],[0, 0]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        assert_eq!(poly_ring_mat_cmp, poly_ring_mat_3);
    }

    /// Checks if matrix multiplication works fine for matrices of different dimensions.
    #[test]
    fn different_dimensions_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[1  42],[1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));

        let poly_ring_mat_3 = &poly_ring_mat_1 * &poly_ring_mat_2;

        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  1 0 8],[0]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        assert_eq!(poly_ring_mat_cmp, poly_ring_mat_3);
    }

    /// Checks if matrix multiplication works fine for large entries.
    #[test]
    fn large_entries() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly_mat_1 =
            MatPolyOverZ::from_str(&format!("[[2  3 {}, 1  15],[1  1, 0]]", u64::MAX)).unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str(&format!("[[2  1 {}],[0]]", u64::MAX)).unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));

        let poly_ring_mat_3 = &poly_ring_mat_1 * &poly_ring_mat_2;

        let poly_mat_cmp = MatPolyOverZ::from_str(&format!(
            "[[3  3 {} {}],[2  1 {}]]",
            u128::from(u64::MAX) * 4,
            u128::from(u64::MAX) * u128::from(u64::MAX),
            u64::MAX
        ))
        .unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        assert_eq!(poly_ring_mat_cmp, poly_ring_mat_3);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// or mismatch moduli throws an error as expected.
    #[test]
    fn errors() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let modulus_2 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();

        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let poly_mat_2 =
            MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17],[1  24, 0]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus_1));
        let poly_mat_3 = MatPolyOverZ::from_str("[[3  11 16 1, 3  1 0 8],[0, 0]]").unwrap();
        let poly_ring_mat_3 = MatPolynomialRingZq::from((&poly_mat_3, &modulus_2));

        assert!((poly_ring_mat_1.mul_safe(&poly_ring_mat_2)).is_err());
        assert!((poly_ring_mat_1.mul_safe(&poly_ring_mat_3)).is_err());
    }
}
