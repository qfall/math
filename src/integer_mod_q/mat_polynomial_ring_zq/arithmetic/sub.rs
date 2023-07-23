// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`MatPolynomialRingZq`] values.

use crate::error::MathError;
use crate::integer_mod_q::MatPolynomialRingZq;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use std::ops::Sub;

impl Sub for &MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;
    /// Implements the [`Sub`] trait for two [`MatPolynomialRingZq`] values.
    /// [`Sub`] is implemented for any combination of [`MatPolynomialRingZq`]
    /// and borrowed [`MatPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract to `self`
    ///
    /// Returns the result of the subtraction as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
    /// let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
    /// let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
    ///
    /// let poly_ring_mat3: MatPolynomialRingZq = &poly_ring_mat1 - &poly_ring_mat2;
    /// let poly_ring_mat4: MatPolynomialRingZq = poly_ring_mat1 - poly_ring_mat2;
    /// let poly_ring_mat5: MatPolynomialRingZq = &poly_ring_mat3 - poly_ring_mat4;
    /// let poly_ring_mat6: MatPolynomialRingZq = poly_ring_mat3 - &poly_ring_mat5;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    /// - if the moduli of both matrices mismatch.
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
    }
}

impl MatPolynomialRingZq {
    /// Implements subtraction for two [`MatPolynomialRingZq`] matrices.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract to `self`
    ///
    /// Returns the result of the subtraction as a [`MatPolynomialRingZq`] or an
    /// error if the matrix dimensions or moduli mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
    /// let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
    /// let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
    ///
    /// let poly_ring_mat3 = poly_ring_mat1.sub_safe(&poly_ring_mat2);
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    /// both [`MatPolynomialRingZq`] mismatch.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingMatrixDimension`]
    /// if the dimensions of both [`MatPolynomialRingZq`] mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<MatPolynomialRingZq, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                "Tried to subtract polynomial with modulus '{}' and polynomial with modulus '{}'.",
                self.modulus, other.modulus
            )));
        }
        let matrix = self.matrix.sub_safe(&other.matrix)?;

        Ok(MatPolynomialRingZq::from((&matrix, &self.modulus)))
    }
}

arithmetic_trait_borrowed_to_owned!(
    Sub,
    sub,
    MatPolynomialRingZq,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Sub,
    sub,
    MatPolynomialRingZq,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);

#[cfg(test)]
mod test_sub {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    /// Testing subtraction for two [`MatPolynomialRingZq`].
    #[test]
    fn sub() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[2  0 1, 1  42],[2  3 4, 2  0 1]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));

        let poly_ring_mat3 = poly_ring_mat1 - poly_ring_mat2;

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  0 0 1, 0],[2  -3 -4, 2  1 1]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));
        assert_eq!(cmp_poly_ring_mat, poly_ring_mat3);
    }

    /// Testing subtraction for big numbers.
    #[test]
    fn sub_large_numbers() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let poly_mat1 =
            MatPolyOverZ::from_str(&format!("[[3  0 {} 1, 1  42],[0, 2  1 2]]", i64::MAX)).unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 =
            MatPolyOverZ::from_str(&format!("[[2  0 {}, 1  42],[2  3 4, 2  0 1]]", i64::MAX))
                .unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));

        let poly_ring_mat3 = poly_ring_mat1 - poly_ring_mat2;

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  0 0 1, 0],[2  -3 -4, 2  1 1]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));
        assert_eq!(cmp_poly_ring_mat, poly_ring_mat3);
    }

    /// Testing sub_safe.
    #[test]
    fn sub_safe() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[2  0 1, 1  42],[2  3 4, 2  0 1]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));

        let poly_ring_mat3 = poly_ring_mat1.sub_safe(&poly_ring_mat2).unwrap();

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  0 0 1, 0],[2  -3 -4, 2  1 1]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));
        assert_eq!(cmp_poly_ring_mat, poly_ring_mat3);
    }

    /// Testing sub_safe throws an error if the dimensions mismatch.
    #[test]
    fn sub_safe_error_dim() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42, 0],[0, 1  17, 1  1]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
        let poly_mat3 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42, 0]]").unwrap();
        let poly_ring_mat3 = MatPolynomialRingZq::from((&poly_mat3, &modulus));

        assert!(poly_ring_mat1.sub_safe(&poly_ring_mat2).is_err());
        assert!(poly_ring_mat3.sub_safe(&poly_ring_mat2).is_err());
    }

    /// Testing sub_safe throws an error if the moduli mismatch.
    #[test]
    fn sub_safe_error_modulus() {
        let modulus1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let modulus2 = ModulusPolynomialRingZq::from_str("4  1 0 1 1 mod 17").unwrap();
        let modulus3 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 18").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat, &modulus1));
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat, &modulus2));
        let poly_ring_mat3 = MatPolynomialRingZq::from((&poly_mat, &modulus3));

        assert!(poly_ring_mat1.sub_safe(&poly_ring_mat2).is_err());
        assert!(poly_ring_mat3.sub_safe(&poly_ring_mat2).is_err());
    }

    /// Tests the doc test (availability).
    #[test]
    fn doc_test() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));

        let poly_ring_mat3: MatPolynomialRingZq = &poly_ring_mat1 - &poly_ring_mat2;
        let poly_ring_mat4: MatPolynomialRingZq = poly_ring_mat1 - poly_ring_mat2;
        let poly_ring_mat5: MatPolynomialRingZq = &poly_ring_mat3 - poly_ring_mat4;
        let _poly_ring_mat6: MatPolynomialRingZq = poly_ring_mat3 - &poly_ring_mat5;
    }
}
