// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`MatPolynomialRingZq`] values.

use crate::error::MathError;
use crate::integer::MatPolyOverZ;
use crate::integer_mod_q::MatPolynomialRingZq;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::MatrixDimensions;
use std::ops::Sub;

impl Sub for &MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;
    /// Implements the [`Sub`] trait for two [`MatPolynomialRingZq`] values.
    /// [`Sub`] is implemented for any combination of [`MatPolynomialRingZq`]
    /// and borrowed [`MatPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from`self`
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
    /// let poly_mat_1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  3],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
    /// let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  7],[0, 1  16]]").unwrap();
    /// let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
    ///
    /// let poly_ring_mat_3: MatPolynomialRingZq = &poly_ring_mat_1 - &poly_ring_mat_2;
    /// let poly_ring_mat_4: MatPolynomialRingZq = poly_ring_mat_1 - poly_ring_mat_2;
    /// let poly_ring_mat_5: MatPolynomialRingZq = &poly_ring_mat_3 - poly_ring_mat_4;
    /// let poly_ring_mat_6: MatPolynomialRingZq = poly_ring_mat_3 - &poly_ring_mat_5;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    /// - if the moduli of both matrices mismatch.
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
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

impl Sub<&MatPolyOverZ> for &MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;
    /// Implements the [`Sub`] trait for a [`MatPolynomialRingZq`] matrix with a [`MatPolyOverZ`] matrix.
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the subtraction of `self` by `other` as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatPolynomialRingZq::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]] / 3  1 2 3 mod 17").unwrap();
    /// let mat_2 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]]").unwrap();
    ///
    /// let mat_3 = &mat_1 - &mat_2;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    fn sub(self, other: &MatPolyOverZ) -> Self::Output {
        self.sub_mat_poly_over_z_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(
    Sub,
    sub,
    MatPolynomialRingZq,
    MatPolyOverZ,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Sub,
    sub,
    MatPolynomialRingZq,
    MatPolyOverZ,
    MatPolynomialRingZq
);

impl MatPolynomialRingZq {
    /// Implements subtraction for two [`MatPolynomialRingZq`] matrices.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from`self`
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
    /// let poly_mat_1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  3],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
    /// let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  7],[0, 1  16]]").unwrap();
    /// let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
    ///
    /// let poly_ring_mat_3 = poly_ring_mat_1.sub_safe(&poly_ring_mat_2);
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    ///     both [`MatPolynomialRingZq`] mismatch.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingMatrixDimension`]
    ///     if the dimensions of both [`MatPolynomialRingZq`] mismatch.
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

    /// Implements subtraction for a [`MatPolynomialRingZq`] matrix with a [`MatPolyOverZ`] matrix.
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the subtraction of `self` by `other` as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatPolynomialRingZq::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]] / 3  1 2 3 mod 17").unwrap();
    /// let mat_2 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]]").unwrap();
    ///
    /// let mat_3 = &mat_1.sub_mat_poly_over_z_safe(&mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`MathError::MismatchingMatrixDimension`] if the dimensions of `self`
    ///     and `other` do not match for multiplication.
    pub fn sub_mat_poly_over_z_safe(&self, other: &MatPolyOverZ) -> Result<Self, MathError> {
        let mut out =
            MatPolynomialRingZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());

        out.matrix = self.matrix.sub_safe(other)?;
        out.reduce();

        Ok(out)
    }
}

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
        let poly_mat_1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[2  0 1, 1  42],[2  3 4, 2  0 1]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));

        let poly_ring_mat_3 = poly_ring_mat_1 - poly_ring_mat_2;

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  0 0 1, 0],[2  -3 -4, 2  1 1]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));
        assert_eq!(cmp_poly_ring_mat, poly_ring_mat_3);
    }

    /// Testing subtraction for large numbers.
    #[test]
    fn sub_large_numbers() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let poly_mat_1 =
            MatPolyOverZ::from_str(&format!("[[3  0 {} 1, 1  42],[0, 2  1 2]]", i64::MAX)).unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 =
            MatPolyOverZ::from_str(&format!("[[2  0 {}, 1  42],[2  3 4, 2  0 1]]", i64::MAX))
                .unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));

        let poly_ring_mat_3 = poly_ring_mat_1 - poly_ring_mat_2;

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  0 0 1, 0],[2  -3 -4, 2  1 1]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));
        assert_eq!(cmp_poly_ring_mat, poly_ring_mat_3);
    }

    /// Testing sub_safe.
    #[test]
    fn sub_safe() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[2  0 1, 1  42],[2  3 4, 2  0 1]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));

        let poly_ring_mat_3 = poly_ring_mat_1.sub_safe(&poly_ring_mat_2).unwrap();

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  0 0 1, 0],[2  -3 -4, 2  1 1]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));
        assert_eq!(cmp_poly_ring_mat, poly_ring_mat_3);
    }

    /// Testing sub_safe throws an error if the dimensions mismatch.
    #[test]
    fn sub_safe_error_dim() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42, 0],[0, 1  17, 1  1]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
        let poly_mat_3 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42, 0]]").unwrap();
        let poly_ring_mat_3 = MatPolynomialRingZq::from((&poly_mat_3, &modulus));

        assert!(poly_ring_mat_1.sub_safe(&poly_ring_mat_2).is_err());
        assert!(poly_ring_mat_3.sub_safe(&poly_ring_mat_2).is_err());
    }

    /// Testing sub_safe throws an error if the moduli mismatch.
    #[test]
    fn sub_safe_error_modulus() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let modulus_2 = ModulusPolynomialRingZq::from_str("4  1 0 1 1 mod 17").unwrap();
        let modulus_3 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 18").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat, &modulus_1));
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat, &modulus_2));
        let poly_ring_mat_3 = MatPolynomialRingZq::from((&poly_mat, &modulus_3));

        assert!(poly_ring_mat_1.sub_safe(&poly_ring_mat_2).is_err());
        assert!(poly_ring_mat_3.sub_safe(&poly_ring_mat_2).is_err());
    }

    /// Tests the doc test (availability).
    #[test]
    fn doc_test() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  3],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  7],[0, 1  16]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));

        let poly_ring_mat_3: MatPolynomialRingZq = &poly_ring_mat_1 - &poly_ring_mat_2;
        let poly_ring_mat_4: MatPolynomialRingZq = poly_ring_mat_1 - poly_ring_mat_2;
        let poly_ring_mat_5: MatPolynomialRingZq = &poly_ring_mat_3 - poly_ring_mat_4;
        let _poly_ring_mat_6: MatPolynomialRingZq = poly_ring_mat_3 - &poly_ring_mat_5;
    }
}

#[cfg(test)]
mod test_mul_mat_poly_over_z {
    use super::MatPolynomialRingZq;
    use crate::{integer::MatPolyOverZ, integer_mod_q::ModulusPolynomialRingZq};
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Checks whether subtraction is available for other types.
    #[test]
    fn availability() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[3  0 1 1, 1  3],[0, 2  1 2]]").unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));

        let _ = &poly_ring_mat - &poly_mat;
        let _ = &poly_ring_mat - poly_mat.clone();
        let _ = poly_ring_mat.clone() - &poly_mat;
        let _ = poly_ring_mat - poly_mat;
    }

    /// Checks if subtraction works fine for squared matrices.
    #[test]
    fn square_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[2  1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();

        let poly_ring_mat_3 = &poly_ring_mat_1 - &poly_mat_2;

        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  -2 1 -1, 0],[0, 2  -16 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        assert_eq!(poly_ring_mat_cmp, poly_ring_mat_3);
    }

    /// Checks if subtraction works fine for large entries.
    #[test]
    fn large_entries() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str(&format!("[[2  3 {}],[1  1]]", u64::MAX)).unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str(&format!("[[2  1 {}],[0]]", u64::MAX)).unwrap();

        let poly_ring_mat_3 = &poly_ring_mat_1 - &poly_mat_2;

        let poly_mat_cmp = MatPolyOverZ::from_str("[[2  2 0],[1  1]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        assert_eq!(poly_ring_mat_cmp, poly_ring_mat_3);
    }

    /// Checks if subtraction with incompatible matrix dimensions
    /// throws an error as expected.
    #[test]
    fn errors() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1],[2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let poly_mat_2 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  1],[2  1 2, 1  1]]").unwrap();

        assert!((poly_ring_mat_1.sub_mat_poly_over_z_safe(&poly_mat_2)).is_err());
    }

    /// Checks if subtraction panics if dimensions mismatch.
    #[test]
    #[should_panic]
    fn mul_panic() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[1  3],[2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let poly_mat_2 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  1],[2  1 2, 1  1]]").unwrap();

        let _ = &poly_ring_mat_1 - &poly_mat_2;
    }
}
