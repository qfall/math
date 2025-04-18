// Copyright © 2023 Phil Milewski, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`MatPolyOverZ`] values.

use super::super::MatPolyOverZ;
use crate::error::MathError;
use crate::integer_mod_q::MatPolynomialRingZq;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::MatrixDimensions;
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_sub;
use std::ops::Sub;

impl Sub for &MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Implements the [`Sub`] trait for two [`MatPolyOverZ`] values.
    /// [`Sub`] is implemented for any combination of [`MatPolyOverZ`] and borrowed [`MatPolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from`self`
    ///
    /// Returns the result of the subtraction as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
    /// let b: MatPolyOverZ = MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
    ///
    /// let c: MatPolyOverZ = &a - &b;
    /// let d: MatPolyOverZ = a - b;
    /// let e: MatPolyOverZ = &c - d;
    /// let f: MatPolyOverZ = c - &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, MatPolyOverZ, MatPolyOverZ, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, MatPolyOverZ, MatPolyOverZ, MatPolyOverZ);

impl Sub<&MatPolynomialRingZq> for &MatPolyOverZ {
    type Output = MatPolynomialRingZq;
    /// Implements the [`Sub`] trait for a [`MatPolyOverZ`] matrix with a [`MatPolynomialRingZq`] matrix.
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
    /// let mat_1 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]]").unwrap();
    /// let mat_2 = MatPolynomialRingZq::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]] / 3  1 2 3 mod 17").unwrap();
    ///
    /// let mat_3 = &mat_1 - &mat_2;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    fn sub(self, other: &MatPolynomialRingZq) -> Self::Output {
        self.sub_mat_poly_ring_zq_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(
    Sub,
    sub,
    MatPolyOverZ,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Sub,
    sub,
    MatPolyOverZ,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);

impl MatPolyOverZ {
    /// Implements subtraction for two [`MatPolyOverZ`] matrices.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from`self`
    ///
    /// Returns the result of the subtraction as a [`MatPolyOverZ`] or an
    /// error if the matrix dimensions mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
    /// let b: MatPolyOverZ = MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
    ///
    /// let c: MatPolyOverZ = a.sub_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// - Returns a [`MathError`] of type
    ///   [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    ///   mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<MatPolyOverZ, MathError> {
        if self.get_num_rows() != other.get_num_rows()
            || self.get_num_columns() != other.get_num_columns()
        {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to subtract a '{}x{}' matrix and a '{}x{}' matrix.",
                other.get_num_rows(),
                other.get_num_columns(),
                self.get_num_rows(),
                self.get_num_columns()
            )));
        }
        let mut out = MatPolyOverZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpz_poly_mat_sub(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }

    /// Implements subtraction for a [`MatPolyOverZ`] matrix with a [`MatPolynomialRingZq`] matrix.
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
    /// let mat_1 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]]").unwrap();
    /// let mat_2 = MatPolynomialRingZq::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]] / 3  1 2 3 mod 17").unwrap();
    ///
    /// let mat_3 = &mat_1.sub_mat_poly_ring_zq_safe(&mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///   [`MathError::MismatchingMatrixDimension`] if the dimensions of `self`
    ///   and `other` do not match for multiplication.
    pub fn sub_mat_poly_ring_zq_safe(
        &self,
        other: &MatPolynomialRingZq,
    ) -> Result<MatPolynomialRingZq, MathError> {
        let mut out =
            MatPolynomialRingZq::new(self.get_num_rows(), self.get_num_columns(), other.get_mod());

        out.matrix = self.sub_safe(&other.matrix)?;
        out.reduce();

        Ok(out)
    }
}

#[cfg(test)]
mod test_sub {
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Testing subtraction for two [`MatPolyOverZ`]
    #[test]
    fn sub() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
        let c: MatPolyOverZ = a - b;
        assert_eq!(
            c,
            MatPolyOverZ::from_str("[[1  42, 1  42, 2  18 -18],[3  16 12 38, 1  18, 1  25]]")
                .unwrap()
        );
    }

    /// Testing subtraction for two borrowed [`MatPolyOverZ`]
    #[test]
    fn sub_borrow() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
        let c: MatPolyOverZ = &a - &b;
        assert_eq!(
            c,
            MatPolyOverZ::from_str("[[1  42, 1  42, 2  18 -18],[3  16 12 38, 1  18, 1  25]]")
                .unwrap()
        );
    }

    /// Testing subtraction for borrowed [`MatPolyOverZ`] and [`MatPolyOverZ`]
    #[test]
    fn sub_first_borrowed() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
        let c: MatPolyOverZ = &a - b;
        assert_eq!(
            c,
            MatPolyOverZ::from_str("[[1  42, 1  42, 2  18 -18],[3  16 12 38, 1  18, 1  25]]")
                .unwrap()
        );
    }

    /// Testing subtraction for [`MatPolyOverZ`] and borrowed [`MatPolyOverZ`]
    #[test]
    fn sub_second_borrowed() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
        let c: MatPolyOverZ = a - &b;
        assert_eq!(
            c,
            MatPolyOverZ::from_str("[[1  42, 1  42, 2  18 -18],[3  16 12 38, 1  18, 1  25]]")
                .unwrap()
        );
    }

    /// Testing subtraction for large numbers
    #[test]
    fn sub_large_numbers() {
        let a: MatPolyOverZ = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 2  1 {}],[2  -{} 7, 0]]",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 2  1 {}],[2  {} 7, 0]]",
            i64::MAX,
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let c: MatPolyOverZ = a - &b;
        assert_eq!(
            c,
            MatPolyOverZ::from_str(&format!("[[0, 2  0 -{}],[1  -{}, 0]]", u64::MAX, i64::MAX))
                .unwrap()
        );
    }

    /// Testing sub_safe
    #[test]
    fn sub_safe() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ =
            MatPolyOverZ::from_str("[[1  -42, 0, 2  24 42],[3  1 12 4, 1  -1, 1  17]]").unwrap();
        let c: MatPolyOverZ = a.sub_safe(&b).unwrap();
        assert_eq!(
            c,
            MatPolyOverZ::from_str("[[1  42, 1  42, 2  18 -18],[3  16 12 38, 1  18, 1  25]]")
                .unwrap()
        );
    }

    /// Testing sub_safe throws error
    #[test]
    fn sub_safe_is_err() {
        let a: MatPolyOverZ =
            MatPolyOverZ::from_str("[[0, 1  42, 2  42 24],[3  17 24 42, 1  17, 1  42]]").unwrap();
        let b: MatPolyOverZ = MatPolyOverZ::from_str("[[1  -42, 0],[3  1 12 4, 1  17]]").unwrap();
        let c: MatPolyOverZ = MatPolyOverZ::from_str("[[0, 1  42, 2  42 24]]").unwrap();
        assert!(a.sub_safe(&b).is_err());
        assert!(c.sub_safe(&b).is_err());
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

        let _ = &poly_mat - &poly_ring_mat;
        let _ = &poly_mat - poly_ring_mat.clone();
        let _ = poly_mat.clone() - &poly_ring_mat;
        let _ = poly_mat.clone() - poly_ring_mat.clone();
    }

    /// Checks if subtraction works fine for squared matrices.
    #[test]
    fn square_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[2  1 1, 1  42],[0, 2  1 2]]").unwrap();

        let poly_ring_mat_3 = &poly_mat_2 - &poly_ring_mat_1;

        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  -2 1 -1, 0],[0, 2  -16 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        assert_eq!(poly_ring_mat_cmp, poly_ring_mat_3);
    }

    /// Checks if subtraction works fine for large entries.
    #[test]
    fn large_entries() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str(&format!("[[2  1 {}],[0]]", u64::MAX)).unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str(&format!("[[2  3 {}],[1  1]]", u64::MAX)).unwrap();

        let poly_ring_mat_3 = &poly_mat_2 - &poly_ring_mat_1;

        let poly_mat_cmp = MatPolyOverZ::from_str("[[2  2 0],[1  1]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        assert_eq!(poly_ring_mat_cmp, poly_ring_mat_3);
    }

    /// Checks if subtraction with incompatible matrix dimensions
    /// throws an error as expected.
    #[test]
    fn errors() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  1],[2  1 2, 1  1]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let poly_mat_2 = MatPolyOverZ::from_str("[[4  -1 0 1 1],[2  1 2]]").unwrap();

        assert!((poly_mat_2.sub_mat_poly_ring_zq_safe(&poly_ring_mat_1)).is_err());
    }

    /// Checks if subtraction panics if dimensions mismatch.
    #[test]
    #[should_panic]
    fn mul_panic() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  1],[2  1 2, 1  1]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let poly_mat_2 = MatPolyOverZ::from_str("[[1  3],[2  1 2]]").unwrap();

        let _ = &poly_mat_2 - &poly_ring_mat_1;
    }
}
