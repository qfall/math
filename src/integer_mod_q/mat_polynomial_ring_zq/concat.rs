// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to concatenate two [`MatPolynomialRingZq`](crate::integer_mod_q::MatPolynomialRingZq).

use super::MatPolynomialRingZq;
use crate::{
    error::MathError,
    integer::MatPolyOverZ,
    traits::{Concatenate, GetNumColumns, GetNumRows},
};
use flint_sys::fmpz_poly_mat::{fmpz_poly_mat_concat_horizontal, fmpz_poly_mat_concat_vertical};

impl Concatenate for &MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;

    /// Concatenates `self` with `other` vertically, i.e. `other` is added below.
    ///
    /// Parameters:
    /// - `other`: the other matrix to concatenate with `self`
    ///
    /// Returns a vertical concatenation of the two matrices or a
    /// an error, if the matrices can not be concatenated vertically.
    ///
    /// # Examples
    /// ```
    /// use crate::qfall_math::traits::*;
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq};
    /// use std::str::FromStr;
    ///
    /// let poly_mod = PolyOverZq::from_str("3  1 17 1 mod 17").unwrap();
    /// let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
    ///
    /// let mat_1 = MatPolynomialRingZq::new(13, 5, &modulus).unwrap();
    /// let mat_2 = MatPolynomialRingZq::new(17, 5, &modulus).unwrap();
    ///
    /// let mat_vert = mat_1.concat_vertical(&mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// Returns a `MathError` of type
    /// [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the matrices can not be concatenated due to mismatching dimensions
    fn concat_vertical(self, other: Self) -> Result<Self::Output, crate::error::MathError> {
        if self.get_num_columns() != other.get_num_columns() {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to concatenate vertically a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            )));
        }
        let mut matrix = MatPolyOverZ::new(
            self.get_num_rows() + other.get_num_rows(),
            self.get_num_columns(),
        )
        .unwrap();
        unsafe {
            fmpz_poly_mat_concat_vertical(
                &mut matrix.matrix,
                &self.matrix.matrix,
                &other.matrix.matrix,
            );
        }
        Ok(MatPolynomialRingZq {
            matrix,
            modulus: self.get_mod(),
        })
    }

    /// Concatenates `self` with `other` horizontally, i.e. `other` is added on the right.
    ///
    /// Parameters:
    /// - `other`: the other matrix to concatenate with `self`
    ///
    /// Returns a horizontal concatenation of the two matrices or a
    /// an error, if the matrices can not be concatenated horizontally.
    ///
    /// # Examples
    /// ```
    /// use crate::qfall_math::traits::*;
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq};
    /// use std::str::FromStr;
    ///
    /// let poly_mod = PolyOverZq::from_str("3  1 17 1 mod 17").unwrap();
    /// let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
    ///
    /// let mat_1 = MatPolynomialRingZq::new(17, 5, &modulus).unwrap();
    /// let mat_2 = MatPolynomialRingZq::new(17, 7, &modulus).unwrap();
    ///
    /// let mat_vert = mat_1.concat_horizontal(&mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// Returns a `MathError` of type
    /// [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the matrices can not be concatenated due to mismatching dimensions
    fn concat_horizontal(self, other: Self) -> Result<Self::Output, crate::error::MathError> {
        if self.get_num_rows() != other.get_num_rows() {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to concatenate horizontally a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            )));
        }
        let mut matrix = MatPolyOverZ::new(
            self.get_num_rows(),
            self.get_num_columns() + other.get_num_columns(),
        )
        .unwrap();
        unsafe {
            fmpz_poly_mat_concat_horizontal(
                &mut matrix.matrix,
                &self.matrix.matrix,
                &other.matrix.matrix,
            );
        }
        Ok(MatPolynomialRingZq {
            matrix,
            modulus: self.get_mod(),
        })
    }
}

#[cfg(test)]
mod test_concatenate {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq},
        traits::{Concatenate, GetNumColumns, GetNumRows},
    };
    use std::str::FromStr;

    const BITPRIME64: u64 = u64::MAX - 58;

    /// Ensure that the dimensions are taken over correctly and an error occurs
    /// if the dimensions mismatch
    #[test]
    fn dimensions_vertical() {
        let poly_mod =
            PolyOverZq::from_str(&format!("3  1 {} 1 mod {}", i64::MAX, BITPRIME64)).unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
        let mat_1 = MatPolynomialRingZq::new(13, 5, &modulus).unwrap();
        let mat_2 = MatPolynomialRingZq::new(17, 5, &modulus).unwrap();
        let mat_3 = MatPolynomialRingZq::new(17, 6, &modulus).unwrap();

        let mat_vert = mat_1.concat_vertical(&mat_2).unwrap();

        assert_eq!(5, mat_vert.get_num_columns());
        assert_eq!(30, mat_vert.get_num_rows());
        assert!(mat_1.concat_vertical(&mat_3).is_err());
    }

    /// Ensure that the dimensions are taken over correctly and an error occurs
    /// if the dimensions mismatch
    #[test]
    fn dimensions_horizontal() {
        let poly_mod =
            PolyOverZq::from_str(&format!("3  1 {} 1 mod {}", i64::MAX, BITPRIME64)).unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
        let mat_1 = MatPolynomialRingZq::new(13, 5, &modulus).unwrap();
        let mat_2 = MatPolynomialRingZq::new(17, 5, &modulus).unwrap();
        let mat_3 = MatPolynomialRingZq::new(17, 6, &modulus).unwrap();

        let mat_vert = mat_2.concat_horizontal(&mat_3).unwrap();

        assert_eq!(11, mat_vert.get_num_columns());
        assert_eq!(17, mat_vert.get_num_rows());
        assert!(mat_1.concat_horizontal(&mat_2).is_err());
    }

    /// Ensure that vertical concatenation works correctly
    #[test]
    fn vertically_correct() {
        let poly_mod =
            PolyOverZq::from_str(&format!("3  1 {} 1 mod {}", i64::MAX, BITPRIME64)).unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str(&format!(
            "[[4  {} {} 1 1, 1  42],[0, 2  1 2]]",
            BITPRIME64 + 2,
            u64::MAX
        ))
        .unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str("[[1  27, 2  10 5]]").unwrap();
        let poly_ring_mat_1 =
            MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_mat_1, &modulus);
        let poly_ring_mat_2 =
            MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_mat_2, &modulus);

        let mat_vertical = poly_ring_mat_1.concat_vertical(&poly_ring_mat_2).unwrap();

        let poly_mat_cmp = MatPolyOverZ::from_str(&format!(
            "[[4  {} {} 1 1, 1  42],[0, 2  1 2],[1  27, 2  10 5]]",
            BITPRIME64 + 2,
            u64::MAX
        ))
        .unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(
            &poly_mat_cmp,
            &modulus,
        );

        assert_eq!(poly_ring_mat_cmp, mat_vertical)
    }

    /// Ensure that horizontal concatenation works correctly
    #[test]
    fn horizontally_correct() {
        let poly_mod =
            PolyOverZq::from_str(&format!("3  1 {} 1 mod {}", i64::MAX, BITPRIME64)).unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str(&format!(
            "[[4  {} {} 1 1, 1  42],[0, 2  1 2]]",
            BITPRIME64 + 2,
            u64::MAX
        ))
        .unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str("[[1  27],[2  10 5]]").unwrap();
        let poly_ring_mat_1 =
            MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_mat_1, &modulus);
        let poly_ring_mat_2 =
            MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_mat_2, &modulus);

        let mat_vertical = poly_ring_mat_1.concat_horizontal(&poly_ring_mat_2).unwrap();

        let poly_mat_cmp = MatPolyOverZ::from_str(&format!(
            "[[4  {} {} 1 1, 1  42, 1  27],[0, 2  1 2, 2  10 5]]",
            BITPRIME64 + 2,
            u64::MAX
        ))
        .unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(
            &poly_mat_cmp,
            &modulus,
        );

        assert_eq!(poly_ring_mat_cmp, mat_vertical)
    }
}
