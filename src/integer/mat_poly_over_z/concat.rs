// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to concatenate two [`MatPolyOverZ`].

use super::MatPolyOverZ;
use crate::{
    error::MathError,
    traits::{Concatenate, GetNumColumns, GetNumRows},
};
use flint_sys::fmpz_poly_mat::{fmpz_poly_mat_concat_horizontal, fmpz_poly_mat_concat_vertical};

impl Concatenate for &MatPolyOverZ {
    type Output = MatPolyOverZ;

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
    /// use qfall_math::traits::*;
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mat_1 = MatPolyOverZ::new(13, 5).unwrap();
    /// let mat_2 = MatPolyOverZ::new(17, 5).unwrap();
    ///
    /// let mat_vert = mat_1.concat_vertical(&mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a `MathError` of type
    /// [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the matrices can not be concatenated due to mismatching dimensions.
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
        let mut out = MatPolyOverZ::new(
            self.get_num_rows() + other.get_num_rows(),
            self.get_num_columns(),
        )
        .unwrap();
        unsafe {
            fmpz_poly_mat_concat_vertical(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
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
    /// use qfall_math::traits::*;
    /// use qfall_math::integer::MatPolyOverZ;
    ///
    /// let mat_1 = MatPolyOverZ::new(17, 5).unwrap();
    /// let mat_2 = MatPolyOverZ::new(17, 6).unwrap();
    ///
    /// let mat_vert = mat_1.concat_horizontal(&mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a `MathError` of type
    /// [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the matrices can not be concatenated due to mismatching dimensions.
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
        let mut out = MatPolyOverZ::new(
            self.get_num_rows(),
            self.get_num_columns() + other.get_num_columns(),
        )
        .unwrap();
        unsafe {
            fmpz_poly_mat_concat_horizontal(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_concatenate {
    use crate::{
        integer::MatPolyOverZ,
        traits::{Concatenate, GetNumColumns, GetNumRows},
    };
    use std::str::FromStr;

    /// ensure that the dimensions are taken over correctly and an error occurs
    /// if the dimensions mismatch
    #[test]
    fn dimensions_vertical() {
        let mat_1 = MatPolyOverZ::new(13, 5).unwrap();
        let mat_2 = MatPolyOverZ::new(17, 5).unwrap();
        let mat_3 = MatPolyOverZ::new(17, 6).unwrap();

        let mat_vert = mat_1.concat_vertical(&mat_2).unwrap();

        assert_eq!(5, mat_vert.get_num_columns());
        assert_eq!(30, mat_vert.get_num_rows());
        assert!(mat_1.concat_vertical(&mat_3).is_err());
    }

    /// ensure that the dimensions are taken over correctly and an error occurs
    /// if the dimensions mismatch
    #[test]
    fn dimensions_horizontal() {
        let mat_1 = MatPolyOverZ::new(13, 5).unwrap();
        let mat_2 = MatPolyOverZ::new(17, 5).unwrap();
        let mat_3 = MatPolyOverZ::new(17, 6).unwrap();

        let mat_hor = mat_2.concat_horizontal(&mat_3).unwrap();

        assert_eq!(11, mat_hor.get_num_columns());
        assert_eq!(17, mat_hor.get_num_rows());
        assert!(mat_1.concat_horizontal(&mat_2).is_err());
    }

    /// ensure that vertical concatenation works correctly
    #[test]
    fn vertically_correct() {
        let mat_1 = MatPolyOverZ::from_str(&format!(
            "[[1  1,1  2,1  {}],[0,1  5,1  {}]]",
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[1  -1,1  2,1  -17]]").unwrap();

        let mat_vertical = mat_1.concat_vertical(&mat_2).unwrap();

        let cmp_mat = MatPolyOverZ::from_str(&format!(
            "[[1  1,1  2,1  {}],[0,1  5,1  {}],[1  -1,1  2,1  -17]]",
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_mat, mat_vertical)
    }

    /// ensure that horizontal concatenation works correctly
    #[test]
    fn horizontally_correct() {
        let mat_1 = MatPolyOverZ::from_str(&format!(
            "[[1  1,1  2,1  {}],[0,1  5,1  {}]]",
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[1  -1,1  2],[0,1  5]]").unwrap();

        let mat_horizontal = mat_1.concat_horizontal(&mat_2).unwrap();

        let cmp_mat = MatPolyOverZ::from_str(&format!(
            "[[1  1,1  2,1  {},1  -1,1  2],[0,1  5,1  {},0,1  5]]",
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_mat, mat_horizontal)
    }
}
