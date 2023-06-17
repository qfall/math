// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to concatenate two [`MatZ`](crate::integer::MatZ).

use super::MatZ;
use crate::{
    error::MathError,
    traits::{Concatenate, GetNumColumns, GetNumRows},
};
use flint_sys::fmpz_mat::{fmpz_mat_concat_horizontal, fmpz_mat_concat_vertical};

impl Concatenate for &MatZ {
    type Output = MatZ;

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
    /// use qfall_math::integer::MatZ;
    ///
    /// let mat_1 = MatZ::new(13, 5);
    /// let mat_2 = MatZ::new(17, 5);
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
        let mut out = MatZ::new(
            self.get_num_rows() + other.get_num_rows(),
            self.get_num_columns(),
        );
        unsafe {
            fmpz_mat_concat_vertical(&mut out.matrix, &self.matrix, &other.matrix);
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
    /// use qfall_math::integer::MatZ;
    ///
    /// let mat_1 = MatZ::new(17, 5);
    /// let mat_2 = MatZ::new(17, 6);
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
        let mut out = MatZ::new(
            self.get_num_rows(),
            self.get_num_columns() + other.get_num_columns(),
        );
        unsafe {
            fmpz_mat_concat_horizontal(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_concatenate {
    use crate::{
        integer::MatZ,
        traits::{Concatenate, GetNumColumns, GetNumRows},
    };
    use std::str::FromStr;

    /// Ensure that the dimensions are taken over correctly and an error occurs
    /// if the dimensions mismatch
    #[test]
    fn dimensions_vertical() {
        let mat_1 = MatZ::new(13, 5);
        let mat_2 = MatZ::new(17, 5);
        let mat_3 = MatZ::new(17, 6);

        let mat_vert = mat_1.concat_vertical(&mat_2).unwrap();

        assert_eq!(5, mat_vert.get_num_columns());
        assert_eq!(30, mat_vert.get_num_rows());
        assert!(mat_1.concat_vertical(&mat_3).is_err());
    }

    /// Ensure that the dimensions are taken over correctly and an error occurs
    /// if the dimensions mismatch
    #[test]
    fn dimensions_horizontal() {
        let mat_1 = MatZ::new(13, 5);
        let mat_2 = MatZ::new(17, 5);
        let mat_3 = MatZ::new(17, 6);

        let mat_vert = mat_2.concat_horizontal(&mat_3).unwrap();

        assert_eq!(11, mat_vert.get_num_columns());
        assert_eq!(17, mat_vert.get_num_rows());
        assert!(mat_1.concat_horizontal(&mat_2).is_err());
    }

    /// Ensure that vertical concatenation works correctly
    #[test]
    fn vertically_correct() {
        let mat_1 =
            MatZ::from_str(&format!("[[1, 2, {}],[4, 5, {}]]", i64::MIN, u64::MAX)).unwrap();
        let mat_2 = MatZ::from_str("[[-1, 2, -17]]").unwrap();

        let mat_vertical = mat_1.concat_vertical(&mat_2).unwrap();

        let cmp_mat = MatZ::from_str(&format!(
            "[[1, 2, {}],[4, 5, {}],[-1, 2, -17]]",
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_mat, mat_vertical)
    }

    /// Ensure that horizontal concatenation works correctly
    #[test]
    fn horizontally_correct() {
        let mat_1 =
            MatZ::from_str(&format!("[[1, 2, {}],[4, 5, {}]]", i64::MIN, u64::MAX)).unwrap();
        let mat_2 = MatZ::from_str("[[-1, 2],[4, 5]]").unwrap();

        let mat_horizontal = mat_1.concat_horizontal(&mat_2).unwrap();

        let cmp_mat = MatZ::from_str(&format!(
            "[[1, 2, {}, -1, 2],[4, 5, {}, 4, 5]]",
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_mat, mat_horizontal)
    }
}
