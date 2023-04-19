// Copyright © 2023 Marvin Beckmann, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to concatenate two [`MatZq`](crate::integer_mod_q::MatZq).

use super::MatZq;
use crate::{
    error::MathError,
    traits::{Concatenate, GetNumColumns, GetNumRows},
};
use flint_sys::fmpz_mod_mat::{fmpz_mod_mat_concat_horizontal, fmpz_mod_mat_concat_vertical};

impl Concatenate for &MatZq {
    type Output = MatZq;

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
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mat_1 = MatZq::new(13, 5, 19).unwrap();
    /// let mat_2 = MatZq::new(17, 5, 19).unwrap();
    ///
    /// let mat_vert = mat_1.concat_vertical(&mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the matrices can not be concatenated due to mismatching dimensions.
    /// - Returns a [`MathError`] of type
    /// [`MismatchingModulus`](MathError::MismatchingModulus)
    /// if the matrices can not be concatenated due to mismatching moduli.
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

        if self.get_mod() != other.get_mod() {
            return Err(MathError::MismatchingModulus(format!(
                "Tried to concatenate matrices with different moduli {} and {}.",
                self.get_mod(),
                other.get_mod(),
            )));
        }

        let mut out = MatZq::new(
            self.get_num_rows() + other.get_num_rows(),
            self.get_num_columns(),
            self.get_mod(),
        )
        .unwrap();
        unsafe {
            fmpz_mod_mat_concat_vertical(&mut out.matrix, &self.matrix, &other.matrix);
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
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let mat_1 = MatZq::new(17, 5, 19).unwrap();
    /// let mat_2 = MatZq::new(17, 6, 19).unwrap();
    ///
    /// let mat_vert = mat_1.concat_horizontal(&mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a `MathError` of type
    /// [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the matrices can not be concatenated due to mismatching dimensions.
    /// - Returns a [`MathError`] of type
    /// [`MismatchingModulus`](MathError::MismatchingModulus)
    /// if the matrices can not be concatenated due to mismatching moduli.
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

        if self.get_mod() != other.get_mod() {
            return Err(MathError::MismatchingModulus(format!(
                "Tried to concatenate matrices with different moduli {} and {}.",
                self.get_mod(),
                other.get_mod(),
            )));
        }

        let mut out = MatZq::new(
            self.get_num_rows(),
            self.get_num_columns() + other.get_num_columns(),
            self.get_mod(),
        )
        .unwrap();
        unsafe {
            fmpz_mod_mat_concat_horizontal(&mut out.matrix, &self.matrix, &other.matrix);
        }

        Ok(out)
    }
}

#[cfg(test)]
mod test_concatenate {
    use crate::{
        integer_mod_q::MatZq,
        traits::{Concatenate, GetNumColumns, GetNumRows},
    };
    use std::str::FromStr;

    /// ensure that the dimensions are taken over correctly and an error occurs
    /// if the dimensions mismatch
    #[test]
    fn dimensions_vertical() {
        let mat_1 = MatZq::new(13, 5, 17).unwrap();
        let mat_2 = MatZq::new(17, 5, 17).unwrap();
        let mat_3 = MatZq::new(17, 6, 17).unwrap();

        let mat_vert = mat_1.concat_vertical(&mat_2).unwrap();

        assert_eq!(5, mat_vert.get_num_columns());
        assert_eq!(30, mat_vert.get_num_rows());
        assert!(mat_1.concat_vertical(&mat_3).is_err());
    }

    /// ensure that the dimensions are taken over correctly and an error occurs
    /// if the dimensions mismatch
    #[test]
    fn dimensions_horizontal() {
        let mat_1 = MatZq::new(13, 5, 17).unwrap();
        let mat_2 = MatZq::new(17, 5, 17).unwrap();
        let mat_3 = MatZq::new(17, 6, 17).unwrap();

        let mat_hor = mat_2.concat_horizontal(&mat_3).unwrap();

        assert_eq!(11, mat_hor.get_num_columns());
        assert_eq!(17, mat_hor.get_num_rows());
        assert!(mat_1.concat_horizontal(&mat_2).is_err());
    }

    /// ensure that concatenation of matrices with mismatching moduli results in
    /// in an error
    #[test]
    fn mismatching_moduli() {
        let mat_1 = MatZq::new(2, 2, 17).unwrap();
        let mat_2 = MatZq::new(2, 2, 19).unwrap();

        let mat_hor = mat_1.concat_horizontal(&mat_2);
        let mat_vert = mat_1.concat_vertical(&mat_2);

        assert!(mat_hor.is_err());
        assert!(mat_vert.is_err());
    }

    /// ensure that vertical concatenation works correctly
    #[test]
    fn vertically_correct() {
        let mat_1 = MatZq::from_str(&format!(
            "[[1, 2, {}],[4, 5, {}]] mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatZq::from_str(&format!("[[-1, 2, -17]] mod {}", u64::MAX)).unwrap();

        let mat_vertical = mat_1.concat_vertical(&mat_2).unwrap();

        let cmp_mat = MatZq::from_str(&format!(
            "[[1, 2, {}],[4, 5, {}],[-1, 2, -17]] mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX,
        ))
        .unwrap();
        assert_eq!(cmp_mat, mat_vertical)
    }

    /// ensure that horizontal concatenation works correctly
    #[test]
    fn horizontally_correct() {
        let mat_1 = MatZq::from_str(&format!(
            "[[1, 2, {}],[4, 5, {}]] mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let mat_2 = MatZq::from_str(&format!("[[-1, 2],[4, 5]] mod {}", u64::MAX)).unwrap();

        let mat_horizontal = mat_1.concat_horizontal(&mat_2).unwrap();

        let cmp_mat = MatZq::from_str(&format!(
            "[[1, 2, {}, -1, 2],[4, 5, {}, 4, 5]] mod {}",
            i64::MIN,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        assert_eq!(cmp_mat, mat_horizontal)
    }
}
