// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Contains functions to sort [`MatPolynomialRingZq`].

use crate::integer_mod_q::MatPolynomialRingZq;
use crate::{
    error::MathError,
    traits::{MatrixDimensions, MatrixGetSubmatrix, MatrixSetSubmatrix},
};

impl MatPolynomialRingZq {
    /// Sorts the columns of the matrix based on some condition defined by `cond_func` in an ascending order.
    ///
    /// This condition is usually a norm with the described input-output behaviour.
    ///
    /// Parameters:
    /// - `cond_func`: computes values implementing [`Ord`] over the columns of the specified matrix.
    ///   These values are then used to re-order / sort the rows of the matrix.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// A [`MathError`] is returned if the execution of `cond_func` returned an error.
    ///
    /// # Examples
    /// ## Use a build-in function as condition
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use std::str::FromStr;
    /// let mat = MatPolynomialRingZq::from_str("[[2  3 4, 1  2, 1  1]] / 3  1 2 3 mod 17").unwrap();
    /// let cmp = MatPolynomialRingZq::from_str("[[1  1, 1  2, 2  3 4]] / 3  1 2 3 mod 17").unwrap();
    ///
    /// let sorted = mat.sort_by_column(MatPolynomialRingZq::norm_eucl_sqrd).unwrap();
    ///
    /// assert_eq!(cmp, sorted);
    /// ```
    /// ## Use a custom function as condition
    /// This function needs to take a column vector as input and output a type implementing [`PartialOrd`]
    /// ```
    /// use qfall_math::{integer_mod_q::MatPolynomialRingZq, integer::{PolyOverZ, Z}, error::MathError, traits::{MatrixDimensions, MatrixGetEntry}};
    /// use crate::qfall_math::traits::GetCoefficient;
    /// use std::str::FromStr;
    /// let mat = MatPolynomialRingZq::from_str("[[2  0 4, 1  2, 1  1]] / 3  1 2 3 mod 17").unwrap();
    /// let cmp = MatPolynomialRingZq::from_str("[[2  0 4, 1  1, 1  2]] / 3  1 2 3 mod 17").unwrap();
    ///
    /// fn custom_cond_func(matrix: &MatPolynomialRingZq) -> Result<Z, MathError> {
    ///     let mut sum = Z::ZERO;
    ///     for entry in matrix.get_entries_rowwise() {
    ///         sum += PolyOverZ::get_coeff(&entry, 0)?;
    ///     }
    ///     Ok(sum)
    /// }
    ///
    /// let sorted = mat.sort_by_column(custom_cond_func).unwrap();
    ///
    /// assert_eq!(cmp, sorted);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of the same type as `cond_func` if the execution of `cond_func` fails.
    pub fn sort_by_column<T: Ord>(
        &self,
        cond_func: fn(&Self) -> Result<T, MathError>,
    ) -> Result<Self, MathError> {
        let mut condition_values = vec![];
        for col in 0..self.get_num_columns() {
            condition_values.push(cond_func(&unsafe { self.get_column_unchecked(col) })?);
        }

        let mut id_vec: Vec<usize> = (0..self.get_num_columns() as usize).collect();
        id_vec.sort_by_key(|x| &condition_values[*x]);

        let mut out = Self::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());
        for (col, item) in id_vec.iter().enumerate() {
            out.set_column(col, self, *item).unwrap();
        }

        Ok(out)
    }

    /// Sorts the rows of the matrix based on some condition defined by `cond_func` in an ascending order.
    ///
    /// This condition is usually a norm with the described input-output behaviour.
    ///
    /// Parameters:
    /// - `cond_func`: computes values implementing [`Ord`] over the columns of the specified matrix.
    ///   These values are then used to re-order / sort the columns of the matrix.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// A [`MathError`] is returned if the execution of `cond_func` returned an error.
    ///
    /// # Examples
    /// ## Use a build-in function as condition
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use std::str::FromStr;
    /// let mat = MatPolynomialRingZq::from_str("[[2  3 4],[1  2],[1  1]] / 3  1 2 3 mod 17").unwrap();
    /// let cmp = MatPolynomialRingZq::from_str("[[1  1],[1  2],[2  3 4]] / 3  1 2 3 mod 17").unwrap();
    ///
    /// let sorted = mat.sort_by_row(MatPolynomialRingZq::norm_infty).unwrap();
    ///
    /// assert_eq!(cmp, sorted);
    /// ```
    /// ## Use a custom function as condition
    /// This function needs to take a row vector as input and output a type implementing [`PartialOrd`]
    /// ```
    /// use qfall_math::{integer_mod_q::MatPolynomialRingZq, integer::{PolyOverZ, Z}, error::MathError, traits::{MatrixDimensions, MatrixGetEntry}};
    /// use crate::qfall_math::traits::GetCoefficient;
    /// use std::str::FromStr;
    /// let mat = MatPolynomialRingZq::from_str("[[2  0 4],[1  2],[1  1]] / 3  1 2 3 mod 17").unwrap();
    /// let cmp = MatPolynomialRingZq::from_str("[[2  0 4],[1  1],[1  2]] / 3  1 2 3 mod 17").unwrap();
    ///
    /// fn custom_cond_func(matrix: &MatPolynomialRingZq) -> Result<Z, MathError> {
    ///     let mut sum = Z::ZERO;
    ///     for entry in matrix.get_entries_columnwise() {
    ///         sum += PolyOverZ::get_coeff(&entry, 0)?;
    ///     }
    ///     Ok(sum)
    /// }
    ///
    /// let sorted = mat.sort_by_row(custom_cond_func).unwrap();
    ///
    /// assert_eq!(cmp, sorted);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of the same type as `cond_func` if the execution of `cond_func` fails.
    pub fn sort_by_row<T: Ord>(
        &self,
        cond_func: fn(&Self) -> Result<T, MathError>,
    ) -> Result<Self, MathError> {
        let mut condition_values = vec![];
        for row in 0..self.get_num_rows() {
            condition_values.push(cond_func(&self.get_row(row).unwrap())?);
        }
        let mut id_vec: Vec<usize> = (0..self.get_num_rows() as usize).collect();
        id_vec.sort_by_key(|x| &condition_values[*x]);

        let mut out = Self::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());
        for (row, item) in id_vec.iter().enumerate() {
            out.set_row(row, self, *item).unwrap();
        }

        Ok(out)
    }
}

#[cfg(test)]
mod test_sort_by_length {
    use crate::error::{MathError, StringConversionError};
    use crate::integer_mod_q::MatPolynomialRingZq;
    use std::str::FromStr;

    /// This function should fail in any case a vector is provided to it.
    /// As `sort_by_column` and `sort_by_row` execute this function on the columns resp. rows of its matrix,
    /// it should always return an error if used as `cond_func` for these two functions
    fn failing_func(matrix: &MatPolynomialRingZq) -> Result<(), MathError> {
        if matrix.is_vector() {
            Err(StringConversionError::InvalidMatrix(String::from(
                "Some silly mistake was made - on purpose",
            )))?
        } else {
            Ok(())
        }
    }

    /// Checks whether sorting by column length acc. to eucl. norm works correct for small entries
    #[test]
    fn column_norm_eucl_sqrd_small_entries() {
        let mat = MatPolynomialRingZq::from_str(
            "[[1  3, 0, 1  2, 1  -1],[1  2, 1  2, 1  2, 1  2]] / 3  1 2 3 mod 17",
        )
        .unwrap();
        let cmp = MatPolynomialRingZq::from_str(
            "[[0, 1  -1, 1  2, 1  3],[1  2, 1  2, 1  2, 1  2]] / 3  1 2 3 mod 17",
        )
        .unwrap();

        let res = mat
            .sort_by_column(MatPolynomialRingZq::norm_eucl_sqrd)
            .unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether sorting by column length acc. to eucl. norm works correct for large entries
    #[test]
    fn column_norm_eucl_sqrd_large_entries() {
        let mat = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 1  {}, 1  5],[1  1, 1  2, 1  5],[0, 0, 0]] / 3  1 2 3 mod {}",
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 1  5, 1  {}],[1  1, 1  5, 1  2],[0, 0, 0]] / 3  1 2 3 mod {}",
            i64::MAX,
            u64::MAX
        ))
        .unwrap();

        let res = mat
            .sort_by_column(MatPolynomialRingZq::norm_eucl_sqrd)
            .unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether sorting by columns length acc. to eucl. norm works properly
    /// for matrices with a few more entries
    #[test]
    fn many_columns() {
        let mat = MatPolynomialRingZq::from_str(
            "[[1  3, 1  4, 1  1, 1  7, 1  2, 0, 1  9, 1  -8, 1  6, 1  5]] / 3  1 2 3 mod 17",
        )
        .unwrap();
        let cmp = MatPolynomialRingZq::from_str(
            "[[0, 1  1, 1  2, 1  3, 1  4, 1  5, 1  6, 1  7, 1  -8, 1  9]] / 3  1 2 3 mod 17",
        )
        .unwrap();

        let res = mat
            .sort_by_column(MatPolynomialRingZq::norm_eucl_sqrd)
            .unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether an error is returned for sorting by columns if the `cond_func` returns an error
    #[test]
    fn column_error_cond_func() {
        let mat =
            MatPolynomialRingZq::from_str("[[1  1, 1  2],[1  3, 1  4]] / 3  1 2 3 mod 17").unwrap();

        let res = mat.sort_by_column(failing_func);

        assert!(res.is_err());
    }

    /// Checks whether sorting by row length acc. to eucl. norm works correct for small entries
    #[test]
    fn row_norm_eucl_sqrd_small_entries() {
        let mat = MatPolynomialRingZq::from_str(
            "[[1  3, 0, 1  2, 1  -1],[1  2, 1  2, 1  2, 1  2]] / 3  1 2 3 mod 17",
        )
        .unwrap();
        let cmp = MatPolynomialRingZq::from_str(
            "[[1  3, 0, 1  2, 1  -1],[1  2, 1  2, 1  2, 1  2]] / 3  1 2 3 mod 17",
        )
        .unwrap();

        let res = mat
            .sort_by_row(MatPolynomialRingZq::norm_eucl_sqrd)
            .unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether sorting by row length acc. to eucl. norm works correct for large entries
    #[test]
    fn row_norm_eucl_sqrd_large_entries() {
        let mat = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 0, 1  5],[1  {}, 1  2, 1  5],[0, 0, 0]] / 3  1 2 3 mod {}",
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatPolynomialRingZq::from_str(&format!(
            "[[0, 0, 0],[1  1, 0, 1  5],[1  {}, 1  2, 1  5]] / 3  1 2 3 mod {}",
            i64::MAX,
            u64::MAX
        ))
        .unwrap();

        let res = mat
            .sort_by_row(MatPolynomialRingZq::norm_eucl_sqrd)
            .unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether sorting by rows length acc. to eucl. norm works properly
    /// for matrices with a few more entries
    #[test]
    fn many_rows() {
        let mat =
            MatPolynomialRingZq::from_str("[[1  3],[0],[1  -1],[1  -7],[1  2],[1  9],[1  4],[1  8],[1  6],[1  5]] / 3  1 2 3 mod 82").unwrap();
        let cmp =
            MatPolynomialRingZq::from_str("[[0],[1  -1],[1  2],[1  3],[1  4],[1  5],[1  6],[1  -7],[1  8],[1  9]] / 3  1 2 3 mod 82").unwrap();

        let res = mat
            .sort_by_row(MatPolynomialRingZq::norm_eucl_sqrd)
            .unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether an error is returned for sorting by rows if the `cond_func` returns an error
    #[test]
    fn row_error_cond_func() {
        let mat =
            MatPolynomialRingZq::from_str("[[1  1, 1  2],[1  3, 1  4]] / 3  1 2 3 mod 17").unwrap();

        let res = mat.sort_by_row(failing_func);

        assert!(res.is_err());
    }
}
