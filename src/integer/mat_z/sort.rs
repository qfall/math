// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Contains functions to sort [`MatZ`] by.

use super::MatZ;
use crate::{
    error::MathError,
    traits::{GetNumColumns, GetNumRows},
    utils::sort::quicksort,
};

impl MatZ {
    #[allow(clippy::needless_range_loop)]
    /// Sorts the matrix based on some via `cond_func` specified condition of its columns.
    ///
    /// This condition is usually a norm with the described input-output behaviour.
    ///
    /// Paramters:
    /// - `cond_func`: computes values implementing [`PartialOrd`] over the columns of the specified matrix.
    /// These values are then used to re-order / sort the rows of the matrix.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// A [`MathError`] is returned if the execution of `cond_func` returned an error.
    ///
    /// # Examples
    /// ## Use a build-in function as condition
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    /// let mat = MatZ::from_str("[[3,2,1]]").unwrap();
    /// let cmp = MatZ::from_str("[[1,2,3]]").unwrap();
    ///
    /// let sorted = mat.sort_by_column(MatZ::norm_eucl_sqrd).unwrap();
    ///
    /// assert_eq!(cmp, sorted);
    /// ```
    /// ## Use a custom function as condition
    /// This function needs to take a column vector as input and output a type implementing [`PartialOrd`]
    /// ```
    /// use qfall_math::{integer::{MatZ, Z}, error::MathError, traits::{GetNumRows, GetEntry}};
    /// use std::str::FromStr;
    /// let mat = MatZ::from_str("[[3,2,1]]").unwrap();
    /// let cmp = MatZ::from_str("[[1,2,3]]").unwrap();
    ///
    /// fn custom_cond_func(matrix: &MatZ) -> Result<Z, MathError> {
    ///     let mut sum = Z::ZERO;
    ///     for row in 0..matrix.get_num_rows() {
    ///         sum = sum + matrix.get_entry(row, 0)?;
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
    pub fn sort_by_column<T>(
        &self,
        cond_func: fn(&Self) -> Result<T, MathError>,
    ) -> Result<Self, MathError>
    where
        T: PartialOrd,
    {
        let mut lengths = vec![];
        for col in 0..self.get_num_columns() {
            lengths.push(cond_func(&self.get_column(col).unwrap())?);
        }
        let length = lengths.len() - 1;
        let mut id_vec: Vec<usize> = (0..self.get_num_columns() as usize).collect();
        quicksort(&mut lengths, 0, length, &mut id_vec);

        let mut out = Self::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        for col in 0..id_vec.len() {
            out.set_column(col, self, id_vec[col]).unwrap();
        }

        Ok(out)
    }

    #[allow(clippy::needless_range_loop)]
    /// Sorts the matrix based on some via `cond_func` specified condition of its rows.
    ///
    /// This condition is usually a norm with the described input-output behaviour.
    ///
    /// Paramters:
    /// - `cond_func`: computes values implementing [`PartialOrd`] over the columns of the specified matrix.
    /// These values are then used to re-order / sort the columns of the matrix.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// A [`MathError`] is returned if the execution of `cond_func` returned an error.
    ///
    /// # Examples
    /// ## Use a build-in function as condition
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    /// let mat = MatZ::from_str("[[3],[2],[1]]").unwrap();
    /// let cmp = MatZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// let sorted = mat.sort_by_row(MatZ::norm_infty).unwrap();
    ///
    /// assert_eq!(cmp, sorted);
    /// ```
    /// ## Use a custom function as condition
    /// This function needs to take a row vector as input and output a type implementing [`PartialOrd`]
    /// ```
    /// use qfall_math::{integer::{MatZ, Z}, error::MathError, traits::{GetNumColumns, GetEntry}};
    /// use std::str::FromStr;
    /// let mat = MatZ::from_str("[[3],[2],[1]]").unwrap();
    /// let cmp = MatZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// fn custom_cond_func(matrix: &MatZ) -> Result<Z, MathError> {
    ///     let mut sum = Z::ZERO;
    ///     for col in 0..matrix.get_num_columns() {
    ///         sum = sum + matrix.get_entry(0, col)?;
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
    pub fn sort_by_row<T>(
        &self,
        cond_func: fn(&Self) -> Result<T, MathError>,
    ) -> Result<Self, MathError>
    where
        T: PartialOrd,
    {
        let mut lengths = vec![];
        for row in 0..self.get_num_rows() {
            lengths.push(cond_func(&self.get_row(row).unwrap())?);
        }
        let last_element = lengths.len() - 1;
        let mut id_vec: Vec<usize> = (0..self.get_num_rows() as usize).collect();
        quicksort(&mut lengths, 0, last_element, &mut id_vec);

        let mut out = Self::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        for row in 0..id_vec.len() {
            out.set_row(row, self, id_vec[row]).unwrap();
        }

        Ok(out)
    }
}

#[cfg(test)]
mod test_sort_by_length {
    use super::MatZ;
    use crate::error::MathError;
    use std::str::FromStr;

    /// This function should fail in any case a vector is provided to it.
    /// As `sort_by_column` and `sort_by_row` execute this function on the columns resp. rows of its matrix,
    /// it should always return an error if used as `cond_func` for these two functions
    fn failing_func(matrix: &MatZ) -> Result<(), MathError> {
        if matrix.is_vector() {
            Err(MathError::InvalidMatrix(String::from(
                "Some silly mistake was made - on purpose",
            )))
        } else {
            Ok(())
        }
    }

    /// Checks whether sorting by column length acc. to eucl. norm works correct for small entries
    #[test]
    fn column_norm_eucl_sqrd_small_entries() {
        let mat = MatZ::from_str("[[3,0,2,-1],[2,2,2,2]]").unwrap();
        let cmp = MatZ::from_str("[[0,-1,2,3],[2,2,2,2]]").unwrap();

        let res = mat.sort_by_column(MatZ::norm_eucl_sqrd).unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether sorting by column length acc. to eucl. norm works correct for large entries
    #[test]
    fn column_norm_eucl_sqrd_large_entries() {
        let mat =
            MatZ::from_str(&format!("[[{},{},5],[1,2,5],[0,0,0]]", i64::MIN, i64::MAX)).unwrap();
        let cmp =
            MatZ::from_str(&format!("[[5,{},{}],[5,2,1],[0,0,0]]", i64::MAX, i64::MIN)).unwrap();

        let res = mat.sort_by_column(MatZ::norm_eucl_sqrd).unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether sorting by column length acc. to infty norm works correct for large entries
    #[test]
    fn column_norm_infty_large_entries() {
        let mat =
            MatZ::from_str(&format!("[[{},{},5],[1,2,5],[0,0,0]]", i64::MIN, i64::MAX)).unwrap();
        let cmp =
            MatZ::from_str(&format!("[[5,{},{}],[5,2,1],[0,0,0]]", i64::MAX, i64::MIN)).unwrap();

        let res = mat.sort_by_column(MatZ::norm_infty).unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether sorting by columns length acc. to eucl. norm works properly
    /// for matrices with a few more entries
    #[test]
    fn many_columns() {
        let mat = MatZ::from_str("[[3,4,1,7,2,0,9,-8,6,5]]").unwrap();
        let cmp = MatZ::from_str("[[0,1,2,3,4,5,6,7,-8,9]]").unwrap();

        let res = mat.sort_by_column(MatZ::norm_eucl_sqrd).unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether an error is returned for sorting by columns if the `cond_func` returns an error
    #[test]
    fn column_error_cond_func() {
        let mat = MatZ::from_str("[[1,2],[3,4]]").unwrap();

        let res = mat.sort_by_column(failing_func);

        assert!(res.is_err());
    }

    /// Checks whether sorting by row length acc. to eucl. norm works correct for small entries
    #[test]
    fn row_norm_eucl_sqrd_small_entries() {
        let mat = MatZ::from_str("[[3,0,2,-1],[2,2,2,2]]").unwrap();
        let cmp = MatZ::from_str("[[3,0,2,-1],[2,2,2,2]]").unwrap();

        let res = mat.sort_by_row(MatZ::norm_eucl_sqrd).unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether sorting by row length acc. to eucl. norm works correct for large entries
    #[test]
    fn row_norm_eucl_sqrd_large_entries() {
        let mat =
            MatZ::from_str(&format!("[[{},0,5],[{},2,5],[0,0,0]]", i64::MIN, i64::MAX)).unwrap();
        let cmp =
            MatZ::from_str(&format!("[[0,0,0],[{},2,5],[{},0,5]]", i64::MAX, i64::MIN)).unwrap();

        let res = mat.sort_by_row(MatZ::norm_eucl_sqrd).unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether sorting by row length acc. to infty norm works correct for large entries
    #[test]
    fn row_norm_infty_large_entries() {
        let mat =
            MatZ::from_str(&format!("[[{},0,5],[{},2,5],[0,0,0]]", i64::MIN, i64::MAX)).unwrap();
        let cmp =
            MatZ::from_str(&format!("[[0,0,0],[{},2,5],[{},0,5]]", i64::MAX, i64::MIN)).unwrap();

        let res = mat.sort_by_row(MatZ::norm_infty).unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether sorting by rows length acc. to eucl. norm works properly
    /// for matrices with a few more entries
    #[test]
    fn many_rows() {
        let mat = MatZ::from_str("[[3],[0],[-1],[-7],[2],[9],[4],[8],[6],[5]]").unwrap();
        let cmp = MatZ::from_str("[[0],[-1],[2],[3],[4],[5],[6],[-7],[8],[9]]").unwrap();

        let res = mat.sort_by_row(MatZ::norm_eucl_sqrd).unwrap();

        assert_eq!(cmp, res);
    }

    /// Checks whether an error is returned for sorting by rows if the `cond_func` returns an error
    #[test]
    fn row_error_cond_func() {
        let mat = MatZ::from_str("[[1,2],[3,4]]").unwrap();

        let res = mat.sort_by_row(failing_func);

        assert!(res.is_err());
    }
}
