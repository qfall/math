// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Initialize a [`MatZ`] with common defaults, e.g., zero and identity.

use super::MatZ;
use crate::utils::index::evaluate_indices;
use flint_sys::fmpz_mat::{fmpz_mat_init, fmpz_mat_one};
use std::{fmt::Display, mem::MaybeUninit};

impl MatZ {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns and
    /// zeros as entries.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    ///
    /// Returns a new [`MatZ`] instance of the provided dimensions.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let matrix = MatZ::new(5, 10);
    /// ```
    ///
    /// # Panics ...
    /// - if the number of rows or columns is negative, `0`, or does not fit into an [`i64`].
    pub fn new(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
    ) -> Self {
        let (num_rows_i64, num_cols_i64) = evaluate_indices(num_rows, num_cols).unwrap();

        assert!(
            num_rows_i64 != 0 && num_cols_i64 != 0,
            "A matrix can not contain 0 rows or 0 columns"
        );

        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_mat_init(matrix.as_mut_ptr(), num_rows_i64, num_cols_i64);

            // Construct MatZ from previously initialized fmpz_mat
            MatZ {
                matrix: matrix.assume_init(),
            }
        }
    }

    /// Generate a `num_rows` times `num_columns` matrix with `1` on the
    /// diagonal and `0` anywhere else.
    ///
    /// Parameters:
    /// - `rum_rows`: the number of rows of the identity matrix
    /// - `num_columns`: the number of columns of the identity matrix
    ///
    /// Returns a matrix with `1` across the diagonal and `0` anywhere else.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let matrix = MatZ::identity(2, 3);
    ///
    /// let identity = MatZ::identity(10, 10);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    /// For further information see [`MatZ::new`].
    pub fn identity(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
    ) -> Self {
        let mut out = MatZ::new(num_rows, num_cols);
        unsafe { fmpz_mat_one(&mut out.matrix) };
        out
    }
}

#[cfg(test)]
mod test_new {
    use crate::{
        integer::{MatZ, Z},
        traits::GetEntry,
    };

    /// Ensure that entries of a new matrix are `0`.
    #[test]
    fn entry_zero() {
        let matrix = MatZ::new(2, 2);

        let entry_1 = matrix.get_entry(0, 0).unwrap();
        let entry_2 = matrix.get_entry(0, 1).unwrap();
        let entry_3 = matrix.get_entry(1, 0).unwrap();
        let entry_4 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::ZERO, entry_1);
        assert_eq!(Z::ZERO, entry_2);
        assert_eq!(Z::ZERO, entry_3);
        assert_eq!(Z::ZERO, entry_4);
    }

    /// Ensure that a new zero matrix fails with `0` as `num_cols`.
    #[should_panic]
    #[test]
    fn error_zero_num_cols() {
        let _ = MatZ::new(1, 0);
    }

    /// Ensure that a new zero matrix fails with `0` as `num_rows`.
    #[should_panic]
    #[test]
    fn error_zero_num_rows() {
        let _ = MatZ::new(0, 1);
    }
}

#[cfg(test)]
mod test_identity {
    use crate::{
        integer::{MatZ, Z},
        traits::GetEntry,
    };

    /// Tests if an identity matrix is set from a zero matrix.
    #[test]
    fn identity() {
        let matrix = MatZ::identity(10, 10);

        for i in 0..10 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap());
                }
            }
        }
    }

    /// Tests if function works for a non-square matrix
    #[test]
    fn non_square_works() {
        let matrix = MatZ::identity(10, 7);

        for i in 0..10 {
            for j in 0..7 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap());
                }
            }
        }

        let matrix = MatZ::identity(7, 10);

        for i in 0..7 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap());
                }
            }
        }
    }
}
