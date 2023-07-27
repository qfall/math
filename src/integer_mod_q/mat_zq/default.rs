// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Initialize a [`MatZq`] with common defaults, e.g., zero and identity.

use super::MatZq;
use crate::{integer::Z, integer_mod_q::Modulus, utils::index::evaluate_indices};
use flint_sys::fmpz_mod_mat::{fmpz_mod_mat_init, fmpz_mod_mat_one};
use std::{fmt::Display, mem::MaybeUninit};

impl MatZq {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns,
    /// zeros as entries and `modulus` as the modulus.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    /// - `modulus`: the common modulus of the matrix entries
    ///
    /// Returns a new [`MatZq`] instance of the provided dimensions.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::new(5, 10, 7);
    /// ```
    ///
    /// # Panics ...
    /// - if the number of rows or columns is negative, zero, or does not fit into an [`i64`].
    /// - if the provided value is not greater than `1`.
    pub fn new(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: impl Into<Modulus>,
    ) -> Self {
        let (num_rows_i64, num_cols_i64) = evaluate_indices(num_rows, num_cols).unwrap();

        assert!(
            num_rows_i64 != 0 && num_cols_i64 != 0,
            "A matrix can not contain 0 rows or 0 columns."
        );

        let modulus: Modulus = modulus.into();

        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_mod_mat_init(
                matrix.as_mut_ptr(),
                num_rows_i64,
                num_cols_i64,
                &modulus.get_fmpz_mod_ctx_struct().n[0],
            );

            MatZq {
                matrix: matrix.assume_init(),
                // we can unwrap here since modulus > 1 was checked before
                modulus,
            }
        }
    }

    /// Generate a `num_rows` times `num_columns` matrix with `1` on the
    /// diagonal and `0` anywhere else with a given modulus (if the modulus is `1`
    /// every entry is `0`).
    ///
    /// Parameters:
    /// - `rum_rows`: the number of rows of the identity matrix
    /// - `num_columns`: the number of columns of the identity matrix
    /// - `modulus`: the modulus of the matrix
    ///
    /// Returns a matrix with `1` across the diagonal and `0` anywhere else.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::identity(2, 3, 3);
    ///
    /// let identity = MatZq::identity(10, 10, 3);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns or the modulus are not suited to create a matrix.
    /// For further information see [`MatZq::new`].
    pub fn identity(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: impl Into<Modulus>,
    ) -> Self {
        let mut out = MatZq::new(num_rows, num_cols, modulus);
        if Z::ONE != Z::from(&out.modulus) {
            unsafe { fmpz_mod_mat_one(&mut out.matrix) };
        }
        out
    }
}

#[cfg(test)]
mod test_identity {
    use crate::{integer::Z, integer_mod_q::MatZq, traits::GetEntry};

    /// Tests if an identity matrix is set from a zero matrix.
    #[test]
    fn identity() {
        let matrix = MatZq::identity(10, 10, 3);

        for i in 0..10 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }
    }

    /// Tests if function works for a non-square matrix
    #[test]
    fn non_square_works() {
        let matrix = MatZq::identity(10, 7, 3);

        for i in 0..10 {
            for j in 0..7 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }

        let matrix = MatZq::identity(7, 10, 3);

        for i in 0..7 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }
    }

    /// Tests if an identity matrix can be created using a large modulus.
    #[test]
    fn modulus_large() {
        let matrix = MatZq::identity(10, 10, i64::MAX);

        for i in 0..10 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }
    }

    /// Assert that a modulus of `1` is not allowed.
    #[should_panic]
    #[test]
    fn modulus_one() {
        let _ = MatZq::identity(10, 10, 1);
    }
}

#[cfg(test)]
mod test_new {
    use crate::{integer::Z, integer_mod_q::MatZq, traits::GetEntry};

    /// Ensure that initialization works.
    #[test]
    fn initialization() {
        let _ = MatZq::new(2, 2, 3);
    }

    /// Ensure that entries of a new matrix are `0`.
    #[test]
    fn entry_zero() {
        let matrix = MatZq::new(2, 2, 3);

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(0, 1).unwrap();
        let entry3 = matrix.get_entry(1, 0).unwrap();
        let entry4 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::ZERO, entry1);
        assert_eq!(Z::ZERO, entry2);
        assert_eq!(Z::ZERO, entry3);
        assert_eq!(Z::ZERO, entry4);
    }

    /// Ensure that a new zero matrix fails with `0` as `num_cols`.
    #[should_panic]
    #[test]
    fn error_zero_num_cols() {
        let _ = MatZq::new(1, 0, 3);
    }

    /// Ensure that a new zero matrix fails with `0` as `num_rows`.
    #[should_panic]
    #[test]
    fn error_zero_num_rows() {
        let _ = MatZq::new(0, 1, 3);
    }

    /// Ensure that an invalid modulus yields an error.
    #[should_panic]
    #[test]
    fn invalid_modulus_error() {
        let _ = MatZq::new(2, 2, 1);
    }

    /// Ensure that a negative modulus yields an error.
    #[should_panic]
    #[test]
    fn negative_modulus_error() {
        let _ = MatZq::new(2, 2, -3);
    }
}
