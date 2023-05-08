// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Initialize a [`MatZq`] with common defaults, e.g., zero and identity.

use super::MatZq;
use crate::{error::MathError, integer::Z, integer_mod_q::Modulus, utils::index::evaluate_index};
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
    /// Returns a [`MatZq`] or an error, if the number of rows or columns is
    /// less than `1` or the modulus is less than `1`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::new(5, 10, 7).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the number of rows or columns is `0`.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is negative or it does not fit into an [`i64`].
    /// - Returns a [`MathError`] of type [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the provided value is not greater than `1`.
    pub fn new(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: impl Into<Z>,
    ) -> Result<Self, MathError> {
        // TODO add separate function
        let num_rows_i64 = evaluate_index(num_rows)?;
        let num_cols_i64 = evaluate_index(num_cols)?;

        if num_rows_i64 == 0 || num_cols_i64 == 0 {
            return Err(MathError::InvalidMatrix(format!(
                "({},{})",
                num_rows_i64, num_cols_i64,
            )));
        }

        let modulus = std::convert::Into::<Z>::into(modulus);

        if modulus <= Z::ONE {
            return Err(MathError::InvalidIntToModulus(format!("{}", modulus)));
        }

        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_mod_mat_init(
                matrix.as_mut_ptr(),
                num_rows_i64,
                num_cols_i64,
                &modulus.value,
            );

            Ok(MatZq {
                matrix: matrix.assume_init(),
                // we can unwrap here since modulus > 1 was checked before
                modulus: Modulus::try_from(&modulus).unwrap(),
            })
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
    /// let matrix = MatZq::identity(2, 3, 3).unwrap();
    ///
    /// let identity = MatZq::identity(10, 10, 3).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix) or
    /// [`OutOfBounds`](MathError::OutOfBounds) if the provided number of rows and columns
    /// are not suited to create a matrix. For further information see [`MatZq::new`].
    /// - Returns a [`MathError`] of type [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the modulus is not greater than `1`. For further information see [`MatZq::new`].
    pub fn identity(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: impl Into<Z>,
    ) -> Result<Self, MathError> {
        let mut out = MatZq::new(num_rows, num_cols, modulus)?;
        if Z::ONE != Z::from(&out.modulus) {
            unsafe { fmpz_mod_mat_one(&mut out.matrix) };
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_identity {
    use crate::{integer::Z, integer_mod_q::MatZq, traits::GetEntry};

    /// Tests if an identity matrix is set from a zero matrix.
    #[test]
    fn identity() {
        let matrix = MatZq::identity(10, 10, 3).unwrap();

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
        let matrix = MatZq::identity(10, 7, 3).unwrap();

        for i in 0..10 {
            for j in 0..7 {
                if i != j {
                    assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(Z::ONE, matrix.get_entry(i, j).unwrap())
                }
            }
        }

        let matrix = MatZq::identity(7, 10, 3).unwrap();

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
        let matrix = MatZq::identity(10, 10, i64::MAX).unwrap();

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

    /// Tests if an identity matrix can be created using a modulus of `1`.
    #[test]
    fn modulus_one() {
        let matrix = MatZq::identity(10, 10, 1).unwrap();

        for i in 0..10 {
            for j in 0..10 {
                assert_eq!(Z::ZERO, matrix.get_entry(i, j).unwrap())
            }
        }
    }
}

#[cfg(test)]
mod test_new {
    use crate::{integer::Z, integer_mod_q::MatZq, traits::GetEntry};

    /// Ensure that initialization works.
    #[test]
    fn initialization() {
        assert!(MatZq::new(2, 2, 3).is_ok());
    }

    /// Ensure that entries of a new matrix are `0`.
    #[test]
    fn entry_zero() {
        let matrix = MatZq::new(2, 2, 3).unwrap();

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(0, 1).unwrap();
        let entry3 = matrix.get_entry(1, 0).unwrap();
        let entry4 = matrix.get_entry(1, 1).unwrap();

        assert_eq!(Z::ZERO, entry1);
        assert_eq!(Z::ZERO, entry2);
        assert_eq!(Z::ZERO, entry3);
        assert_eq!(Z::ZERO, entry4);
    }

    /// Ensure that a new zero matrix fails with `0` as input.
    #[test]
    fn error_zero() {
        let matrix1 = MatZq::new(1, 0, 3);
        let matrix2 = MatZq::new(0, 1, 3);
        let matrix3 = MatZq::new(0, 0, 3);

        assert!(matrix1.is_err());
        assert!(matrix2.is_err());
        assert!(matrix3.is_err());
    }

    /// Ensure that an invalid modulus yields an error.
    #[test]
    fn invalid_modulus_error() {
        assert!(MatZq::new(2, 2, -3).is_err());
        assert!(MatZq::new(2, 2, 0).is_err());
    }
}
