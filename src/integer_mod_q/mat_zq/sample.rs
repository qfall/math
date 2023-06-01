// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for different distributions.

use crate::{
    error::MathError,
    integer::Z,
    integer_mod_q::MatZq,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::sample::uniform::sample_uniform_rejection,
};
use std::fmt::Display;

impl MatZq {
    /// Outputs a [`MatZq`] instance with entries chosen uniform at random
    /// in `[0, modulus)`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `num_rows`: specifies the number of rows the new matrix should have
    /// - `num_cols`: specifies the number of columns the new matrix should have
    /// - `modulus`: specifies the modulus of the matrix and defines the interval
    /// over which is sampled
    ///
    /// Returns a new [`MatZq`] instance with entries chosen
    /// uniformly at random in `[0, modulus)` or a [`MathError`]
    /// if the dimensions of the matrix or the modulus were chosen too small.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::sample_uniform(3, 3, &17).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if the number of rows or columns is `0`.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is negative or it does not fit into an [`i64`].
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    /// if the given `modulus` is smaller than or equal to `1`.
    /// - Returns a [`MathError`] of type [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the provided modulus is not greater than `1`.
    pub fn sample_uniform<T>(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: &T,
    ) -> Result<Self, MathError>
    where
        T: Into<Z> + Clone,
    {
        let modulus: Z = modulus.clone().into();
        let mut matrix = MatZq::new(num_rows, num_cols, modulus.clone())?;

        for row in 0..matrix.get_num_rows() {
            for col in 0..matrix.get_num_columns() {
                let sample = sample_uniform_rejection(&modulus)?;
                matrix.set_entry(row, col, sample).unwrap();
            }
        }

        Ok(matrix)
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::traits::{GetEntry, GetNumColumns, GetNumRows};
    use crate::{
        integer::Z,
        integer_mod_q::{MatZq, Modulus},
    };
    use std::str::FromStr;

    /// Checks whether the boundaries of the interval are kept for small moduli.
    #[test]
    fn boundaries_kept_small() {
        for _ in 0..32 {
            let matrix = MatZq::sample_uniform(1, 1, &17).unwrap();
            let sample = matrix.get_entry(0, 0).unwrap();
            assert!(Z::ZERO <= sample);
            assert!(sample < Z::from(17));
        }
    }

    /// Checks whether the boundaries of the interval are kept for large moduli.
    #[test]
    fn boundaries_kept_large() {
        let modulus = Z::from(u64::MAX);
        for _ in 0..256 {
            let matrix = MatZq::sample_uniform(1, 1, &modulus).unwrap();
            let sample = matrix.get_entry(0, 0).unwrap();
            assert!(Z::ZERO <= sample);
            assert!(sample < modulus);
        }
    }

    /// Checks whether providing an invalid interval/ modulus results in an error.
    #[test]
    fn invalid_modulus() {
        let mat_0 = MatZq::sample_uniform(3, 3, &-1);
        let mat_1 = MatZq::sample_uniform(4, 1, &1);
        let mat_2 = MatZq::sample_uniform(1, 5, &0);
        let mat_3 = MatZq::sample_uniform(1, 5, &i32::MIN);
        let mat_4 = MatZq::sample_uniform(1, 5, &Z::from(i64::MIN));

        assert!(mat_0.is_err());
        assert!(mat_1.is_err());
        assert!(mat_2.is_err());
        assert!(mat_3.is_err());
        assert!(mat_4.is_err());
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing Into<Z> + Clone, i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from_str("7").unwrap();
        let z = Z::from(7);

        let _ = MatZq::sample_uniform(1, 1, &7u8);
        let _ = MatZq::sample_uniform(1, 1, &7u16);
        let _ = MatZq::sample_uniform(1, 1, &7u32);
        let _ = MatZq::sample_uniform(1, 1, &7u64);
        let _ = MatZq::sample_uniform(1, 1, &7i8);
        let _ = MatZq::sample_uniform(1, 1, &7i16);
        let _ = MatZq::sample_uniform(1, 1, &7i32);
        let _ = MatZq::sample_uniform(1, 1, &7i64);
        let _ = MatZq::sample_uniform(1, 1, &modulus);
        let _ = MatZq::sample_uniform(1, 1, &z);
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let modulus = Z::from(15);

        let mat_0 = MatZq::sample_uniform(3, 3, &modulus).unwrap();
        let mat_1 = MatZq::sample_uniform(4, 1, &modulus).unwrap();
        let mat_2 = MatZq::sample_uniform(1, 5, &modulus).unwrap();
        let mat_3 = MatZq::sample_uniform(15, 20, &modulus).unwrap();

        assert_eq!(3, mat_0.get_num_rows());
        assert_eq!(3, mat_0.get_num_columns());
        assert_eq!(4, mat_1.get_num_rows());
        assert_eq!(1, mat_1.get_num_columns());
        assert_eq!(1, mat_2.get_num_rows());
        assert_eq!(5, mat_2.get_num_columns());
        assert_eq!(15, mat_3.get_num_rows());
        assert_eq!(20, mat_3.get_num_columns());
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in an error
    #[test]
    fn false_sizes() {
        let modulus = Z::from(15);

        let mat_0 = MatZq::sample_uniform(0, 3, &modulus);
        let mat_1 = MatZq::sample_uniform(3, 0, &modulus);
        let mat_2 = MatZq::sample_uniform(0, -1, &modulus);
        let mat_3 = MatZq::sample_uniform(2, u64::MAX, &modulus);

        assert!(mat_0.is_err());
        assert!(mat_1.is_err());
        assert!(mat_2.is_err());
        assert!(mat_3.is_err());
    }
}
