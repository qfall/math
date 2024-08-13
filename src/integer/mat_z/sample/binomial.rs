// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling
//! according to the binomial distribution.

use crate::{
    error::MathError,
    integer::{MatZ, Z},
    rational::Q,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::sample::binomial::sample_binomial,
};
use std::fmt::Display;

impl MatZ {
    /// Outputs a [`MatZ`] instance with entries chosen according to the binomial
    /// distribution parameterized by `n` and `p`.
    ///
    /// Parameters:
    /// - `num_rows`: specifies the number of rows the new matrix should have
    /// - `num_cols`: specifies the number of columns the new matrix should have
    /// - `n`: specifies the number of trials
    /// - `p`: specifies the probability of success
    ///
    /// Returns a new [`MatZ`] instance with entries chosen
    /// according to the binomial distribution or a [`MathError`]
    /// if `n < 1`, `p ∉ (0,1)`, `n` does not fit into an [`i64`],
    /// or the dimensions of the matrix were chosen too small.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let sample = MatZ::sample_binomial(2, 2, 5, 0.5).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///     if `n < 1`.
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    ///     if `p ∉ (0,1)`.
    /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
    ///     if `n` does not fit into an [`i64`].
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    ///     For further information see [`MatZ::new`].
    pub fn sample_binomial(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        n: impl Into<Z>,
        p: impl Into<Q>,
    ) -> Result<Self, MathError> {
        Self::sample_binomial_with_offset(num_rows, num_cols, 0, n, p)
    }

    /// Outputs a [`MatZ`] instance with entries chosen according to the binomial
    /// distribution parameterized by `n` and `p` with given `offset`.
    ///
    /// Parameters:
    /// - `num_rows`: specifies the number of rows the new matrix should have
    /// - `num_cols`: specifies the number of columns the new matrix should have
    /// - `offset`: specifies an offset applied to each sample
    ///     collected from the binomial distribution
    /// - `n`: specifies the number of trials
    /// - `p`: specifies the probability of success
    ///
    /// Returns a new [`MatZ`] instance with entries chosen
    /// according to the binomial distribution or a [`MathError`]
    /// if `n < 1`, `p ∉ (0,1)`, `n` does not fit into an [`i64`],
    /// or the dimensions of the matrix were chosen too small.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let sample = MatZ::sample_binomial_with_offset(2, 2, -1, 2, 0.5).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///     if `n < 1`.
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    ///     if `p ∉ (0,1)`.
    /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
    ///     if `n` does not fit into an [`i64`].
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    ///     For further information see [`MatZ::new`].
    pub fn sample_binomial_with_offset(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        offset: impl Into<Z>,
        n: impl Into<Z>,
        p: impl Into<Q>,
    ) -> Result<Self, MathError> {
        let offset: Z = offset.into();
        let n: Z = n.into();
        let p: Q = p.into();
        let mut matrix = MatZ::new(num_rows, num_cols);

        for row in 0..matrix.get_num_rows() {
            for col in 0..matrix.get_num_columns() {
                let sample = sample_binomial(&n, &p)?;
                matrix.set_entry(row, col, &offset + sample).unwrap();
            }
        }

        Ok(matrix)
    }
}

#[cfg(test)]
mod test_sample_binomial {
    use super::{MatZ, Q, Z};
    use crate::traits::{GetEntry, GetNumColumns, GetNumRows};

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        for _ in 0..8 {
            let matrix = MatZ::sample_binomial(1, 1, 2, 0.5).unwrap();
            let sample = matrix.get_entry(0, 0).unwrap();
            assert!(Z::ZERO <= sample);
            assert!(sample <= Z::from(2));
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let _ = MatZ::sample_binomial(0, 3, 1, 0.5);
    }

    /// Checks whether `sample_binomial` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    #[test]
    fn availability() {
        let _ = MatZ::sample_binomial(1, 1, 1u16, 7u8);
        let _ = MatZ::sample_binomial(1, 1, 1u32, 7u16);
        let _ = MatZ::sample_binomial(1, 1, 1u64, 7u32);
        let _ = MatZ::sample_binomial(1, 1, 1i8, 7u64);
        let _ = MatZ::sample_binomial(1, 1, 1i16, 7i8);
        let _ = MatZ::sample_binomial(1, 1, 1i32, 7i16);
        let _ = MatZ::sample_binomial(1, 1, 1i64, 7i32);
        let _ = MatZ::sample_binomial(1, 1, Z::ONE, 7i64);
        let _ = MatZ::sample_binomial(1, 1, 1u8, 0.5f32);
        let _ = MatZ::sample_binomial(1, 1, 1u8, 0.5f64);
        let _ = MatZ::sample_binomial(1, 1, 1, Q::from((1, 2)));
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let mat_0 = MatZ::sample_binomial(3, 3, 1, 0.5).unwrap();
        let mat_1 = MatZ::sample_binomial(4, 1, 1, 0.5).unwrap();
        let mat_2 = MatZ::sample_binomial(1, 5, 1, 0.5).unwrap();
        let mat_3 = MatZ::sample_binomial(15, 20, 1, 0.5).unwrap();

        assert_eq!(3, mat_0.get_num_rows());
        assert_eq!(3, mat_0.get_num_columns());
        assert_eq!(4, mat_1.get_num_rows());
        assert_eq!(1, mat_1.get_num_columns());
        assert_eq!(1, mat_2.get_num_rows());
        assert_eq!(5, mat_2.get_num_columns());
        assert_eq!(15, mat_3.get_num_rows());
        assert_eq!(20, mat_3.get_num_columns());
    }
}

#[cfg(test)]
mod test_sample_binomial_with_offset {
    use super::{MatZ, Q, Z};
    use crate::traits::{GetEntry, GetNumColumns, GetNumRows};

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        for _ in 0..8 {
            let matrix = MatZ::sample_binomial_with_offset(1, 1, -1, 2, 0.5).unwrap();
            let sample = matrix.get_entry(0, 0).unwrap();
            assert!(Z::MINUS_ONE <= sample);
            assert!(sample <= Z::ONE);
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let _ = MatZ::sample_binomial_with_offset(0, 3, 0, 1, 0.5);
    }

    /// Checks whether `sample_binomial_with_offset` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    #[test]
    fn availability() {
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0u8, 1u16, 7u8);
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0u16, 1u32, 7u16);
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0u32, 1u64, 7u32);
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0u64, 1i8, 7u64);
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0i8, 1i16, 7i8);
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0i16, 1i32, 7i16);
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0i64, 1i64, 7i32);
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0, Z::ONE, 7i64);
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0, 1u8, 0.5f32);
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0, 1u8, 0.5f64);
        let _ = MatZ::sample_binomial_with_offset(1, 1, 0, 1, Q::from((1, 2)));
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let mat_0 = MatZ::sample_binomial_with_offset(3, 3, 0, 1, 0.5).unwrap();
        let mat_1 = MatZ::sample_binomial_with_offset(4, 1, 0, 1, 0.5).unwrap();
        let mat_2 = MatZ::sample_binomial_with_offset(1, 5, 0, 1, 0.5).unwrap();
        let mat_3 = MatZ::sample_binomial_with_offset(15, 20, 0, 1, 0.5).unwrap();

        assert_eq!(3, mat_0.get_num_rows());
        assert_eq!(3, mat_0.get_num_columns());
        assert_eq!(4, mat_1.get_num_rows());
        assert_eq!(1, mat_1.get_num_columns());
        assert_eq!(1, mat_2.get_num_rows());
        assert_eq!(5, mat_2.get_num_columns());
        assert_eq!(15, mat_3.get_num_rows());
        assert_eq!(20, mat_3.get_num_columns());
    }
}
