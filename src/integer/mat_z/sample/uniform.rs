// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for uniform distributions.

use crate::{
    error::MathError,
    integer::{MatZ, Z},
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::sample::uniform::sample_uniform_rejection,
};
use std::fmt::Display;

impl MatZ {
    /// Outputs a [`MatZ`] instance with entries chosen uniform at random
    /// in `[lower_bound, upper_bound)`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `num_rows`: specifies the number of rows the new matrix should have
    /// - `num_cols`: specifies the number of columns the new matrix should have
    /// - `lower_bound`: specifies the included lower bound of the
    /// interval over which is sampled
    /// - `upper_bound`: specifies the excluded upper bound of the
    /// interval over which is sampled
    ///
    /// Returns a new [`MatZ`] instance with entries chosen
    /// uniformly at random in `[lower_bound, upper_bound)` or a [`MathError`]
    /// if the dimensions of the matrix or the interval were chosen too small.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let matrix = MatZ::sample_uniform(3, 3, &17, &26).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    /// if the given `upper_bound` isn't at least bigger than `lower_bound + 1`,
    /// i.e. the interval size is at most `1`.
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    /// For further information see [`MatZ::new`].
    pub fn sample_uniform<T1, T2>(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        lower_bound: &T1,
        upper_bound: &T2,
    ) -> Result<Self, MathError>
    where
        T1: Into<Z> + Clone,
        T2: Into<Z> + Clone,
    {
        let lower_bound: Z = lower_bound.to_owned().into();
        let upper_bound: Z = upper_bound.to_owned().into();
        let mut matrix = MatZ::new(num_rows, num_cols);

        let interval_size = &upper_bound - &lower_bound;
        for row in 0..matrix.get_num_rows() {
            for col in 0..matrix.get_num_columns() {
                let sample = sample_uniform_rejection(&interval_size)?;
                matrix.set_entry(row, col, &lower_bound + sample).unwrap();
            }
        }

        Ok(matrix)
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::traits::{GetEntry, GetNumColumns, GetNumRows};
    use crate::{
        integer::{MatZ, Z},
        integer_mod_q::Modulus,
    };

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        let lower_bound = Z::from(17);
        let upper_bound = Z::from(32);
        for _ in 0..32 {
            let matrix = MatZ::sample_uniform(1, 1, &lower_bound, &upper_bound).unwrap();
            let sample = matrix.get_entry(0, 0).unwrap();
            assert!(lower_bound <= sample);
            assert!(sample < upper_bound);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large intervals.
    #[test]
    fn boundaries_kept_large() {
        let lower_bound = Z::from(i64::MIN) - Z::from(u64::MAX);
        let upper_bound = Z::from(i64::MIN);
        for _ in 0..256 {
            let matrix = MatZ::sample_uniform(1, 1, &lower_bound, &upper_bound).unwrap();
            let sample = matrix.get_entry(0, 0).unwrap();
            assert!(lower_bound <= sample);
            assert!(sample < upper_bound);
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let lower_bound = Z::from(-15);
        let upper_bound = Z::from(15);

        let _ = MatZ::sample_uniform(0, 3, &lower_bound, &upper_bound);
    }

    /// Checks whether providing an invalid interval results in an error.
    #[test]
    fn invalid_interval() {
        let lb_0 = Z::from(i64::MIN) - Z::ONE;
        let lb_1 = Z::from(i64::MIN);
        let lb_2 = Z::ZERO;
        let upper_bound = Z::from(i64::MIN);

        let mat_0 = MatZ::sample_uniform(3, 3, &lb_0, &upper_bound);
        let mat_1 = MatZ::sample_uniform(4, 1, &lb_1, &upper_bound);
        let mat_2 = MatZ::sample_uniform(1, 5, &lb_2, &upper_bound);

        assert!(mat_0.is_err());
        assert!(mat_1.is_err());
        assert!(mat_2.is_err());
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing Into<Z> + Clone, i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::try_from_z(&Z::from(7)).unwrap();
        let z = Z::from(7);

        let _ = MatZ::sample_uniform(1, 1, &0u16, &7u8);
        let _ = MatZ::sample_uniform(1, 1, &0u32, &7u16);
        let _ = MatZ::sample_uniform(1, 1, &0u64, &7u32);
        let _ = MatZ::sample_uniform(1, 1, &0i8, &7u64);
        let _ = MatZ::sample_uniform(1, 1, &0i16, &7i8);
        let _ = MatZ::sample_uniform(1, 1, &0i32, &7i16);
        let _ = MatZ::sample_uniform(1, 1, &0i64, &7i32);
        let _ = MatZ::sample_uniform(1, 1, &Z::ZERO, &7i64);
        let _ = MatZ::sample_uniform(1, 1, &0u8, &modulus);
        let _ = MatZ::sample_uniform(1, 1, &0, &z);
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let lower_bound = Z::from(-15);
        let upper_bound = Z::from(15);

        let mat_0 = MatZ::sample_uniform(3, 3, &lower_bound, &upper_bound).unwrap();
        let mat_1 = MatZ::sample_uniform(4, 1, &lower_bound, &upper_bound).unwrap();
        let mat_2 = MatZ::sample_uniform(1, 5, &lower_bound, &upper_bound).unwrap();
        let mat_3 = MatZ::sample_uniform(15, 20, &lower_bound, &upper_bound).unwrap();

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
