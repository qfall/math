// Copyright 2023 Jan Niklas Siemer
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
    macros::seeded::seedable_function,
    traits::{MatrixDimensions, MatrixSetEntry},
    utils::sample::uniform::UniformIntegerSampler,
};
use std::fmt::Display;

impl MatZ {
    seedable_function!(
        /// Outputs a [`MatZ`] instance with entries chosen uniform at random
        /// in `[lower_bound, upper_bound)`.
        ///
        /// The internally used uniform at random chosen bytes are generated
        #[unseeded]
        /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and is
        #[seeded]
        /// by a [`StdRng`](rand::rngs::StdRng) seeded with `seed`, which uses ChaCha12 and is
        #[optionally_seeded]
        /// by a [`StdRng`](rand::rngs::StdRng) seeded with `seed` or by [`ThreadRng`](rand::rngs::ThreadRng)
        #[optionally_seeded]
        /// if `seed` is `None`. Both use ChaCha12 and are
        /// considered cryptographically secure.
        ///
        /// Parameters:
        /// - `num_rows`: specifies the number of rows the new matrix should have
        /// - `num_cols`: specifies the number of columns the new matrix should have
        /// - `lower_bound`: specifies the included lower bound of the
        ///   interval over which is sampled
        /// - `upper_bound`: specifies the excluded upper bound of the
        ///   interval over which is sampled
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns a new [`MatZ`] instance with entries chosen
        /// uniformly at random in `[lower_bound, upper_bound)` or a [`MathError`]
        /// if the dimensions of the matrix or the interval were chosen too small.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer::MatZ;
        ///
        #[unseeded]
        /// let matrix = MatZ::sample_uniform(3, 3, 17, 26).unwrap();
        #[seeded]
        /// let matrix = MatZ::sample_uniform_seeded(3, 3, 17, 26, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
        ///   if the given `upper_bound` isn't at least larger than `lower_bound`.
        ///
        /// # Panics ...
        /// - if the provided number of rows and columns are not suited to create a matrix.
        ///   For further information see [`MatZ::new`].
        pub(crate) fn sample_uniform(
            num_rows: impl TryInto<i64> + Display,
            num_cols: impl TryInto<i64> + Display,
            lower_bound: impl Into<Z>,
            upper_bound: impl Into<Z>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let lower_bound: Z = lower_bound.into();
            let upper_bound: Z = upper_bound.into();
            let mut matrix = MatZ::new(num_rows, num_cols);

            let interval_size = &upper_bound - &lower_bound;
            let mut uis = UniformIntegerSampler::init(&interval_size, seed)?;
            for row in 0..matrix.get_num_rows() {
                for col in 0..matrix.get_num_columns() {
                    let sample = uis.sample();
                    unsafe { matrix.set_entry_unchecked(row, col, &lower_bound + sample) };
                }
            }

            Ok(matrix)
        }
    );
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::traits::{MatrixDimensions, MatrixGetEntry};
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
    /// or too large for an [`i64`] results in an error.
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
        let lb_0 = Z::from(i64::MIN);
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
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from(7);
        let z = Z::from(7);

        let _ = MatZ::sample_uniform(1, 1, 0u16, 7u8);
        let _ = MatZ::sample_uniform(1, 1, 0u32, 7u16);
        let _ = MatZ::sample_uniform(1, 1, 0u64, 7u32);
        let _ = MatZ::sample_uniform(1, 1, 0i8, 7u64);
        let _ = MatZ::sample_uniform(1, 1, 0i16, 7i8);
        let _ = MatZ::sample_uniform(1, 1, 0i32, 7i16);
        let _ = MatZ::sample_uniform(1, 1, 0i64, 7i32);
        let _ = MatZ::sample_uniform(1, 1, &Z::ZERO, 7i64);
        let _ = MatZ::sample_uniform(1, 1, 0u8, &modulus);
        let _ = MatZ::sample_uniform(1, 1, 0, &z);
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

#[cfg(test)]
mod test_sample_uniform_seeded {
    use crate::traits::{MatrixDimensions, MatrixGetEntry};
    use crate::utils::sample::test_seed;
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
            let matrix =
                MatZ::sample_uniform_seeded(1, 1, &lower_bound, &upper_bound, test_seed()).unwrap();
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
            let matrix =
                MatZ::sample_uniform_seeded(1, 1, &lower_bound, &upper_bound, test_seed()).unwrap();
            let sample = matrix.get_entry(0, 0).unwrap();
            assert!(lower_bound <= sample);
            assert!(sample < upper_bound);
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too large for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let lower_bound = Z::from(-15);
        let upper_bound = Z::from(15);

        let _ = MatZ::sample_uniform_seeded(0, 3, &lower_bound, &upper_bound, test_seed());
    }

    /// Checks whether providing an invalid interval results in an error.
    #[test]
    fn invalid_interval() {
        let lb_0 = Z::from(i64::MIN);
        let lb_1 = Z::from(i64::MIN);
        let lb_2 = Z::ZERO;
        let upper_bound = Z::from(i64::MIN);

        let mat_0 = MatZ::sample_uniform_seeded(3, 3, &lb_0, &upper_bound, test_seed());
        let mat_1 = MatZ::sample_uniform_seeded(4, 1, &lb_1, &upper_bound, test_seed());
        let mat_2 = MatZ::sample_uniform_seeded(1, 5, &lb_2, &upper_bound, test_seed());

        assert!(mat_0.is_err());
        assert!(mat_1.is_err());
        assert!(mat_2.is_err());
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from(7);
        let z = Z::from(7);

        let _ = MatZ::sample_uniform_seeded(1, 1, 0u16, 7u8, test_seed());
        let _ = MatZ::sample_uniform_seeded(1, 1, 0u32, 7u16, test_seed());
        let _ = MatZ::sample_uniform_seeded(1, 1, 0u64, 7u32, test_seed());
        let _ = MatZ::sample_uniform_seeded(1, 1, 0i8, 7u64, test_seed());
        let _ = MatZ::sample_uniform_seeded(1, 1, 0i16, 7i8, test_seed());
        let _ = MatZ::sample_uniform_seeded(1, 1, 0i32, 7i16, test_seed());
        let _ = MatZ::sample_uniform_seeded(1, 1, 0i64, 7i32, test_seed());
        let _ = MatZ::sample_uniform_seeded(1, 1, &Z::ZERO, 7i64, test_seed());
        let _ = MatZ::sample_uniform_seeded(1, 1, 0u8, &modulus, test_seed());
        let _ = MatZ::sample_uniform_seeded(1, 1, 0, &z, test_seed());
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let lower_bound = Z::from(-15);
        let upper_bound = Z::from(15);

        let mat_0 =
            MatZ::sample_uniform_seeded(3, 3, &lower_bound, &upper_bound, test_seed()).unwrap();
        let mat_1 =
            MatZ::sample_uniform_seeded(4, 1, &lower_bound, &upper_bound, test_seed()).unwrap();
        let mat_2 =
            MatZ::sample_uniform_seeded(1, 5, &lower_bound, &upper_bound, test_seed()).unwrap();
        let mat_3 =
            MatZ::sample_uniform_seeded(15, 20, &lower_bound, &upper_bound, test_seed()).unwrap();

        assert_eq!(3, mat_0.get_num_rows());
        assert_eq!(3, mat_0.get_num_columns());
        assert_eq!(4, mat_1.get_num_rows());
        assert_eq!(1, mat_1.get_num_columns());
        assert_eq!(1, mat_2.get_num_rows());
        assert_eq!(5, mat_2.get_num_columns());
        assert_eq!(15, mat_3.get_num_rows());
        assert_eq!(20, mat_3.get_num_columns());
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer::MatZ;
        let sample_0 = MatZ::sample_uniform_seeded(3, 3, 17, 26, [42; 32]).unwrap();
        let sample_1 = MatZ::sample_uniform_seeded(3, 3, 17, 26, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }
}
