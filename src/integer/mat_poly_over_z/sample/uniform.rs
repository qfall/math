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
    integer::{MatPolyOverZ, PolyOverZ, Z},
    macros::seeded::seedable_function,
    traits::{MatrixDimensions, MatrixSetEntry},
    utils::index::evaluate_index,
    utils::sample::uniform::SamplerRng,
};
use std::fmt::Display;

impl MatPolyOverZ {
    seedable_function!(
        /// Outputs a [`MatPolyOverZ`] instance with polynomials as entries,
        /// whose coefficients were chosen uniform at random in `[lower_bound, upper_bound)`.
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
        /// - `max_degree`: specifies the maximum length of all polynomials in the matrix,
        ///   i.e. the maximum number of coefficients any polynomial in the matrix can have
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
        /// Returns a new [`MatPolyOverZ`] instance with polynomials as entries,
        /// whose coefficients were chosen uniformly at random in
        /// `[lower_bound, upper_bound)` or a [`MathError`]
        /// if the interval was chosen too small or the `max_degree` of the polynomials
        /// is negative or too large to fit into [`i64`].
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer::MatPolyOverZ;
        ///
        #[unseeded]
        /// let matrix = MatPolyOverZ::sample_uniform(3, 3, 5, 17, 26).unwrap();
        #[seeded]
        /// let matrix = MatPolyOverZ::sample_uniform_seeded(3, 3, 5, 17, 26, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
        ///   if the given `upper_bound` isn't at least larger than `lower_bound`.
        /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
        ///   the `max_degree` is negative or it does not fit into an [`i64`].
        ///
        /// # Panics ...
        /// - if the provided number of rows and columns are not suited to create a matrix.
        ///   For further information see [`MatPolyOverZ::new`].
        pub(crate) fn sample_uniform(
            num_rows: impl TryInto<i64> + Display,
            num_cols: impl TryInto<i64> + Display,
            max_degree: impl TryInto<i64> + Display,
            lower_bound: impl Into<Z>,
            upper_bound: impl Into<Z>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            // derives an independent seed for every call of a seedable function below,
            // see the documentation of `seedable_function` in `src/macros/seeded.rs`
            let mut rng = SamplerRng::new(seed);

            let lower_bound: Z = lower_bound.into();
            let upper_bound: Z = upper_bound.into();
            let max_degree = evaluate_index(max_degree)?;
            let mut matrix = MatPolyOverZ::new(num_rows, num_cols);

            for row in 0..matrix.get_num_rows() {
                for col in 0..matrix.get_num_columns() {
                    let sample = PolyOverZ::sample_uniform_optionally_seeded(
                        max_degree,
                        &lower_bound,
                        &upper_bound,
                        rng.derive_seed(),
                    )?;
                    unsafe { matrix.set_entry_unchecked(row, col, sample) };
                }
            }

            Ok(matrix)
        }
    );
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::traits::{GetCoefficient, MatrixDimensions, MatrixGetEntry};
    use crate::utils::sample::test_seed;
    use crate::{
        integer::{MatPolyOverZ, Z},
        integer_mod_q::Modulus,
    };

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        for seeded in [false, true] {
            let lower_bound = Z::from(17);
            let upper_bound = Z::from(32);
            for _ in 0..32 {
                let matrix = MatPolyOverZ::sample_uniform_optionally_seeded(
                    1,
                    1,
                    0,
                    &lower_bound,
                    &upper_bound,
                    seeded.then(test_seed),
                )
                .unwrap();
                let sample = matrix.get_entry(0, 0).unwrap();
                let coeff = sample.get_coeff(0).unwrap();

                assert!(lower_bound <= coeff);
                assert!(coeff < upper_bound);
            }
        }
    }

    /// Checks whether the boundaries of the interval are kept for large intervals.
    #[test]
    fn boundaries_kept_large() {
        for seeded in [false, true] {
            let lower_bound = Z::from(i64::MIN) - Z::from(u64::MAX);
            let upper_bound = Z::from(i64::MIN);
            for _ in 0..256 {
                let matrix = MatPolyOverZ::sample_uniform_optionally_seeded(
                    1,
                    1,
                    0,
                    &lower_bound,
                    &upper_bound,
                    seeded.then(test_seed),
                )
                .unwrap();
                let sample = matrix.get_entry(0, 0).unwrap();
                let coeff = sample.get_coeff(0).unwrap();

                assert!(lower_bound <= coeff);
                assert!(coeff < upper_bound);
            }
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        for seeded in [false, true] {
            let degrees = [1, 3, 7, 15, 32, 120];
            for degree in degrees {
                let matrix = MatPolyOverZ::sample_uniform_optionally_seeded(
                    1,
                    1,
                    degree,
                    1,
                    15,
                    seeded.then(test_seed),
                )
                .unwrap();
                let poly = matrix.get_entry(0, 0).unwrap();

                assert_eq!(degree, poly.get_degree());
            }
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too large for an [`i64`] results in an error.
    #[test]
    fn false_size() {
        for seeded in [false, true] {
            let result = std::panic::catch_unwind(|| {
                let lower_bound = Z::from(-15);
                let upper_bound = Z::from(15);

                let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                    0,
                    3,
                    1,
                    &lower_bound,
                    &upper_bound,
                    seeded.then(test_seed),
                );
            });
            assert!(result.is_err());
        }
    }

    /// Checks whether providing an invalid interval results in an error.
    #[test]
    fn invalid_interval() {
        for seeded in [false, true] {
            let lb_0 = Z::from(i64::MIN);
            let lb_1 = Z::from(i64::MIN);
            let lb_2 = Z::ZERO;
            let upper_bound = Z::from(i64::MIN);

            let mat_0 = MatPolyOverZ::sample_uniform_optionally_seeded(
                3,
                3,
                0,
                &lb_0,
                &upper_bound,
                seeded.then(test_seed),
            );
            let mat_1 = MatPolyOverZ::sample_uniform_optionally_seeded(
                4,
                1,
                0,
                &lb_1,
                &upper_bound,
                seeded.then(test_seed),
            );
            let mat_2 = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                5,
                0,
                &lb_2,
                &upper_bound,
                seeded.then(test_seed),
            );

            assert!(mat_0.is_err());
            assert!(mat_1.is_err());
            assert!(mat_2.is_err());
        }
    }

    /// Checks whether providing a length smaller than `0` results in an error.
    #[test]
    fn invalid_max_degree() {
        for seeded in [false, true] {
            let lower_bound = Z::from(0);
            let upper_bound = Z::from(15);

            let res_0 = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                -1,
                &lower_bound,
                &upper_bound,
                seeded.then(test_seed),
            );
            let res_1 = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                i64::MIN,
                &lower_bound,
                &upper_bound,
                seeded.then(test_seed),
            );

            assert!(res_0.is_err());
            assert!(res_1.is_err());
        }
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        for seeded in [false, true] {
            let modulus = Modulus::from(7);
            let z = Z::from(7);

            let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                0u8,
                0u16,
                7u8,
                seeded.then(test_seed),
            );
            let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                0u16,
                0u32,
                7u16,
                seeded.then(test_seed),
            );
            let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                0u32,
                0u64,
                7u32,
                seeded.then(test_seed),
            );
            let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                0u64,
                0i8,
                7u64,
                seeded.then(test_seed),
            );
            let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                0i8,
                0i16,
                7i8,
                seeded.then(test_seed),
            );
            let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                0i16,
                0i32,
                7i16,
                seeded.then(test_seed),
            );
            let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                0i32,
                0i64,
                7i32,
                seeded.then(test_seed),
            );
            let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                0i64,
                &Z::ZERO,
                7i64,
                seeded.then(test_seed),
            );
            let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                0,
                0u8,
                &modulus,
                seeded.then(test_seed),
            );
            let _ = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                1,
                Z::ZERO,
                0,
                &z,
                seeded.then(test_seed),
            );

            // explicitly checks the existence of the unseeded and the seeded function
            if seeded {
                let _ = MatPolyOverZ::sample_uniform_seeded(1, 1, 0u8, 0u16, 7u8, test_seed());
            } else {
                let _ = MatPolyOverZ::sample_uniform(1, 1, 0u8, 0u16, 7u8);
            }
        }
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        for seeded in [false, true] {
            let lower_bound = Z::from(-15);
            let upper_bound = Z::from(15);

            let mat_0 = MatPolyOverZ::sample_uniform_optionally_seeded(
                3,
                3,
                0,
                &lower_bound,
                &upper_bound,
                seeded.then(test_seed),
            )
            .unwrap();
            let mat_1 = MatPolyOverZ::sample_uniform_optionally_seeded(
                4,
                1,
                0,
                &lower_bound,
                &upper_bound,
                seeded.then(test_seed),
            )
            .unwrap();
            let mat_2 = MatPolyOverZ::sample_uniform_optionally_seeded(
                1,
                5,
                0,
                &lower_bound,
                &upper_bound,
                seeded.then(test_seed),
            )
            .unwrap();
            let mat_3 = MatPolyOverZ::sample_uniform_optionally_seeded(
                15,
                20,
                0,
                &lower_bound,
                &upper_bound,
                seeded.then(test_seed),
            )
            .unwrap();

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

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer::MatPolyOverZ;
        let sample_0 = MatPolyOverZ::sample_uniform_seeded(3, 3, 5, 17, 26, [42; 32]).unwrap();
        let sample_1 = MatPolyOverZ::sample_uniform_seeded(3, 3, 5, 17, 26, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }

    /// Checks whether the seeded variant outputs the known sample for a fixed seed.
    #[test]
    fn known_answer() {
        use crate::integer::MatPolyOverZ;
        let sample = MatPolyOverZ::sample_uniform_seeded(3, 3, 5, 17, 26, [42; 32]).unwrap();

        assert_eq!(
            "[[6  18 19 20 20 18 22, 6  18 25 25 21 20 19, 6  20 20 23 22 22 24],[6  23 19 22 17 23 23, 6  19 20 19 24 21 22, 6  17 22 23 24 25 25],[6  22 24 24 17 21 24, 6  20 17 25 19 17 20, 6  24 18 22 17 24 18]]",
            sample.to_string()
        );
    }
}
