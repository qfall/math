// Copyright 2023 Jan Niklas Siemer
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
    integer::{MatPolyOverZ, PolyOverZ, Z},
    macros::seeded::seedable_function,
    rational::Q,
    traits::{MatrixDimensions, MatrixSetEntry, SetCoefficient},
    utils::{index::evaluate_index, sample::binomial::BinomialSampler},
};
use std::fmt::Display;

impl MatPolyOverZ {
    seedable_function!(
        /// Outputs a [`MatPolyOverZ`] instance with entries chosen according to the binomial
        /// distribution parameterized by `n` and `p`.
        ///
        /// Parameters:
        /// - `num_rows`: specifies the number of rows the new matrix should have
        /// - `num_cols`: specifies the number of columns the new matrix should have
        /// - `max_degree`: specifies the maximum length of all polynomials in the matrix,
        ///   i.e. the maximum number of coefficients any polynomial in the matrix can have
        /// - `n`: specifies the number of trials
        /// - `p`: specifies the probability of success
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns a new [`MatPolyOverZ`] instance with entries chosen
        /// according to the binomial distribution or a [`MathError`]
        /// if `n < 0`, `p ∉ (0,1)`, `n` does not fit into an [`i64`],
        /// or the dimensions of the matrix were chosen too small.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer::MatPolyOverZ;
        ///
        #[unseeded]
        /// let sample = MatPolyOverZ::sample_binomial(2, 2, 5, 2, 0.5).unwrap();
        #[seeded]
        /// let sample = MatPolyOverZ::sample_binomial_seeded(2, 2, 5, 2, 0.5, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `n < 0` or `p ∉ (0,1)`.
        /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
        ///   if `n` does not fit into an [`i64`].
        ///
        /// # Panics ...
        /// - if the provided number of rows and columns are not suited to create a matrix.
        ///   For further information see [`MatPolyOverZ::new`].
        pub(crate) fn sample_binomial(
            num_rows: impl TryInto<i64> + Display,
            num_cols: impl TryInto<i64> + Display,
            max_degree: impl TryInto<i64> + Display,
            n: impl Into<Z>,
            p: impl Into<Q>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            Self::sample_binomial_with_offset_optionally_seeded(
                num_rows, num_cols, max_degree, 0, n, p, seed,
            )
        }
    );

    seedable_function!(
        /// Outputs a [`MatPolyOverZ`] instance with entries chosen according to the binomial
        /// distribution parameterized by `n` and `p` with given `offset`.
        ///
        /// Parameters:
        /// - `num_rows`: specifies the number of rows the new matrix should have
        /// - `num_cols`: specifies the number of columns the new matrix should have
        /// - `max_degree`: specifies the maximum length of all polynomials in the matrix,
        ///   i.e. the maximum number of coefficients any polynomial in the matrix can have
        /// - `offset`: specifies an offset applied to each sample
        ///   collected from the binomial distribution
        /// - `n`: specifies the number of trials
        /// - `p`: specifies the probability of success
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns a new [`MatPolyOverZ`] instance with entries chosen
        /// according to the binomial distribution or a [`MathError`]
        /// if `n < 0`, `p ∉ (0,1)`, `n` does not fit into an [`i64`],
        /// or the dimensions of the matrix were chosen too small.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer::MatPolyOverZ;
        ///
        #[unseeded]
        /// let sample = MatPolyOverZ::sample_binomial_with_offset(2, 2, 5, -1, 2, 0.5).unwrap();
        #[seeded]
        /// let sample = MatPolyOverZ::sample_binomial_with_offset_seeded(2, 2, 5, -1, 2, 0.5, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `n < 0` or `p ∉ (0,1)`.
        /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
        ///   if `n` does not fit into an [`i64`].
        /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
        ///   the `max_degree` is negative or it does not fit into an [`i64`].
        ///
        /// # Panics ...
        /// - if the provided number of rows and columns are not suited to create a matrix.
        ///   For further information see [`MatPolyOverZ::new`].
        pub(crate) fn sample_binomial_with_offset(
            num_rows: impl TryInto<i64> + Display,
            num_cols: impl TryInto<i64> + Display,
            max_degree: impl TryInto<i64> + Display,
            offset: impl Into<Z>,
            n: impl Into<Z>,
            p: impl Into<Q>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let max_degree = evaluate_index(max_degree)?;
            let offset: Z = offset.into();
            let mut bin_sampler = BinomialSampler::init(n, p, seed)?;
            let mut matrix = MatPolyOverZ::new(num_rows, num_cols);

            for row in 0..matrix.get_num_rows() {
                for col in 0..matrix.get_num_columns() {
                    let mut poly_z = PolyOverZ::default();

                    for index in 0..=max_degree {
                        let mut sample = bin_sampler.sample();
                        sample += &offset;
                        unsafe { poly_z.set_coeff_unchecked(index, sample) };
                    }

                    unsafe { matrix.set_entry_unchecked(row, col, poly_z) };
                }
            }

            Ok(matrix)
        }
    );
}

#[cfg(test)]
mod test_sample_binomial {
    use super::{MatPolyOverZ, Q, Z};
    use crate::traits::{GetCoefficient, MatrixDimensions, MatrixGetEntry};

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether the boundaries of the interval are kept.
    #[test]
    fn boundaries_kept() {
        for _ in 0..8 {
            let matrix = MatPolyOverZ::sample_binomial(1, 1, 0, 2, 0.5).unwrap();
            let entry = matrix.get_entry(0, 0).unwrap();
            let poly = entry.get_coeff(0).unwrap();

            assert!(Z::ZERO <= poly);
            assert!(poly <= 2);
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let matrix = MatPolyOverZ::sample_binomial(1, 1, degree, 256, 0.99999).unwrap();
            let poly = matrix.get_entry(0, 0).unwrap();

            assert_eq!(
                degree,
                poly.get_degree(),
                "This test can fail with probability close to 0."
            );
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let _ = MatPolyOverZ::sample_binomial(0, 3, 0, 1, 0.5);
    }

    /// Checks whether providing a length smaller than `0` results in an error.
    #[test]
    fn invalid_max_degree() {
        let res_0 = MatPolyOverZ::sample_binomial(1, 1, -1, 2, 0.5);
        let res_1 = MatPolyOverZ::sample_binomial(1, 1, i64::MIN, 2, 0.5);

        assert!(res_0.is_err());
        assert!(res_1.is_err());
    }

    /// Checks whether `sample_binomial` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    #[test]
    fn availability() {
        let _ = MatPolyOverZ::sample_binomial(1, 1, 0u8, 1u16, 7u8);
        let _ = MatPolyOverZ::sample_binomial(1, 1, 0u16, 1u32, 7u16);
        let _ = MatPolyOverZ::sample_binomial(1, 1, 0u32, 1u64, 7u32);
        let _ = MatPolyOverZ::sample_binomial(1, 1, 0u64, 1i8, 7u64);
        let _ = MatPolyOverZ::sample_binomial(1, 1, 0i8, 1i16, 7i8);
        let _ = MatPolyOverZ::sample_binomial(1, 1, 0i16, 1i32, 7i16);
        let _ = MatPolyOverZ::sample_binomial(1, 1, 0i32, 1i64, 7i32);
        let _ = MatPolyOverZ::sample_binomial(1, 1, 0i64, Z::ONE, 7i64);
        let _ = MatPolyOverZ::sample_binomial(1, 1, 0, 1u8, 0.5f32);
        let _ = MatPolyOverZ::sample_binomial(1, 1, Z::ZERO, 1u8, 0.5f64);
        let _ = MatPolyOverZ::sample_binomial(1, 1, 0, 1, Q::from((1, 2)));
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let mat_0 = MatPolyOverZ::sample_binomial(3, 3, 0, 1, 0.5).unwrap();
        let mat_1 = MatPolyOverZ::sample_binomial(4, 1, 0, 1, 0.5).unwrap();
        let mat_2 = MatPolyOverZ::sample_binomial(1, 5, 0, 1, 0.5).unwrap();
        let mat_3 = MatPolyOverZ::sample_binomial(15, 20, 0, 1, 0.5).unwrap();

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
mod test_sample_binomial_seeded {
    use super::{MatPolyOverZ, Q, Z};
    use crate::traits::{GetCoefficient, MatrixDimensions, MatrixGetEntry};
    use crate::utils::sample::test_seed;

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether the boundaries of the interval are kept.
    #[test]
    fn boundaries_kept() {
        for _ in 0..8 {
            let matrix =
                MatPolyOverZ::sample_binomial_seeded(1, 1, 0, 2, 0.5, test_seed()).unwrap();
            let entry = matrix.get_entry(0, 0).unwrap();
            let poly = entry.get_coeff(0).unwrap();

            assert!(Z::ZERO <= poly);
            assert!(poly <= 2);
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let matrix =
                MatPolyOverZ::sample_binomial_seeded(1, 1, degree, 256, 0.99999, test_seed())
                    .unwrap();
            let poly = matrix.get_entry(0, 0).unwrap();

            assert_eq!(
                degree,
                poly.get_degree(),
                "This test can fail with probability close to 0."
            );
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let _ = MatPolyOverZ::sample_binomial_seeded(0, 3, 0, 1, 0.5, test_seed());
    }

    /// Checks whether providing a length smaller than `0` results in an error.
    #[test]
    fn invalid_max_degree() {
        let res_0 = MatPolyOverZ::sample_binomial_seeded(1, 1, -1, 2, 0.5, test_seed());
        let res_1 = MatPolyOverZ::sample_binomial_seeded(1, 1, i64::MIN, 2, 0.5, test_seed());

        assert!(res_0.is_err());
        assert!(res_1.is_err());
    }

    /// Checks whether `sample_binomial` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    #[test]
    fn availability() {
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, 0u8, 1u16, 7u8, test_seed());
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, 0u16, 1u32, 7u16, test_seed());
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, 0u32, 1u64, 7u32, test_seed());
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, 0u64, 1i8, 7u64, test_seed());
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, 0i8, 1i16, 7i8, test_seed());
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, 0i16, 1i32, 7i16, test_seed());
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, 0i32, 1i64, 7i32, test_seed());
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, 0i64, Z::ONE, 7i64, test_seed());
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, 0, 1u8, 0.5f32, test_seed());
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, Z::ZERO, 1u8, 0.5f64, test_seed());
        let _ = MatPolyOverZ::sample_binomial_seeded(1, 1, 0, 1, Q::from((1, 2)), test_seed());
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let mat_0 = MatPolyOverZ::sample_binomial_seeded(3, 3, 0, 1, 0.5, test_seed()).unwrap();
        let mat_1 = MatPolyOverZ::sample_binomial_seeded(4, 1, 0, 1, 0.5, test_seed()).unwrap();
        let mat_2 = MatPolyOverZ::sample_binomial_seeded(1, 5, 0, 1, 0.5, test_seed()).unwrap();
        let mat_3 = MatPolyOverZ::sample_binomial_seeded(15, 20, 0, 1, 0.5, test_seed()).unwrap();

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
        use crate::integer::MatPolyOverZ;
        let sample_0 = MatPolyOverZ::sample_binomial_seeded(2, 2, 5, 2, 0.5, [42; 32]).unwrap();
        let sample_1 = MatPolyOverZ::sample_binomial_seeded(2, 2, 5, 2, 0.5, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }
}

#[cfg(test)]
mod test_sample_binomial_with_offset {
    use super::{MatPolyOverZ, Q, Z};
    use crate::traits::{GetCoefficient, MatrixDimensions, MatrixGetEntry};

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether the boundaries of the interval are kept.
    #[test]
    fn boundaries_kept() {
        for _ in 0..8 {
            let matrix = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0, -1, 2, 0.5).unwrap();
            let entry = matrix.get_entry(0, 0).unwrap();
            let poly = entry.get_coeff(0).unwrap();

            assert!(Z::MINUS_ONE <= poly);
            assert!(poly <= Z::ONE);
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let matrix =
                MatPolyOverZ::sample_binomial_with_offset(1, 1, degree, -1, 256, 0.99999).unwrap();
            let poly = matrix.get_entry(0, 0).unwrap();

            assert_eq!(
                degree,
                poly.get_degree(),
                "This test can fail with probability close to 0."
            );
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let _ = MatPolyOverZ::sample_binomial_with_offset(0, 3, 0, 0, 1, 0.5);
    }

    /// Checks whether providing a length smaller than `0` results in an error.
    #[test]
    fn invalid_max_degree() {
        let res_0 = MatPolyOverZ::sample_binomial_with_offset(1, 1, -1, -1, 2, 0.5);
        let res_1 = MatPolyOverZ::sample_binomial_with_offset(1, 1, i64::MIN, -1, 2, 0.5);

        assert!(res_0.is_err());
        assert!(res_1.is_err());
    }

    /// Checks whether `sample_binomial_with_offset` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    #[test]
    fn availability() {
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0u8, -1, 1u16, 7u8);
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0u16, 0, 1u32, 7u16);
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0u32, Z::ONE, 1u64, 7u32);
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0u64, Z::MINUS_ONE, 1i8, 7u64);
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0i8, -1, 1i16, 7i8);
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0i16, -1, 1i32, 7i16);
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0i32, -1, 1i64, 7i32);
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0i64, -1, Z::ONE, 7i64);
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0, -1, 1u8, 0.5f32);
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, Z::ZERO, -1, 1u8, 0.5f64);
        let _ = MatPolyOverZ::sample_binomial_with_offset(1, 1, 0, -1, 1, Q::from((1, 2)));
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let mat_0 = MatPolyOverZ::sample_binomial_with_offset(3, 3, 0, -1, 1, 0.5).unwrap();
        let mat_1 = MatPolyOverZ::sample_binomial_with_offset(4, 1, 0, -1, 1, 0.5).unwrap();
        let mat_2 = MatPolyOverZ::sample_binomial_with_offset(1, 5, 0, -1, 1, 0.5).unwrap();
        let mat_3 = MatPolyOverZ::sample_binomial_with_offset(15, 20, 0, -1, 1, 0.5).unwrap();

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
mod test_sample_binomial_with_offset_seeded {
    use super::{MatPolyOverZ, Q, Z};
    use crate::traits::{GetCoefficient, MatrixDimensions, MatrixGetEntry};
    use crate::utils::sample::test_seed;

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether the boundaries of the interval are kept.
    #[test]
    fn boundaries_kept() {
        for _ in 0..8 {
            let matrix =
                MatPolyOverZ::sample_binomial_with_offset_seeded(1, 1, 0, -1, 2, 0.5, test_seed())
                    .unwrap();
            let entry = matrix.get_entry(0, 0).unwrap();
            let poly = entry.get_coeff(0).unwrap();

            assert!(Z::MINUS_ONE <= poly);
            assert!(poly <= Z::ONE);
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let matrix = MatPolyOverZ::sample_binomial_with_offset_seeded(
                1,
                1,
                degree,
                -1,
                256,
                0.99999,
                test_seed(),
            )
            .unwrap();
            let poly = matrix.get_entry(0, 0).unwrap();

            assert_eq!(
                degree,
                poly.get_degree(),
                "This test can fail with probability close to 0."
            );
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let _ = MatPolyOverZ::sample_binomial_with_offset_seeded(0, 3, 0, 0, 1, 0.5, test_seed());
    }

    /// Checks whether providing a length smaller than `0` results in an error.
    #[test]
    fn invalid_max_degree() {
        let res_0 =
            MatPolyOverZ::sample_binomial_with_offset_seeded(1, 1, -1, -1, 2, 0.5, test_seed());
        let res_1 = MatPolyOverZ::sample_binomial_with_offset_seeded(
            1,
            1,
            i64::MIN,
            -1,
            2,
            0.5,
            test_seed(),
        );

        assert!(res_0.is_err());
        assert!(res_1.is_err());
    }

    /// Checks whether `sample_binomial_with_offset` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    #[test]
    fn availability() {
        let _ =
            MatPolyOverZ::sample_binomial_with_offset_seeded(1, 1, 0u8, -1, 1u16, 7u8, test_seed());
        let _ = MatPolyOverZ::sample_binomial_with_offset_seeded(
            1,
            1,
            0u16,
            0,
            1u32,
            7u16,
            test_seed(),
        );
        let _ = MatPolyOverZ::sample_binomial_with_offset_seeded(
            1,
            1,
            0u32,
            Z::ONE,
            1u64,
            7u32,
            test_seed(),
        );
        let _ = MatPolyOverZ::sample_binomial_with_offset_seeded(
            1,
            1,
            0u64,
            Z::MINUS_ONE,
            1i8,
            7u64,
            test_seed(),
        );
        let _ =
            MatPolyOverZ::sample_binomial_with_offset_seeded(1, 1, 0i8, -1, 1i16, 7i8, test_seed());
        let _ = MatPolyOverZ::sample_binomial_with_offset_seeded(
            1,
            1,
            0i16,
            -1,
            1i32,
            7i16,
            test_seed(),
        );
        let _ = MatPolyOverZ::sample_binomial_with_offset_seeded(
            1,
            1,
            0i32,
            -1,
            1i64,
            7i32,
            test_seed(),
        );
        let _ = MatPolyOverZ::sample_binomial_with_offset_seeded(
            1,
            1,
            0i64,
            -1,
            Z::ONE,
            7i64,
            test_seed(),
        );
        let _ =
            MatPolyOverZ::sample_binomial_with_offset_seeded(1, 1, 0, -1, 1u8, 0.5f32, test_seed());
        let _ = MatPolyOverZ::sample_binomial_with_offset_seeded(
            1,
            1,
            Z::ZERO,
            -1,
            1u8,
            0.5f64,
            test_seed(),
        );
        let _ = MatPolyOverZ::sample_binomial_with_offset_seeded(
            1,
            1,
            0,
            -1,
            1,
            Q::from((1, 2)),
            test_seed(),
        );
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let mat_0 =
            MatPolyOverZ::sample_binomial_with_offset_seeded(3, 3, 0, -1, 1, 0.5, test_seed())
                .unwrap();
        let mat_1 =
            MatPolyOverZ::sample_binomial_with_offset_seeded(4, 1, 0, -1, 1, 0.5, test_seed())
                .unwrap();
        let mat_2 =
            MatPolyOverZ::sample_binomial_with_offset_seeded(1, 5, 0, -1, 1, 0.5, test_seed())
                .unwrap();
        let mat_3 =
            MatPolyOverZ::sample_binomial_with_offset_seeded(15, 20, 0, -1, 1, 0.5, test_seed())
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

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer::MatPolyOverZ;
        let sample_0 =
            MatPolyOverZ::sample_binomial_with_offset_seeded(2, 2, 5, -1, 2, 0.5, [42; 32])
                .unwrap();
        let sample_1 =
            MatPolyOverZ::sample_binomial_with_offset_seeded(2, 2, 5, -1, 2, 0.5, [42; 32])
                .unwrap();

        assert_eq!(sample_0, sample_1);
    }
}
