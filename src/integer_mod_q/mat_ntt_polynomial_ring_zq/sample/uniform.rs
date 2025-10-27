// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the uniform distribution.

use crate::{
    integer::Z,
    integer_mod_q::MatNTTPolynomialRingZq,
    utils::{index::evaluate_index, sample::uniform::UniformIntegerSampler},
};
use std::fmt::Display;

impl MatNTTPolynomialRingZq {
    /// Generates a [`MatNTTPolynomialRingZq`] instance with maximum degree `modulus_degree`
    /// and entries chosen uniform at random in `[0, modulus)`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `num_rows`: defines the number of rows of the matrix
    /// - `num_columns`: defines the number of columns of the matrix
    /// - `modulus_degree`: specifies the degree of the modulus polynomial, i.e. the maximum number
    ///   of sampled coefficients is `modulus_degree - 1`
    /// - `modulus`: specifies the modulus of the values and thus,
    ///   the interval size over which is sampled
    ///
    /// Returns a fresh [`MatNTTPolynomialRingZq`] instance of length `modulus_degree` with entries
    /// chosen uniform at random in `[0, modulus)`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatNTTPolynomialRingZq;
    ///
    /// let sample = MatNTTPolynomialRingZq::sample_uniform(3, 2, 3, 17);
    /// ```
    ///
    /// # Panics ...
    /// - if `nr_rows` or `nr_columns` is `0`.
    /// - if `modulus` is smaller than `2`.
    /// - the `modulus_degree` is smaller than `2` or it does not fit into an [`i64`].
    pub fn sample_uniform(
        nr_rows: usize,
        nr_columns: usize,
        modulus_degree: impl TryInto<i64> + Display + Copy,
        modulus: impl Into<Z>,
    ) -> Self {
        assert!(nr_rows > 0);
        assert!(nr_columns > 0);
        let modulus_degree = evaluate_index(modulus_degree)
            .expect("`modulus_degree` can't be smaller negative and must fit into an i64.");
        assert!(
            modulus_degree > 1,
            "`modulus_degree` can't be smaller than 2 and must fit into an i64."
        );
        let interval_size = modulus.into();
        assert!(interval_size > Z::ONE);

        let mut uis = UniformIntegerSampler::init(&interval_size).unwrap();

        let vector = (0..modulus_degree as usize * nr_rows * nr_columns)
            .map(|_| uis.sample())
            .collect();
        Self {
            matrix: vector,
            d: modulus_degree as usize,
            nr_rows,
            nr_columns,
        }
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{integer::Z, integer_mod_q::MatNTTPolynomialRingZq};

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        for _ in 0..32 {
            let matrix = MatNTTPolynomialRingZq::sample_uniform(1, 1, 2, 17);
            let sample = matrix.matrix[0].clone();

            assert!(Z::ZERO <= sample);
            assert!(sample < 17);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large intervals.
    #[test]
    fn boundaries_kept_large() {
        for _ in 0..256 {
            let matrix = MatNTTPolynomialRingZq::sample_uniform(1, 1, 2, u64::MAX);
            let sample = matrix.matrix[0].clone();

            assert!(Z::ZERO <= sample);
            assert!(sample < u64::MAX);
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too large for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let _ = MatNTTPolynomialRingZq::sample_uniform(0, 1, 2, 3);
    }

    /// Checks whether 0 modulus polynomial is insufficient.
    #[test]
    #[should_panic]
    fn invalid_modulus() {
        let _ = MatNTTPolynomialRingZq::sample_uniform(1, 1, 1, 1);
    }
}
