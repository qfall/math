// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the uniform distribution.

use crate::{
    integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq},
    utils::sample::uniform::UniformIntegerSampler,
};

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
    /// use qfall_math::integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
    /// modulus.set_ntt_unchecked(64);
    ///
    /// let sample = MatNTTPolynomialRingZq::sample_uniform(3, 2, &modulus);
    /// ```
    ///
    /// # Panics ...
    /// - if `nr_rows` or `nr_columns` is `0`.
    pub fn sample_uniform(
        nr_rows: usize,
        nr_columns: usize,
        modulus: &ModulusPolynomialRingZq,
    ) -> Self {
        assert!(nr_rows > 0, "Number of rows needs to be larger than 0.");
        assert!(
            nr_columns > 0,
            "Number of columns needs to be larger than 0."
        );
        let interval_size = modulus.get_q();

        let mut uis = UniformIntegerSampler::init(&interval_size).unwrap();

        let vector = (0..modulus.get_degree() as usize * nr_rows * nr_columns)
            .map(|_| uis.sample())
            .collect();
        Self {
            matrix: vector,
            nr_rows,
            nr_columns,
            modulus: modulus.clone(),
        }
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{
        integer::Z,
        integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        for _ in 0..32 {
            let matrix = MatNTTPolynomialRingZq::sample_uniform(1, 1, &modulus);
            let sample = matrix.matrix[0].clone();

            assert!(Z::ZERO <= sample);
            assert!(sample < 257);
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too large for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        let _ = MatNTTPolynomialRingZq::sample_uniform(0, 1, &modulus);
    }
}
