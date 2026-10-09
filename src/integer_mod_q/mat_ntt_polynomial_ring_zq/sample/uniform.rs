// Copyright 2025 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the uniform distribution.

use crate::{
    integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq},
    macros::seeded::seedable_function,
    utils::sample::uniform::UniformIntegerSampler,
};

impl MatNTTPolynomialRingZq {
    seedable_function!(
        /// Generates a [`MatNTTPolynomialRingZq`] instance with maximum degree `modulus_degree`
        /// and entries chosen uniform at random in `[0, modulus)`.
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
        /// - `num_rows`: defines the number of rows of the matrix
        /// - `num_columns`: defines the number of columns of the matrix
        /// - `modulus_degree`: specifies the degree of the modulus polynomial, i.e. the maximum number
        ///   of sampled coefficients is `modulus_degree - 1`
        /// - `modulus`: specifies the modulus of the values and thus,
        ///   the interval size over which is sampled
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
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
        #[unseeded]
        /// let sample = MatNTTPolynomialRingZq::sample_uniform(3, 2, &modulus);
        #[seeded]
        /// let sample = MatNTTPolynomialRingZq::sample_uniform_seeded(3, 2, &modulus, [42; 32]);
        /// ```
        ///
        /// # Panics ...
        /// - if `nr_rows` or `nr_columns` is `0`.
        pub(crate) fn sample_uniform(
            nr_rows: usize,
            nr_columns: usize,
            modulus: &ModulusPolynomialRingZq,
            seed: Option<[u8; 32]>,
        ) -> Self {
            assert!(nr_rows > 0, "Number of rows needs to be larger than 0.");
            assert!(
                nr_columns > 0,
                "Number of columns needs to be larger than 0."
            );
            let interval_size = modulus.get_q();

            let mut uis = UniformIntegerSampler::init(&interval_size, seed).unwrap();

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
    );
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

#[cfg(test)]
mod test_sample_uniform_seeded {
    use crate::utils::sample::test_seed;
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
            let matrix = MatNTTPolynomialRingZq::sample_uniform_seeded(1, 1, &modulus, test_seed());
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

        let _ = MatNTTPolynomialRingZq::sample_uniform_seeded(0, 1, &modulus, test_seed());
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq};
        use std::str::FromStr;
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);
        let sample_0 = MatNTTPolynomialRingZq::sample_uniform_seeded(3, 2, &modulus, [42; 32]);
        let sample_1 = MatNTTPolynomialRingZq::sample_uniform_seeded(3, 2, &modulus, [42; 32]);

        assert_eq!(sample_0, sample_1);
    }
}
