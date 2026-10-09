// Copyright 2025 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the uniform distribution.

use crate::{
    integer_mod_q::{ModulusPolynomialRingZq, NTTPolynomialRingZq},
    macros::seeded::seedable_function,
    utils::sample::uniform::UniformIntegerSampler,
};

impl NTTPolynomialRingZq {
    seedable_function!(
        /// Generates a [`NTTPolynomialRingZq`] instance with degree `modulus_degree - 1`
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
        /// Returns a fresh [`NTTPolynomialRingZq`] instance of length `modulus_degree` with entries
        /// chosen uniform at random in `[0, modulus)`.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer_mod_q::{NTTPolynomialRingZq, ModulusPolynomialRingZq};
        /// use std::str::FromStr;
        /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        /// modulus.set_ntt_unchecked(64);
        ///
        #[unseeded]
        /// let sample = NTTPolynomialRingZq::sample_uniform(&modulus);
        #[seeded]
        /// let sample = NTTPolynomialRingZq::sample_uniform_seeded(&modulus, [42; 32]);
        /// ```
        pub(crate) fn sample_uniform(
            modulus: &ModulusPolynomialRingZq,
            seed: Option<[u8; 32]>,
        ) -> Self {
            let interval_size = modulus.get_q();
            assert!(interval_size > 1);

            let mut uis = UniformIntegerSampler::init(&interval_size, seed).unwrap();

            let vector = (0..modulus.get_degree()).map(|_| uis.sample()).collect();
            Self {
                poly: vector,
                modulus: modulus.clone(),
            }
        }
    );
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{
        integer::Z,
        integer_mod_q::{ModulusPolynomialRingZq, NTTPolynomialRingZq},
    };
    use std::str::FromStr;

    /// Checks whether the boundaries of the interval are kept.
    #[test]
    fn boundaries_kept() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        let poly = NTTPolynomialRingZq::sample_uniform(&modulus);

        for i in 0..4 {
            let sample = &poly.poly[i];
            assert!(&Z::ZERO <= sample);
            assert!(sample < &Z::from(257));
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        let res = NTTPolynomialRingZq::sample_uniform(&modulus);

        assert_eq!(4, res.poly.len(),);
    }
}

#[cfg(test)]
mod test_sample_uniform_seeded {
    use crate::utils::sample::test_seed;
    use crate::{
        integer::Z,
        integer_mod_q::{ModulusPolynomialRingZq, NTTPolynomialRingZq},
    };
    use std::str::FromStr;

    /// Checks whether the boundaries of the interval are kept.
    #[test]
    fn boundaries_kept() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        let poly = NTTPolynomialRingZq::sample_uniform_seeded(&modulus, test_seed());

        for i in 0..4 {
            let sample = &poly.poly[i];
            assert!(&Z::ZERO <= sample);
            assert!(sample < &Z::from(257));
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        let res = NTTPolynomialRingZq::sample_uniform_seeded(&modulus, test_seed());

        assert_eq!(4, res.poly.len(),);
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer_mod_q::{ModulusPolynomialRingZq, NTTPolynomialRingZq};
        use std::str::FromStr;
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);
        let sample_0 = NTTPolynomialRingZq::sample_uniform_seeded(&modulus, [42; 32]);
        let sample_1 = NTTPolynomialRingZq::sample_uniform_seeded(&modulus, [42; 32]);

        assert_eq!(sample_0, sample_1);
    }
}
