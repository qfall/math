// Copyright 2023 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for uniform random sampling.

use crate::{
    integer::Z, integer_mod_q::Zq, macros::seeded::seedable_function,
    utils::sample::uniform::UniformIntegerSampler,
};

impl Zq {
    seedable_function!(
        /// Chooses a [`Zq`] instance uniformly at random in `[0, modulus)`.
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
        /// - `modulus`: specifies the [`Modulus`](crate::integer_mod_q::Modulus)
        ///   of the new [`Zq`] instance and thus the size of the interval over which is sampled
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns a new [`Zq`] instance with a value chosen
        /// uniformly at random in `[0, modulus)`.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer_mod_q::Zq;
        ///
        #[unseeded]
        /// let sample = Zq::sample_uniform(17);
        #[seeded]
        /// let sample = Zq::sample_uniform_seeded(17, [42; 32]);
        /// ```
        ///
        /// # Panics
        /// - if the given modulus is smaller than or equal to `1`.
        pub(crate) fn sample_uniform(modulus: impl Into<Z>, seed: Option<[u8; 32]>) -> Self {
            let modulus: Z = modulus.into();
            let mut uis = UniformIntegerSampler::init(&modulus, seed).unwrap();

            let random = uis.sample();
            Zq::from((random, modulus))
        }
    );
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{
        integer::Z,
        integer_mod_q::{Modulus, Zq},
    };

    /// Checks whether the boundaries of the interval are kept for small moduli.
    /// These should be protected by the sampling algorithm and [`Zq`]s instantiation.
    #[test]
    fn boundaries_kept_small() {
        let modulus = Z::from(17);
        for _ in 0..32 {
            let sample = Zq::sample_uniform(&modulus);
            assert!(Z::ZERO <= sample.value);
            assert!(sample.value < modulus);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large moduli.
    /// These should be protected by the sampling algorithm and [`Zq`]s instantiation.
    #[test]
    fn boundaries_kept_large() {
        let modulus = Z::from(u64::MAX);
        for _ in 0..256 {
            let sample = Zq::sample_uniform(&modulus);
            assert!(Z::ZERO <= sample.value);
            assert!(sample.value < modulus);
        }
    }

    /// Checks whether providing an invalid interval results in an error.
    #[test]
    #[should_panic]
    fn invalid_interval() {
        let modulus = Z::ZERO;

        let _ = Zq::sample_uniform(&modulus);
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from(7);
        let z = Z::from(7);

        let _ = Zq::sample_uniform(7u8);
        let _ = Zq::sample_uniform(7u16);
        let _ = Zq::sample_uniform(7u32);
        let _ = Zq::sample_uniform(7u64);
        let _ = Zq::sample_uniform(7i8);
        let _ = Zq::sample_uniform(7i16);
        let _ = Zq::sample_uniform(7i32);
        let _ = Zq::sample_uniform(7i64);
        let _ = Zq::sample_uniform(&modulus);
        let _ = Zq::sample_uniform(&z);
    }

    /// Roughly checks the uniformity of the distribution.
    /// This test could possibly fail for a truly uniform distribution
    /// with probability smaller than 1/1000.
    #[test]
    fn uniformity() {
        let modulus = Z::from(5);
        let mut counts = [0; 5];
        // count sampled instances
        for _ in 0..1000 {
            let sample_z = Zq::sample_uniform(&modulus);
            let sample_int = i64::try_from(&sample_z.value).unwrap() as usize;
            counts[sample_int] += 1;
        }

        // Check that every sampled integer was sampled roughly the same time
        // this could possibly fail for true uniform randomness with probability
        for count in counts {
            assert!(count > 150, "This test can fail with probability close to 0. 
            It fails if the sampled occurrences do not look like a typical uniform random distribution. 
            If this happens, rerun the tests several times and check whether this issue comes up again.");
        }
    }
}

#[cfg(test)]
mod test_sample_uniform_seeded {
    use crate::utils::sample::test_seed;
    use crate::{
        integer::Z,
        integer_mod_q::{Modulus, Zq},
    };

    /// Checks whether the boundaries of the interval are kept for small moduli.
    /// These should be protected by the sampling algorithm and [`Zq`]s instantiation.
    #[test]
    fn boundaries_kept_small() {
        let modulus = Z::from(17);
        for _ in 0..32 {
            let sample = Zq::sample_uniform_seeded(&modulus, test_seed());
            assert!(Z::ZERO <= sample.value);
            assert!(sample.value < modulus);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large moduli.
    /// These should be protected by the sampling algorithm and [`Zq`]s instantiation.
    #[test]
    fn boundaries_kept_large() {
        let modulus = Z::from(u64::MAX);
        for _ in 0..256 {
            let sample = Zq::sample_uniform_seeded(&modulus, test_seed());
            assert!(Z::ZERO <= sample.value);
            assert!(sample.value < modulus);
        }
    }

    /// Checks whether providing an invalid interval results in an error.
    #[test]
    #[should_panic]
    fn invalid_interval() {
        let modulus = Z::ZERO;

        let _ = Zq::sample_uniform_seeded(&modulus, test_seed());
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from(7);
        let z = Z::from(7);

        let _ = Zq::sample_uniform_seeded(7u8, test_seed());
        let _ = Zq::sample_uniform_seeded(7u16, test_seed());
        let _ = Zq::sample_uniform_seeded(7u32, test_seed());
        let _ = Zq::sample_uniform_seeded(7u64, test_seed());
        let _ = Zq::sample_uniform_seeded(7i8, test_seed());
        let _ = Zq::sample_uniform_seeded(7i16, test_seed());
        let _ = Zq::sample_uniform_seeded(7i32, test_seed());
        let _ = Zq::sample_uniform_seeded(7i64, test_seed());
        let _ = Zq::sample_uniform_seeded(&modulus, test_seed());
        let _ = Zq::sample_uniform_seeded(&z, test_seed());
    }

    /// Roughly checks the uniformity of the distribution.
    /// This test could possibly fail for a truly uniform distribution
    /// with probability smaller than 1/1000.
    #[test]
    fn uniformity() {
        let modulus = Z::from(5);
        let mut counts = [0; 5];
        // count sampled instances
        for _ in 0..1000 {
            let sample_z = Zq::sample_uniform_seeded(&modulus, test_seed());
            let sample_int = i64::try_from(&sample_z.value).unwrap() as usize;
            counts[sample_int] += 1;
        }

        // Check that every sampled integer was sampled roughly the same time
        // this could possibly fail for true uniform randomness with probability
        for count in counts {
            assert!(count > 150, "This test can fail with probability close to 0. 
            It fails if the sampled occurrences do not look like a typical uniform random distribution. 
            If this happens, rerun the tests several times and check whether this issue comes up again.");
        }
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer_mod_q::Zq;
        let sample_0 = Zq::sample_uniform_seeded(17, [42; 32]);
        let sample_1 = Zq::sample_uniform_seeded(17, [42; 32]);

        assert_eq!(sample_0, sample_1);
    }
}
