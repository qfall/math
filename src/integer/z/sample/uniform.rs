// Copyright 2023 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the uniform distribution.

use crate::{
    error::MathError, integer::Z, macros::seeded::seedable_function,
    utils::sample::uniform::UniformIntegerSampler,
};

impl Z {
    seedable_function!(
        /// Chooses a [`Z`] instance uniformly at random
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
        /// Returns a fresh [`Z`] instance with a
        /// uniform random value in `[lower_bound, upper_bound)` or a [`MathError`]
        /// if the provided interval was chosen too small.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer::Z;
        ///
        #[unseeded]
        /// let sample = Z::sample_uniform(17, 26).unwrap();
        #[seeded]
        /// let sample = Z::sample_uniform_seeded(17, 26, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
        ///   if the given `upper_bound` isn't at least larger than `lower_bound`.
        pub(crate) fn sample_uniform(
            lower_bound: impl Into<Z>,
            upper_bound: impl Into<Z>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let lower_bound: Z = lower_bound.into();
            let upper_bound: Z = upper_bound.into();

            let interval_size = &upper_bound - &lower_bound;
            let mut uis = UniformIntegerSampler::init(&interval_size, seed)?;

            let sample = uis.sample();
            Ok(&lower_bound + sample)
        }
    );

    seedable_function!(
        /// Chooses a prime [`Z`] instance uniformly at random
        /// in `[lower_bound, upper_bound)`. If after 2 * `n` steps, where `n` denotes the size of
        /// the interval, no suitable prime was found, the algorithm aborts.
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
        /// Returns a fresh [`Z`] instance with a
        /// uniform random value in `[lower_bound, upper_bound)`. Otherwise, a [`MathError`]
        /// if the provided interval was chosen too small, no prime could be found in the interval,
        /// or the provided `lower_bound` was negative.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer::Z;
        ///
        #[unseeded]
        /// let prime = Z::sample_prime_uniform(1, 100).unwrap();
        #[seeded]
        /// let prime = Z::sample_prime_uniform_seeded(1, 100, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
        ///   if the given `upper_bound` isn't at least larger than `lower_bound`
        ///   , or if no prime could be found in the specified interval.
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `lower_bound` is negative as primes are always positive.
        pub(crate) fn sample_prime_uniform(
            lower_bound: impl Into<Z>,
            upper_bound: impl Into<Z>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let lower_bound: Z = lower_bound.into();
            let upper_bound: Z = upper_bound.into();

            if lower_bound < Z::ZERO {
                return Err(MathError::InvalidIntegerInput(format!(
                    "Primes are always positive. Hence, sample_prime_uniform expects a positive lower_bound.
                    The provided one is {lower_bound}.")));
            }

            let interval_size = &upper_bound - &lower_bound;
            let mut uis = UniformIntegerSampler::init(&interval_size, seed)?;
            let mut sample = &lower_bound + uis.sample();

            // after 2 * size of interval many uniform random samples, a suitable prime should have been
            // found with high probability, if there is one prime in the interval
            let mut steps = 2 * &interval_size;
            while !sample.is_prime() {
                if steps == Z::ZERO {
                    return Err(MathError::InvalidInterval(format!(
                        "After sampling O({interval_size}) times uniform at random in the interval [{lower_bound}, {upper_bound}[
                            no prime was found. It is very likely, that no prime exists in this interval.
                            Please choose the interval larger.")));
                }
                sample = &lower_bound + uis.sample();
                steps -= 1;
            }

            Ok(sample)
        }
    );
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::utils::sample::test_seed;
    use crate::{integer::Z, integer_mod_q::Modulus};

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        for seeded in [false, true] {
            let lower_bound = Z::from(17);
            let upper_bound = Z::from(32);
            for _ in 0..32 {
                let sample = Z::sample_uniform_optionally_seeded(
                    &lower_bound,
                    &upper_bound,
                    seeded.then(test_seed),
                )
                .unwrap();
                assert!(lower_bound <= sample);
                assert!(sample < upper_bound);
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
                let sample = Z::sample_uniform_optionally_seeded(
                    &lower_bound,
                    &upper_bound,
                    seeded.then(test_seed),
                )
                .unwrap();
                assert!(lower_bound <= sample);
                assert!(sample < upper_bound);
            }
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

            let res_0 =
                Z::sample_uniform_optionally_seeded(&lb_0, &upper_bound, seeded.then(test_seed));
            let res_1 =
                Z::sample_uniform_optionally_seeded(&lb_1, &upper_bound, seeded.then(test_seed));
            let res_2 =
                Z::sample_uniform_optionally_seeded(&lb_2, &upper_bound, seeded.then(test_seed));

            assert!(res_0.is_err());
            assert!(res_1.is_err());
            assert!(res_2.is_err());
        }
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        for seeded in [false, true] {
            let modulus = Modulus::from(7);
            let z = Z::from(7);

            let _ = Z::sample_uniform_optionally_seeded(0u16, 7u8, seeded.then(test_seed));
            let _ = Z::sample_uniform_optionally_seeded(0u32, 7u16, seeded.then(test_seed));
            let _ = Z::sample_uniform_optionally_seeded(0u64, 7u32, seeded.then(test_seed));
            let _ = Z::sample_uniform_optionally_seeded(0i8, 7u64, seeded.then(test_seed));
            let _ = Z::sample_uniform_optionally_seeded(0i16, 7i8, seeded.then(test_seed));
            let _ = Z::sample_uniform_optionally_seeded(0i32, 7i16, seeded.then(test_seed));
            let _ = Z::sample_uniform_optionally_seeded(0i64, 7i32, seeded.then(test_seed));
            let _ = Z::sample_uniform_optionally_seeded(&Z::ZERO, 7i64, seeded.then(test_seed));
            let _ = Z::sample_uniform_optionally_seeded(0u8, &modulus, seeded.then(test_seed));
            let _ = Z::sample_uniform_optionally_seeded(0, &z, seeded.then(test_seed));

            // explicitly checks the existence of the unseeded and the seeded function
            if seeded {
                let _ = Z::sample_uniform_seeded(0u16, 7u8, test_seed());
            } else {
                let _ = Z::sample_uniform(0u16, 7u8);
            }
        }
    }

    /// Roughly checks the uniformity of the distribution.
    /// This test could possibly fail for a truly uniform distribution
    /// with probability smaller than 1/1000.
    #[test]
    fn uniformity() {
        for seeded in [false, true] {
            let lower_bound = Z::ZERO;
            let upper_bound = Z::from(5);
            let mut counts = [0; 5];
            // count sampled instances
            for _ in 0..1000 {
                let sample_z = Z::sample_uniform_optionally_seeded(
                    &lower_bound,
                    &upper_bound,
                    seeded.then(test_seed),
                )
                .unwrap();
                let sample_int = i64::try_from(&sample_z).unwrap() as usize;
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

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer::Z;
        let sample_0 = Z::sample_uniform_seeded(17, 26, [42; 32]).unwrap();
        let sample_1 = Z::sample_uniform_seeded(17, 26, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }

    /// Checks whether the seeded variant outputs the known sample for a fixed seed.
    #[test]
    fn known_answer() {
        use crate::integer::Z;
        let sample = Z::sample_uniform_seeded(17, 26, [42; 32]).unwrap();

        assert_eq!("19", sample.to_string());
    }
}

#[cfg(test)]
mod test_sample_prime_uniform {
    use crate::utils::sample::test_seed;
    use crate::{integer::Z, integer_mod_q::Modulus};

    /// Checks whether `sample_prime_uniform` outputs a prime sample every time.
    #[test]
    fn is_prime() {
        for seeded in [false, true] {
            for _ in 0..8 {
                let sample =
                    Z::sample_prime_uniform_optionally_seeded(20, i64::MAX, seeded.then(test_seed))
                        .unwrap();
                assert!(sample.is_prime(), "Can fail with probability ~2^-60.");
            }
        }
    }

    /// Checks whether `sample_prime_uniform` returns an error if
    /// no prime exists in the specified interval.
    #[test]
    fn no_prime_exists() {
        for seeded in [false, true] {
            let res_0 = Z::sample_prime_uniform_optionally_seeded(14, 17, seeded.then(test_seed));
            // there is no prime between u64::MAX - 57 and u64::MAX
            let res_1 = Z::sample_prime_uniform_optionally_seeded(
                u64::MAX - 57,
                u64::MAX,
                seeded.then(test_seed),
            );

            assert!(res_0.is_err());
            assert!(res_1.is_err());
        }
    }

    /// Checks whether a negative lower bound result in an error.
    #[test]
    fn negative_lower_bound() {
        for seeded in [false, true] {
            let res_0 = Z::sample_prime_uniform_optionally_seeded(-1, 10, seeded.then(test_seed));
            let res_1 = Z::sample_prime_uniform_optionally_seeded(-200, 1, seeded.then(test_seed));

            assert!(res_0.is_err());
            assert!(res_1.is_err());
        }
    }

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        for seeded in [false, true] {
            let lower_bound = Z::from(17);
            let upper_bound = Z::from(32);
            for _ in 0..32 {
                let sample = Z::sample_prime_uniform_optionally_seeded(
                    &lower_bound,
                    &upper_bound,
                    seeded.then(test_seed),
                )
                .unwrap();
                assert!(lower_bound <= sample);
                assert!(sample < upper_bound);
            }
        }
    }

    /// Checks whether the boundaries of the interval are kept for large intervals.
    #[test]
    fn boundaries_kept_large() {
        for seeded in [false, true] {
            let lower_bound = Z::ZERO;
            let upper_bound = Z::from(i64::MAX);
            for _ in 0..256 {
                let sample = Z::sample_prime_uniform_optionally_seeded(
                    &lower_bound,
                    &upper_bound,
                    seeded.then(test_seed),
                )
                .unwrap();
                assert!(lower_bound <= sample);
                assert!(sample < upper_bound);
            }
        }
    }

    /// Checks whether providing an invalid interval results in an error.
    #[test]
    fn invalid_interval() {
        for seeded in [false, true] {
            let lb_0 = Z::from(i64::MIN) - Z::ONE;
            let lb_1 = Z::from(i64::MIN);
            let lb_2 = Z::ZERO;
            let upper_bound = Z::from(i64::MIN);

            let res_0 = Z::sample_prime_uniform_optionally_seeded(
                &lb_0,
                &upper_bound,
                seeded.then(test_seed),
            );
            let res_1 = Z::sample_prime_uniform_optionally_seeded(
                &lb_1,
                &upper_bound,
                seeded.then(test_seed),
            );
            let res_2 = Z::sample_prime_uniform_optionally_seeded(
                &lb_2,
                &upper_bound,
                seeded.then(test_seed),
            );

            assert!(res_0.is_err());
            assert!(res_1.is_err());
            assert!(res_2.is_err());
        }
    }

    /// Checks whether `sample_prime_uniform` is available for types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        for seeded in [false, true] {
            let modulus = Modulus::from(7);
            let z = Z::from(7);

            let _ = Z::sample_prime_uniform_optionally_seeded(0u16, 7u8, seeded.then(test_seed));
            let _ = Z::sample_prime_uniform_optionally_seeded(0u32, 7u16, seeded.then(test_seed));
            let _ = Z::sample_prime_uniform_optionally_seeded(0u64, 7u32, seeded.then(test_seed));
            let _ = Z::sample_prime_uniform_optionally_seeded(0i8, 7u64, seeded.then(test_seed));
            let _ = Z::sample_prime_uniform_optionally_seeded(0i16, 7i8, seeded.then(test_seed));
            let _ = Z::sample_prime_uniform_optionally_seeded(0i32, 7i16, seeded.then(test_seed));
            let _ = Z::sample_prime_uniform_optionally_seeded(0i64, 7i32, seeded.then(test_seed));
            let _ =
                Z::sample_prime_uniform_optionally_seeded(&Z::ZERO, 7i64, seeded.then(test_seed));
            let _ =
                Z::sample_prime_uniform_optionally_seeded(0u8, &modulus, seeded.then(test_seed));
            let _ = Z::sample_prime_uniform_optionally_seeded(0, &z, seeded.then(test_seed));

            // explicitly checks the existence of the unseeded and the seeded function
            if seeded {
                let _ = Z::sample_prime_uniform_seeded(0u16, 7u8, test_seed());
            } else {
                let _ = Z::sample_prime_uniform(0u16, 7u8);
            }
        }
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer::Z;
        let sample_0 = Z::sample_prime_uniform_seeded(1, 100, [42; 32]).unwrap();
        let sample_1 = Z::sample_prime_uniform_seeded(1, 100, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }

    /// Checks whether the seeded variant outputs the known sample for a fixed seed.
    #[test]
    fn known_answer() {
        use crate::integer::Z;
        let sample = Z::sample_prime_uniform_seeded(1, 100, [42; 32]).unwrap();

        assert_eq!("17", sample.to_string());
    }
}
