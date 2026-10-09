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
    integer::Z,
    integer_mod_q::{Modulus, Zq},
    macros::seeded::seedable_function,
    rational::Q,
    utils::sample::binomial::BinomialSampler,
};

impl Zq {
    seedable_function!(
        /// Chooses a [`Zq`] instance according to the binomial distribution
        /// parameterized by `n` and `p`.
        ///
        /// Parameters:
        /// - `modulus`: specifies the [`Modulus`] of the new [`Zq`] instance
        /// - `n`: specifies the number of trials
        /// - `p`: specifies the probability of success
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns a fresh [`Zq`] instance with a value sampled
        /// according to the binomial distribution or a [`MathError`]
        /// if `n < 0`, `p ∉ (0,1)`, or `n` does not fit into an [`i64`].
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer_mod_q::Zq;
        ///
        #[unseeded]
        /// let sample = Zq::sample_binomial(7, 2, 0.5).unwrap();
        #[seeded]
        /// let sample = Zq::sample_binomial_seeded(7, 2, 0.5, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `n < 0`.
        /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
        ///   if `p ∉ (0,1)`.
        /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
        ///   if `n` does not fit into an [`i64`].
        ///
        /// # Panics ...
        /// - if `modulus` is smaller than `2`.
        pub(crate) fn sample_binomial(
            modulus: impl Into<Modulus>,
            n: impl Into<Z>,
            p: impl Into<Q>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let modulus: Modulus = modulus.into();
            let mut bin_sampler = BinomialSampler::init(n, p, seed)?;

            let sample = bin_sampler.sample();
            Ok(Zq::from((sample, modulus)))
        }
    );
}

#[cfg(test)]
mod test_sample_binomial {
    use super::{Q, Z, Zq};

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether `sample_binomial` is available for all types
    /// implementing [`Into<Zq>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    /// and [`Into<Modulus>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let _ = Zq::sample_binomial(7u8, 1u16, 7u8);
        let _ = Zq::sample_binomial(7u16, 1u32, 7u16);
        let _ = Zq::sample_binomial(7u32, 1u64, 7u32);
        let _ = Zq::sample_binomial(7u64, 1i8, 7u64);
        let _ = Zq::sample_binomial(7i8, 1i16, 7i8);
        let _ = Zq::sample_binomial(7i16, 1i32, 7i16);
        let _ = Zq::sample_binomial(7i32, 1i64, 7i32);
        let _ = Zq::sample_binomial(7i64, Z::ONE, 7i64);
        let _ = Zq::sample_binomial(7, 1u8, 0.5f32);
        let _ = Zq::sample_binomial(7, 1u8, 0.5f64);
        let _ = Zq::sample_binomial(7, 1, Q::from((1, 2)));
    }
}

#[cfg(test)]
mod test_sample_binomial_seeded {
    use super::{Q, Z, Zq};
    use crate::utils::sample::test_seed;

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether `sample_binomial` is available for all types
    /// implementing [`Into<Zq>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    /// and [`Into<Modulus>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let _ = Zq::sample_binomial_seeded(7u8, 1u16, 7u8, test_seed());
        let _ = Zq::sample_binomial_seeded(7u16, 1u32, 7u16, test_seed());
        let _ = Zq::sample_binomial_seeded(7u32, 1u64, 7u32, test_seed());
        let _ = Zq::sample_binomial_seeded(7u64, 1i8, 7u64, test_seed());
        let _ = Zq::sample_binomial_seeded(7i8, 1i16, 7i8, test_seed());
        let _ = Zq::sample_binomial_seeded(7i16, 1i32, 7i16, test_seed());
        let _ = Zq::sample_binomial_seeded(7i32, 1i64, 7i32, test_seed());
        let _ = Zq::sample_binomial_seeded(7i64, Z::ONE, 7i64, test_seed());
        let _ = Zq::sample_binomial_seeded(7, 1u8, 0.5f32, test_seed());
        let _ = Zq::sample_binomial_seeded(7, 1u8, 0.5f64, test_seed());
        let _ = Zq::sample_binomial_seeded(7, 1, Q::from((1, 2)), test_seed());
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer_mod_q::Zq;
        let sample_0 = Zq::sample_binomial_seeded(7, 2, 0.5, [42; 32]).unwrap();
        let sample_1 = Zq::sample_binomial_seeded(7, 2, 0.5, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }
}
