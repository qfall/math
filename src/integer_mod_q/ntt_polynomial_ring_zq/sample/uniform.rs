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
    integer_mod_q::NTTPolynomialRingZq,
    utils::{index::evaluate_index, sample::uniform::UniformIntegerSampler},
};
use std::fmt::Display;

impl NTTPolynomialRingZq {
    /// Generates a [`NTTPolynomialRingZq`] instance with maximum degree `nr_entries`
    /// and entries chosen uniform at random in `[0, modulus)`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `nr_entries`: specifies the largest number of sampled entries
    /// - `modulus`: specifies the modulus of the values and thus,
    ///   the interval size over which is sampled
    ///
    /// Returns a fresh [`NTTPolynomialRingZq`] instance of length `nr_entries` with entries
    /// chosen uniform at random in `[0, modulus)`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::NTTPolynomialRingZq;
    ///
    /// let sample = NTTPolynomialRingZq::sample_uniform(3, 17);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    /// - the `nr_entries` is negative or it does not fit into an [`i64`].
    pub fn sample_uniform(
        nr_entries: impl TryInto<i64> + Display + Copy,
        modulus: impl Into<Z>,
    ) -> Self {
        let max_degree = evaluate_index(nr_entries)
            .expect("`nr_entries` can't be smaller negative and must fit into an i64.");
        let interval_size = modulus.into();
        assert!(interval_size > 1);

        let mut uis = UniformIntegerSampler::init(&interval_size).unwrap();

        let vector = (0..max_degree).map(|_| uis.sample()).collect();
        Self { poly: vector }
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{
        integer::Z,
        integer_mod_q::{Modulus, NTTPolynomialRingZq},
    };

    /// Checks whether the boundaries of the interval are kept for small moduli.
    #[test]
    fn boundaries_kept_small() {
        let modulus = Z::from(17);

        let poly = NTTPolynomialRingZq::sample_uniform(32, &modulus);

        for i in 0..32 {
            let sample = &poly.poly[i];
            assert!(&Z::ZERO <= sample);
            assert!(sample < &modulus);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large moduli.
    #[test]
    fn boundaries_kept_large() {
        let modulus = Z::from(i64::MAX);

        let poly = NTTPolynomialRingZq::sample_uniform(256, &modulus);

        for i in 0..256 {
            let sample = &poly.poly[i];
            assert!(&Z::ZERO <= sample);
            assert!(sample < &modulus);
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res = NTTPolynomialRingZq::sample_uniform(degree, u64::MAX);

            assert_eq!(
                degree,
                res.poly.len(),
                "Could fail with probability 1/{}.",
                u64::MAX
            );
        }
    }

    /// Checks whether providing an invalid interval/ modulus results in an error.
    #[test]
    #[should_panic]
    fn invalid_modulus_negative() {
        let _ = NTTPolynomialRingZq::sample_uniform(1, i64::MIN);
    }

    /// Checks whether providing an invalid interval/ modulus results in an error.
    #[test]
    #[should_panic]
    fn invalid_modulus_one() {
        let _ = NTTPolynomialRingZq::sample_uniform(1, 1);
    }

    /// Checks whether providing a length smaller than `1` results in an error.
    #[test]
    #[should_panic]
    fn invalid_max_degree() {
        let _ = NTTPolynomialRingZq::sample_uniform(-1, 15);
        let _ = NTTPolynomialRingZq::sample_uniform(i64::MIN, 15);
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from(10);
        let z = Z::from(10);

        let _ = NTTPolynomialRingZq::sample_uniform(1u64, 10u16);
        let _ = NTTPolynomialRingZq::sample_uniform(1i64, 10u32);
        let _ = NTTPolynomialRingZq::sample_uniform(1u8, 10u64);
        let _ = NTTPolynomialRingZq::sample_uniform(1u16, 10i8);
        let _ = NTTPolynomialRingZq::sample_uniform(1u32, 10i16);
        let _ = NTTPolynomialRingZq::sample_uniform(1i32, 10i32);
        let _ = NTTPolynomialRingZq::sample_uniform(1i16, 10i64);
        let _ = NTTPolynomialRingZq::sample_uniform(1i8, &z);
        let _ = NTTPolynomialRingZq::sample_uniform(1, z);
        let _ = NTTPolynomialRingZq::sample_uniform(1, &modulus);
        let _ = NTTPolynomialRingZq::sample_uniform(1, modulus);
    }
}
