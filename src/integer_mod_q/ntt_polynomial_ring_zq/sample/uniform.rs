// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the uniform distribution.

use crate::{
    integer_mod_q::{ModulusPolynomialRingZq, NTTPolynomialRingZq},
    utils::sample::uniform::UniformIntegerSampler,
};

impl NTTPolynomialRingZq {
    /// Generates a [`NTTPolynomialRingZq`] instance with degree `modulus_degree - 1`
    /// and entries chosen uniform at random in `[0, modulus)`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `modulus_degree`: specifies the degree of the modulus polynomial, i.e. the maximum number
    ///   of sampled coefficients is `modulus_degree - 1`
    /// - `modulus`: specifies the modulus of the values and thus,
    ///   the interval size over which is sampled
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
    /// let sample = NTTPolynomialRingZq::sample_uniform(&modulus);
    /// ```
    pub fn sample_uniform(modulus: &ModulusPolynomialRingZq) -> Self {
        let interval_size = modulus.get_q();
        assert!(interval_size > 1);

        let mut uis = UniformIntegerSampler::init(&interval_size).unwrap();

        let vector = (0..modulus.get_degree()).map(|_| uis.sample()).collect();
        Self {
            poly: vector,
            modulus: modulus.clone(),
        }
    }
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
