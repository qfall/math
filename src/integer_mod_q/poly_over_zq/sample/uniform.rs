// Copyright 2023 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the uniform distribution.

use crate::{
    error::MathError,
    integer::Z,
    integer_mod_q::{Modulus, PolyOverZq},
    macros::seeded::seedable_function,
    traits::SetCoefficient,
    utils::{index::evaluate_index, sample::uniform::UniformIntegerSampler},
};
use std::fmt::Display;

impl PolyOverZq {
    seedable_function!(
        /// Generates a [`PolyOverZq`] instance with maximum degree `max_degree`
        /// and coefficients chosen uniform at random in `[0, modulus)`.
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
        /// - `max_degree`: specifies the length of the polynomial,
        ///   i.e. the number of coefficients
        /// - `modulus`: specifies the modulus of the coefficients and thus,
        ///   the interval size over which is sampled
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns a fresh [`PolyOverZq`] instance of length `max_degree` with coefficients
        /// chosen uniform at random in `[0, modulus)` or a [`MathError`]
        /// if the `max_degree` was smaller than `0` or the provided `modulus` was chosen too small.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer_mod_q::PolyOverZq;
        ///
        #[unseeded]
        /// let sample = PolyOverZq::sample_uniform(3, 17).unwrap();
        #[seeded]
        /// let sample = PolyOverZq::sample_uniform_seeded(3, 17, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
        ///   if the given `modulus` isn't larger than `1`, i.e. the interval size is at most `1`.
        /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
        ///   the `max_degree` is negative or it does not fit into an [`i64`].
        ///
        /// # Panics ...
        /// - if `modulus` is smaller than `2`.
        pub(crate) fn sample_uniform(
            max_degree: impl TryInto<i64> + Display + Copy,
            modulus: impl Into<Z>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let max_degree = evaluate_index(max_degree)?;
            let interval_size = modulus.into();
            let modulus = Modulus::from(&interval_size);
            let mut poly_zq = PolyOverZq::from(&modulus);

            let mut uis = UniformIntegerSampler::init(&interval_size, seed)?;

            for index in 0..=max_degree {
                let sample = uis.sample();
                unsafe { poly_zq.set_coeff_unchecked(index, sample) };
            }
            Ok(poly_zq)
        }
    );
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{
        integer::Z,
        integer_mod_q::{Modulus, PolyOverZq},
        traits::GetCoefficient,
    };

    /// Checks whether the boundaries of the interval are kept for small moduli.
    #[test]
    fn boundaries_kept_small() {
        let modulus = Z::from(17);

        let poly_zq = PolyOverZq::sample_uniform(32, &modulus).unwrap();

        for i in 0..32 {
            let sample: Z = poly_zq.get_coeff(i).unwrap();
            assert!(Z::ZERO <= sample);
            assert!(sample < modulus);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large moduli.
    #[test]
    fn boundaries_kept_large() {
        let modulus = Z::from(i64::MAX);

        let poly_zq = PolyOverZq::sample_uniform(256, &modulus).unwrap();

        for i in 0..256 {
            let sample: Z = poly_zq.get_coeff(i).unwrap();
            assert!(Z::ZERO <= sample);
            assert!(sample < modulus);
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res = PolyOverZq::sample_uniform(degree, u64::MAX).unwrap();

            assert_eq!(
                degree,
                res.get_degree(),
                "Could fail with probability 1/{}.",
                u64::MAX
            );
        }
    }

    /// Checks whether providing an invalid interval/ modulus results in an error.
    #[test]
    #[should_panic]
    fn invalid_modulus_negative() {
        let _ = PolyOverZq::sample_uniform(1, i64::MIN);
    }

    /// Checks whether providing an invalid interval/ modulus results in an error.
    #[test]
    #[should_panic]
    fn invalid_modulus_one() {
        let _ = PolyOverZq::sample_uniform(1, 1);
    }

    /// Checks whether providing a length smaller than `1` results in an error.
    #[test]
    fn invalid_max_degree() {
        let modulus = Z::from(15);

        let res_0 = PolyOverZq::sample_uniform(-1, &modulus);
        let res_1 = PolyOverZq::sample_uniform(i64::MIN, &modulus);

        assert!(res_0.is_err());
        assert!(res_1.is_err());
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from(10);
        let z = Z::from(10);

        let _ = PolyOverZq::sample_uniform(1u64, 10u16).unwrap();
        let _ = PolyOverZq::sample_uniform(1i64, 10u32).unwrap();
        let _ = PolyOverZq::sample_uniform(1u8, 10u64).unwrap();
        let _ = PolyOverZq::sample_uniform(1u16, 10i8).unwrap();
        let _ = PolyOverZq::sample_uniform(1u32, 10i16).unwrap();
        let _ = PolyOverZq::sample_uniform(1i32, 10i32).unwrap();
        let _ = PolyOverZq::sample_uniform(1i16, 10i64).unwrap();
        let _ = PolyOverZq::sample_uniform(1i8, &z).unwrap();
        let _ = PolyOverZq::sample_uniform(1, z).unwrap();
        let _ = PolyOverZq::sample_uniform(1, &modulus).unwrap();
        let _ = PolyOverZq::sample_uniform(1, modulus).unwrap();
    }
}

#[cfg(test)]
mod test_sample_uniform_seeded {
    use crate::utils::sample::test_seed;
    use crate::{
        integer::Z,
        integer_mod_q::{Modulus, PolyOverZq},
        traits::GetCoefficient,
    };

    /// Checks whether the boundaries of the interval are kept for small moduli.
    #[test]
    fn boundaries_kept_small() {
        let modulus = Z::from(17);

        let poly_zq = PolyOverZq::sample_uniform_seeded(32, &modulus, test_seed()).unwrap();

        for i in 0..32 {
            let sample: Z = poly_zq.get_coeff(i).unwrap();
            assert!(Z::ZERO <= sample);
            assert!(sample < modulus);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large moduli.
    #[test]
    fn boundaries_kept_large() {
        let modulus = Z::from(i64::MAX);

        let poly_zq = PolyOverZq::sample_uniform_seeded(256, &modulus, test_seed()).unwrap();

        for i in 0..256 {
            let sample: Z = poly_zq.get_coeff(i).unwrap();
            assert!(Z::ZERO <= sample);
            assert!(sample < modulus);
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res = PolyOverZq::sample_uniform_seeded(degree, u64::MAX, test_seed()).unwrap();

            assert_eq!(
                degree,
                res.get_degree(),
                "Could fail with probability 1/{}.",
                u64::MAX
            );
        }
    }

    /// Checks whether providing an invalid interval/ modulus results in an error.
    #[test]
    #[should_panic]
    fn invalid_modulus_negative() {
        let _ = PolyOverZq::sample_uniform_seeded(1, i64::MIN, test_seed());
    }

    /// Checks whether providing an invalid interval/ modulus results in an error.
    #[test]
    #[should_panic]
    fn invalid_modulus_one() {
        let _ = PolyOverZq::sample_uniform_seeded(1, 1, test_seed());
    }

    /// Checks whether providing a length smaller than `1` results in an error.
    #[test]
    fn invalid_max_degree() {
        let modulus = Z::from(15);

        let res_0 = PolyOverZq::sample_uniform_seeded(-1, &modulus, test_seed());
        let res_1 = PolyOverZq::sample_uniform_seeded(i64::MIN, &modulus, test_seed());

        assert!(res_0.is_err());
        assert!(res_1.is_err());
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from(10);
        let z = Z::from(10);

        let _ = PolyOverZq::sample_uniform_seeded(1u64, 10u16, test_seed()).unwrap();
        let _ = PolyOverZq::sample_uniform_seeded(1i64, 10u32, test_seed()).unwrap();
        let _ = PolyOverZq::sample_uniform_seeded(1u8, 10u64, test_seed()).unwrap();
        let _ = PolyOverZq::sample_uniform_seeded(1u16, 10i8, test_seed()).unwrap();
        let _ = PolyOverZq::sample_uniform_seeded(1u32, 10i16, test_seed()).unwrap();
        let _ = PolyOverZq::sample_uniform_seeded(1i32, 10i32, test_seed()).unwrap();
        let _ = PolyOverZq::sample_uniform_seeded(1i16, 10i64, test_seed()).unwrap();
        let _ = PolyOverZq::sample_uniform_seeded(1i8, &z, test_seed()).unwrap();
        let _ = PolyOverZq::sample_uniform_seeded(1, z, test_seed()).unwrap();
        let _ = PolyOverZq::sample_uniform_seeded(1, &modulus, test_seed()).unwrap();
        let _ = PolyOverZq::sample_uniform_seeded(1, modulus, test_seed()).unwrap();
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer_mod_q::PolyOverZq;
        let sample_0 = PolyOverZq::sample_uniform_seeded(3, 17, [42; 32]).unwrap();
        let sample_1 = PolyOverZq::sample_uniform_seeded(3, 17, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }
}
