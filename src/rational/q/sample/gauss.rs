// Copyright 2024 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for gaussian distributions over [`Q`].

use crate::{
    error::MathError, macros::seeded::seedable_function, rational::Q,
    utils::sample::uniform::SamplerRng,
};
use probability::{
    distribution::{Gaussian, Sample},
    source,
};
use rand::Rng;

impl Q {
    seedable_function!(
        /// Chooses a [`Q`] instance according to the continuous Gaussian distribution.
        ///
        /// Parameters:
        /// - `center`: specifies the position of the center
        /// - `sigma`: specifies the standard deviation
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns new [`Q`] sample chosen according to the specified continuous Gaussian
        /// distribution or a [`MathError`] if the specified parameters were not chosen
        /// appropriately (`sigma > 0`).
        ///
        /// # Examples
        /// ```
        /// use qfall_math::rational::Q;
        ///
        #[unseeded]
        /// let sample = Q::sample_gauss(0, 1).unwrap();
        #[seeded]
        /// let sample = Q::sample_gauss_seeded(0, 1, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`NonPositive`](MathError::NonPositive)
        ///   if `sigma <= 0`.
        pub(crate) fn sample_gauss(
            center: impl Into<Q>,
            sigma: impl Into<f64>,
            seed: Option<[u8; 32]>,
        ) -> Result<Q, MathError> {
            let center = center.into();
            let sigma = sigma.into();
            if sigma <= 0.0 {
                return Err(MathError::NonPositive(format!(
                    "The sigma has to be positive and not zero, but the provided value is {sigma}."
                )));
            }
            let mut rng = SamplerRng::new(seed);
            let mut source = source::default(rng.next_u64());

            // Instead of sampling with a center of c, we sample with center 0 and add the
            // center later. These are equivalent and this way we can sample in larger ranges
            let sampler = Gaussian::new(0.0, sigma);
            let sample = center + Q::from(sampler.sample(&mut source));

            Ok(sample)
        }
    );
}

#[cfg(test)]
mod test_sample_gauss {
    use crate::rational::Q;

    /// Test correct distribution with a confidence level of 99.7% -> 3 standard
    /// deviations.
    #[test]
    fn in_concentration_bound() {
        let range = 3;
        for (mu, sigma) in [(i64::MAX, 1), (0, 20), (i64::MIN, 100)] {
            assert!(range * sigma >= (Q::from(mu) - Q::sample_gauss(mu, sigma).unwrap()).abs())
        }
    }

    /// Ensure that an error is returned if `sigma` is not positive
    #[test]
    fn non_positive_sigma() {
        for (mu, sigma) in [(0, 0), (0, -1)] {
            assert!(Q::sample_gauss(mu, sigma).is_err())
        }
    }
}

#[cfg(test)]
mod test_sample_gauss_seeded {
    use crate::rational::Q;
    use crate::utils::sample::test_seed;

    /// Test correct distribution with a confidence level of 99.7% -> 3 standard
    /// deviations.
    #[test]
    fn in_concentration_bound() {
        let range = 3;
        for (mu, sigma) in [(i64::MAX, 1), (0, 20), (i64::MIN, 100)] {
            assert!(
                range * sigma
                    >= (Q::from(mu) - Q::sample_gauss_seeded(mu, sigma, test_seed()).unwrap())
                        .abs()
            )
        }
    }

    /// Ensure that an error is returned if `sigma` is not positive
    #[test]
    fn non_positive_sigma() {
        for (mu, sigma) in [(0, 0), (0, -1)] {
            assert!(Q::sample_gauss_seeded(mu, sigma, test_seed()).is_err())
        }
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::rational::Q;
        let sample_0 = Q::sample_gauss_seeded(0, 1, [42; 32]).unwrap();
        let sample_1 = Q::sample_gauss_seeded(0, 1, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }
}
