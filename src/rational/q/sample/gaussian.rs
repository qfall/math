// Copyright © 2024 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for gaussian distributions over [`Q`].

use crate::{error::MathError, rational::Q};
use probability::{
    distribution::{Gaussian, Sample},
    source,
};
use rand::RngCore;

impl Q {
    /// Chooses a [`Q`] instance according to the continuous Gaussian distribution.
    ///
    /// Parameters:
    /// - `center`: specifies the position of the center
    /// - `sigma`: specifies the standard deviation
    ///
    /// Returns new [`Q`] sample chosen according to the specified continuous Gaussian
    /// distribution or a [`MathError`] if the specified parameters were not chosen
    /// appropriately, `sigma > 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let sample = Q::sample_gauss(0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`NonPositive`](MathError::NonPositive)
    ///     if `sigma <= 0`.
    pub fn sample_gauss(center: impl Into<Q>, sigma: impl Into<f64>) -> Result<Q, MathError> {
        let center = center.into();
        let sigma = sigma.into();
        if sigma <= 0.0 {
            return Err(MathError::NonPositive(format!(
                "The sigma has to be positive and not zero, but the provided value is {sigma}."
            )));
        }
        let mut rng = rand::thread_rng();
        let mut source = source::default(rng.next_u64());

        // instead of sampling with a center of c, we with center 0 and add the
        // center later these are equivalent and this way we can sample in larger ranges
        let sampler = Gaussian::new(0.0, sigma);
        let sample = center + Q::from(sampler.sample(&mut source));

        Ok(sample)
    }
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
            assert!(
                Q::from(range * sigma) >= (Q::from(mu) - Q::sample_gauss(mu, sigma).unwrap()).abs()
            )
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
