// Copyright 2024 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according
//! to the Gaussian distribution.

use crate::{
    error::MathError,
    macros::seeded::seedable_function,
    rational::{PolyOverQ, Q},
    traits::SetCoefficient,
    utils::index::evaluate_index,
    utils::sample::uniform::SamplerRng,
};
use probability::{
    prelude::{Gaussian, Sample},
    source,
};
use rand::Rng;
use std::fmt::Display;

impl PolyOverQ {
    seedable_function!(
        /// Initializes a new [`PolyOverQ`] with maximum degree `max_degree`
        /// and with each coefficient sampled independently according to the
        /// Gaussian distribution, using [`Q::sample_gauss`].
        ///
        /// Parameters:
        /// - `max_degree`: specifies the included maximal degree the created [`PolyOverQ`] should have
        /// - `center`: specifies the center for each coefficient of the polynomial
        /// - `sigma`: specifies the standard deviation
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns a fresh [`PolyOverQ`] instance of maximum degree `max_degree`
        /// with coefficients chosen independently according the Gaussian
        /// distribution or a [`MathError`] if the specified parameters were not chosen
        /// appropriately (`sigma > 0`).
        ///
        /// # Examples
        /// ```
        /// use qfall_math::rational::PolyOverQ;
        ///
        #[unseeded]
        /// let sample = PolyOverQ::sample_gauss(2, 0, 1).unwrap();
        #[seeded]
        /// let sample = PolyOverQ::sample_gauss_seeded(2, 0, 1, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`NonPositive`](MathError::NonPositive)
        ///   if `sigma <= 0`.
        ///
        /// # Panics ...
        /// - if `max_degree` is negative, or does not fit into an [`i64`].
        pub(crate) fn sample_gauss(
            max_degree: impl TryInto<i64> + Display,
            center: impl Into<Q>,
            sigma: impl Into<f64>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let max_degree = evaluate_index(max_degree).unwrap();

            let center = center.into();
            let sigma: f64 = sigma.into();
            let mut poly = PolyOverQ::default();

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

            for index in 0..=max_degree {
                let mut sample = Q::from(sampler.sample(&mut source));
                sample += &center;
                unsafe { poly.set_coeff_unchecked(index, &sample) };
            }
            Ok(poly)
        }
    );
}

#[cfg(test)]
mod test_sample_gauss {
    use crate::{
        integer::Z,
        rational::{PolyOverQ, Q},
    };

    /// Checks whether `sample_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let center_q = Q::ZERO;
        let center_z = Z::ZERO;

        let _ = PolyOverQ::sample_gauss(1u8, 16u8, 0f32);
        let _ = PolyOverQ::sample_gauss(1u16, 16u16, 0f64);
        let _ = PolyOverQ::sample_gauss(1u32, 16u32, 0f32);
        let _ = PolyOverQ::sample_gauss(1u64, 16u64, 0f64);
        let _ = PolyOverQ::sample_gauss(1i8, 16u8, 0f32);
        let _ = PolyOverQ::sample_gauss(1i16, 16i16, 0f32);
        let _ = PolyOverQ::sample_gauss(1i32, 16i32, 0f32);
        let _ = PolyOverQ::sample_gauss(1i64, 16i64, 0f64);
        let _ = PolyOverQ::sample_gauss(1u8, center_q, 0f32);
        let _ = PolyOverQ::sample_gauss(1u8, center_z, 0f64);
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res = PolyOverQ::sample_gauss(degree, i64::MAX, 1).unwrap();

            assert_eq!(
                res.get_degree(),
                degree,
                "Could fail with negligible probability."
            );
        }
    }

    /// Checks is as error is returned, if sigma is less than 1.
    #[test]
    fn invalid_sigma() {
        assert!(PolyOverQ::sample_gauss(1, 0, 0).is_err());
        assert!(PolyOverQ::sample_gauss(1, 0, -1).is_err());
    }

    /// Checks whether the maximum degree needs to be at least 0.
    #[test]
    #[should_panic]
    fn invalid_max_degree() {
        let _ = PolyOverQ::sample_gauss(-1, 0, 1).unwrap();
    }
}

#[cfg(test)]
mod test_sample_gauss_seeded {
    use crate::utils::sample::test_seed;
    use crate::{
        integer::Z,
        rational::{PolyOverQ, Q},
    };

    /// Checks whether `sample_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let center_q = Q::ZERO;
        let center_z = Z::ZERO;

        let _ = PolyOverQ::sample_gauss_seeded(1u8, 16u8, 0f32, test_seed());
        let _ = PolyOverQ::sample_gauss_seeded(1u16, 16u16, 0f64, test_seed());
        let _ = PolyOverQ::sample_gauss_seeded(1u32, 16u32, 0f32, test_seed());
        let _ = PolyOverQ::sample_gauss_seeded(1u64, 16u64, 0f64, test_seed());
        let _ = PolyOverQ::sample_gauss_seeded(1i8, 16u8, 0f32, test_seed());
        let _ = PolyOverQ::sample_gauss_seeded(1i16, 16i16, 0f32, test_seed());
        let _ = PolyOverQ::sample_gauss_seeded(1i32, 16i32, 0f32, test_seed());
        let _ = PolyOverQ::sample_gauss_seeded(1i64, 16i64, 0f64, test_seed());
        let _ = PolyOverQ::sample_gauss_seeded(1u8, center_q, 0f32, test_seed());
        let _ = PolyOverQ::sample_gauss_seeded(1u8, center_z, 0f64, test_seed());
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res = PolyOverQ::sample_gauss_seeded(degree, i64::MAX, 1, test_seed()).unwrap();

            assert_eq!(
                res.get_degree(),
                degree,
                "Could fail with negligible probability."
            );
        }
    }

    /// Checks is as error is returned, if sigma is less than 1.
    #[test]
    fn invalid_sigma() {
        assert!(PolyOverQ::sample_gauss_seeded(1, 0, 0, test_seed()).is_err());
        assert!(PolyOverQ::sample_gauss_seeded(1, 0, -1, test_seed()).is_err());
    }

    /// Checks whether the maximum degree needs to be at least 0.
    #[test]
    #[should_panic]
    fn invalid_max_degree() {
        let _ = PolyOverQ::sample_gauss_seeded(-1, 0, 1, test_seed()).unwrap();
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::rational::PolyOverQ;
        let sample_0 = PolyOverQ::sample_gauss_seeded(2, 0, 1, [42; 32]).unwrap();
        let sample_1 = PolyOverQ::sample_gauss_seeded(2, 0, 1, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }
}
