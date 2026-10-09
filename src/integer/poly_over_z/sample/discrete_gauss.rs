// Copyright 2023 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according
//! to the discrete Gaussian distribution.

use crate::{
    error::MathError,
    integer::PolyOverZ,
    macros::seeded::seedable_function,
    rational::Q,
    traits::SetCoefficient,
    utils::{
        index::evaluate_index,
        sample::discrete_gauss::{DiscreteGaussianIntegerSampler, LookupTableSetting, TAILCUT},
    },
};
use std::fmt::Display;

impl PolyOverZ {
    seedable_function!(
        /// Initializes a new [`PolyOverZ`] with maximum degree `max_degree`
        /// and with each entry sampled independently according to the
        /// discrete Gaussian distribution, using [`Z::sample_discrete_gauss`](crate::integer::Z::sample_discrete_gauss).
        ///
        /// Parameters:
        /// - `max_degree`: specifies the included maximal degree the created [`PolyOverZ`] should have
        /// - `center`: specifies the positions of the center with peak probability
        /// - `s`: specifies the Gaussian parameter, which is proportional
        ///   to the standard deviation `sigma * sqrt(2 * pi) = s`
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns a fresh [`PolyOverZ`] instance of maximum degree `max_degree`
        /// with coefficients chosen independently according the discrete Gaussian distribution or
        /// a [`MathError`] if `s < 0`.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer::PolyOverZ;
        ///
        #[unseeded]
        /// let sample = PolyOverZ::sample_discrete_gauss(2, 0, 1).unwrap();
        #[seeded]
        /// let sample = PolyOverZ::sample_discrete_gauss_seeded(2, 0, 1, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `s < 0`.
        ///
        /// # Panics ...
        /// - if `max_degree` is negative, or does not fit into an [`i64`].
        pub(crate) fn sample_discrete_gauss(
            max_degree: impl TryInto<i64> + Display,
            center: impl Into<Q>,
            s: impl Into<Q>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let max_degree = evaluate_index(max_degree).unwrap();

            let center = center.into();
            let s = s.into();
            let mut poly = PolyOverZ::default();

            let mut dgis = DiscreteGaussianIntegerSampler::init(
                &center,
                &s,
                unsafe { TAILCUT },
                LookupTableSetting::FillOnTheFly,
                seed,
            )?;

            for index in 0..=max_degree {
                let sample = dgis.sample_z();
                unsafe { poly.set_coeff_unchecked(index, &sample) };
            }
            Ok(poly)
        }
    );
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::{integer::PolyOverZ, rational::Q};

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let center = Q::ZERO;
        let s = Q::ONE;

        let _ = PolyOverZ::sample_discrete_gauss(1u8, 0f32, 1u8);
        let _ = PolyOverZ::sample_discrete_gauss(1u16, 0f64, 1u16);
        let _ = PolyOverZ::sample_discrete_gauss(1u32, 0f32, 1u32);
        let _ = PolyOverZ::sample_discrete_gauss(1u64, 0f64, 1u64);
        let _ = PolyOverZ::sample_discrete_gauss(1i8, 0f32, 1i8);
        let _ = PolyOverZ::sample_discrete_gauss(1i8, 0f32, 1i16);
        let _ = PolyOverZ::sample_discrete_gauss(1i16, 0f32, 1i32);
        let _ = PolyOverZ::sample_discrete_gauss(1i32, 0f64, 1i64);
        let _ = PolyOverZ::sample_discrete_gauss(1i64, center, s);
        let _ = PolyOverZ::sample_discrete_gauss(1u8, 0f32, 1f64);
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res = PolyOverZ::sample_discrete_gauss(degree, i64::MAX, 1).unwrap();

            assert_eq!(
                res.get_degree(),
                degree,
                "Could fail with negligible probability."
            );
        }
    }

    /// Checks whether the maximum degree needs to be at least 0.
    #[test]
    #[should_panic]
    fn invalid_max_degree() {
        let _ = PolyOverZ::sample_discrete_gauss(-1, 0, 1).unwrap();
    }
}

#[cfg(test)]
mod test_sample_discrete_gauss_seeded {
    use crate::utils::sample::test_seed;
    use crate::{integer::PolyOverZ, rational::Q};

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let center = Q::ZERO;
        let s = Q::ONE;

        let _ = PolyOverZ::sample_discrete_gauss_seeded(1u8, 0f32, 1u8, test_seed());
        let _ = PolyOverZ::sample_discrete_gauss_seeded(1u16, 0f64, 1u16, test_seed());
        let _ = PolyOverZ::sample_discrete_gauss_seeded(1u32, 0f32, 1u32, test_seed());
        let _ = PolyOverZ::sample_discrete_gauss_seeded(1u64, 0f64, 1u64, test_seed());
        let _ = PolyOverZ::sample_discrete_gauss_seeded(1i8, 0f32, 1i8, test_seed());
        let _ = PolyOverZ::sample_discrete_gauss_seeded(1i8, 0f32, 1i16, test_seed());
        let _ = PolyOverZ::sample_discrete_gauss_seeded(1i16, 0f32, 1i32, test_seed());
        let _ = PolyOverZ::sample_discrete_gauss_seeded(1i32, 0f64, 1i64, test_seed());
        let _ = PolyOverZ::sample_discrete_gauss_seeded(1i64, center, s, test_seed());
        let _ = PolyOverZ::sample_discrete_gauss_seeded(1u8, 0f32, 1f64, test_seed());
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res =
                PolyOverZ::sample_discrete_gauss_seeded(degree, i64::MAX, 1, test_seed()).unwrap();

            assert_eq!(
                res.get_degree(),
                degree,
                "Could fail with negligible probability."
            );
        }
    }

    /// Checks whether the maximum degree needs to be at least 0.
    #[test]
    #[should_panic]
    fn invalid_max_degree() {
        let _ = PolyOverZ::sample_discrete_gauss_seeded(-1, 0, 1, test_seed()).unwrap();
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer::PolyOverZ;
        let sample_0 = PolyOverZ::sample_discrete_gauss_seeded(2, 0, 1, [42; 32]).unwrap();
        let sample_1 = PolyOverZ::sample_discrete_gauss_seeded(2, 0, 1, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }
}
