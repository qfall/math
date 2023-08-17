// Copyright © 2023 Niklas Siemer
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
    integer::{PolyOverZ, Z},
    rational::Q,
    traits::SetCoefficient,
    utils::{index::evaluate_index, sample::discrete_gauss::sample_z},
};
use std::fmt::Display;

impl PolyOverZ {
    /// Initializes a new [`PolyOverZ`] with maximum degree `max_degree`
    /// and with each entry sampled independently according to the
    /// discrete Gaussian distribution, using [`Z::sample_discrete_gauss`].
    ///
    /// Parameters:
    /// - `max_degree`: specifies the included maximal degree the created [`PolyOverZ`] should have
    /// - `n`: specifies the range from which [`Z::sample_discrete_gauss`] samples
    /// - `center`: specifies the positions of the center with peak probability
    /// - `s`: specifies the Gaussian parameter, which is proportional
    /// to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a fresh [`PolyOverZ`] instance of maximum degree `max_degree`
    /// with coefficients chosen independently according the discrete Gaussian distribution or
    /// a [`MathError`] if `n <= 1` or `s <= 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    ///
    /// let sample = PolyOverZ::sample_discrete_gauss(2, 1024, 0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if `n <= 1` or `s <= 0`.
    ///
    /// # Panics ...
    /// - if `max_degree` is negative, or does not fit into an [`i64`].
    pub fn sample_discrete_gauss(
        max_degree: impl TryInto<i64> + Display,
        n: impl Into<Z>,
        center: impl Into<Q>,
        s: impl Into<Q>,
    ) -> Result<Self, MathError> {
        let max_degree = evaluate_index(max_degree).unwrap();

        let n = n.into();
        let center = center.into();
        let s = s.into();
        let mut poly = PolyOverZ::default();

        for index in 0..=max_degree {
            let sample = sample_z(&n, &center, &s)?;
            poly.set_coeff(index, &sample)?;
        }
        Ok(poly)
    }
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::{
        integer::{PolyOverZ, Z},
        rational::Q,
    };

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let n = Z::from(1024);
        let center = Q::ZERO;
        let s = Q::ONE;

        let _ = PolyOverZ::sample_discrete_gauss(1u8, 16u8, 0f32, 1u8);
        let _ = PolyOverZ::sample_discrete_gauss(1u16, 16u16, 0f64, 1u16);
        let _ = PolyOverZ::sample_discrete_gauss(1u32, 16u32, 0f32, 1u32);
        let _ = PolyOverZ::sample_discrete_gauss(1u64, 16u64, 0f64, 1u64);
        let _ = PolyOverZ::sample_discrete_gauss(1i8, 16u8, 0f32, 1i8);
        let _ = PolyOverZ::sample_discrete_gauss(1i8, 16i16, 0f32, 1i16);
        let _ = PolyOverZ::sample_discrete_gauss(1i16, 16i32, 0f32, 1i32);
        let _ = PolyOverZ::sample_discrete_gauss(1i32, 16i64, 0f64, 1i64);
        let _ = PolyOverZ::sample_discrete_gauss(1i64, n, center, s);
        let _ = PolyOverZ::sample_discrete_gauss(1u8, 16i64, 0f32, 1f64);
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res = PolyOverZ::sample_discrete_gauss(degree, 1024, i64::MAX, 1).unwrap();

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
        let _ = PolyOverZ::sample_discrete_gauss(-1, 1024, 0, 1).unwrap();
    }
}
