// Copyright © 2024 Marcel Luca Schmidt
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
    rational::{PolyOverQ, Q},
    traits::SetCoefficient,
    utils::index::evaluate_index,
};
use std::fmt::Display;

impl PolyOverQ {
    /// Initializes a new [`PolyOverQ`] with maximum degree `max_degree`
    /// and with each coefficient sampled independently according to the
    /// Gaussian distribution, using [`Q::sample_gauss`].
    ///
    /// Parameters:
    /// - `max_degree`: specifies the included maximal degree the created [`PolyOverQ`] should have
    /// - `center`: specifies the center for each coefficient of the polynomial
    /// - `sigma`: specifies the standard deviation
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
    /// let sample = PolyOverQ::sample_gauss(2, 0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`NonPositive`](MathError::NonPositive)
    ///     if `sigma <= 0`.
    ///
    /// # Panics ...
    /// - if `max_degree` is negative, or does not fit into an [`i64`].
    pub fn sample_gauss(
        max_degree: impl TryInto<i64> + Display,
        center: impl Into<Q>,
        sigma: impl Into<f64>,
    ) -> Result<Self, MathError> {
        let max_degree = evaluate_index(max_degree).unwrap();

        let center = center.into();
        let sigma: f64 = sigma.into();
        let mut poly = PolyOverQ::default();

        for index in 0..=max_degree {
            let sample: Q = Q::sample_gauss(&center, sigma)?;
            poly.set_coeff(index, &sample)?;
        }
        Ok(poly)
    }
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
