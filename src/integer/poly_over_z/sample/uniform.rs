// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the uniform distribution.

use crate::{
    error::MathError,
    integer::{PolyOverZ, Z},
    traits::SetCoefficient,
    utils::{index::evaluate_index, sample::uniform::sample_uniform_rejection},
};
use std::fmt::Display;

impl PolyOverZ {
    /// Generates a [`PolyOverZ`] instance with length `nr_coeffs` and coefficients
    /// chosen uniform at random in `[lower_bound, upper_bound)`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `nr_coeffs`: specifies the length of the polynomial,
    /// i.e. the number of coefficients
    /// - `lower_bound`: specifies the included lower bound of the
    /// interval over which is sampled
    /// - `upper_bound`: specifies the excluded upper bound of the
    /// interval over which is sampled
    ///
    /// Returns a fresh [`PolyOverZ`] instance of length `nr_coeffs` with coefficients
    /// chosen uniform at random in `[lower_bound, upper_bound)` or a [`MathError`]
    /// if the `nr_coeffs` was smaller than `1` or the provided interval was chosen too small.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{PolyOverZ, Z};
    ///
    /// let sample = PolyOverZ::sample_uniform(3, 17, 26).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    /// if the given `upper_bound` isn't at least bigger than `lower_bound + 1`,
    /// i.e. the interval size is at most `1`.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// the `nr_coefficients` is negative or it does not fit into an [`i64`].
    pub fn sample_uniform(
        nr_coeffs: impl TryInto<i64> + Display + Copy,
        lower_bound: impl Into<Z>,
        upper_bound: impl Into<Z>,
    ) -> Result<Self, MathError> {
        let nr_coeffs = evaluate_index(nr_coeffs)?;
        let lower_bound: Z = lower_bound.into();
        let upper_bound: Z = upper_bound.into();

        let interval_size = &upper_bound - &lower_bound;
        let mut poly_z = PolyOverZ::default();

        for index in 0..nr_coeffs {
            let sample = sample_uniform_rejection(&interval_size)?;
            poly_z.set_coeff(index, &lower_bound + sample)?;
        }
        Ok(poly_z)
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{
        integer::{PolyOverZ, Z},
        integer_mod_q::Modulus,
        traits::GetCoefficient,
    };

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        let lower_bound = Z::from(17);
        let upper_bound = Z::from(32);
        let poly_z = PolyOverZ::sample_uniform(32, &lower_bound, &upper_bound).unwrap();

        for i in 0..32 {
            let sample = poly_z.get_coeff(i).unwrap();
            assert!(lower_bound <= sample);
            assert!(sample < upper_bound);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large intervals.
    #[test]
    fn boundaries_kept_large() {
        let lower_bound = Z::from(i64::MIN) - Z::from(u64::MAX);
        let upper_bound = Z::from(i64::MIN);

        let poly_z = PolyOverZ::sample_uniform(256, &lower_bound, &upper_bound).unwrap();

        for i in 0..256 {
            let sample = poly_z.get_coeff(i).unwrap();
            assert!(lower_bound <= sample);
            assert!(sample < upper_bound);
        }
    }

    /// Checks whether providing an invalid interval results in an error.
    #[test]
    fn invalid_interval() {
        let lb_0 = Z::from(i64::MIN) - Z::ONE;
        let lb_1 = Z::from(i64::MIN);
        let lb_2 = Z::ZERO;
        let upper_bound = Z::from(i64::MIN);

        let res_0 = PolyOverZ::sample_uniform(1, &lb_0, &upper_bound);
        let res_1 = PolyOverZ::sample_uniform(1, &lb_1, &upper_bound);
        let res_2 = PolyOverZ::sample_uniform(1, &lb_2, &upper_bound);

        assert!(res_0.is_err());
        assert!(res_1.is_err());
        assert!(res_2.is_err());
    }

    /// Checks whether providing a length smaller than `1` results in an error.
    #[test]
    fn invalid_nr_coeffs() {
        let lower_bound = Z::from(0);
        let upper_bound = Z::from(15);

        let res_0 = PolyOverZ::sample_uniform(-1, &lower_bound, &upper_bound);
        let res_1 = PolyOverZ::sample_uniform(i64::MIN, &lower_bound, &upper_bound);

        assert!(res_0.is_err());
        assert!(res_1.is_err());
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from(7);
        let z = Z::from(7);

        let _ = PolyOverZ::sample_uniform(1u64, 0u16, 7u8);
        let _ = PolyOverZ::sample_uniform(1i64, 0u32, 7u16);
        let _ = PolyOverZ::sample_uniform(1u8, 0u64, 7u32);
        let _ = PolyOverZ::sample_uniform(1u16, 0i8, 7u64);
        let _ = PolyOverZ::sample_uniform(1u32, 0i16, 7i8);
        let _ = PolyOverZ::sample_uniform(1i32, 0i32, 7i16);
        let _ = PolyOverZ::sample_uniform(1i16, 0i64, 7i32);
        let _ = PolyOverZ::sample_uniform(1i8, &Z::ZERO, 7i64);
        let _ = PolyOverZ::sample_uniform(1, 0u8, &modulus);
        let _ = PolyOverZ::sample_uniform(1, 0, &z);
    }
}
