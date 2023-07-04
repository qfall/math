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
    integer::Z,
    integer_mod_q::{Modulus, PolyOverZq},
    traits::SetCoefficient,
    utils::{index::evaluate_index, sample::uniform::sample_uniform_rejection},
};
use std::fmt::Display;

impl PolyOverZq {
    /// Generates a [`PolyOverZq`] instance with length `nr_coeffs` and coefficients
    /// chosen uniform at random in `[0, modulus)`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `nr_coeffs`: specifies the length of the polynomial,
    /// i.e. the number of coefficients
    /// - `modulus`: specifies the modulus of the coefficients and thus,
    /// the interval size over which is sampled
    ///
    /// Returns a fresh [`PolyOverZq`] instance of length `nr_coeffs` with coefficients
    /// chosen uniform at random in `[0, modulus)` or a [`MathError`]
    /// if the `nr_coeffs` was smaller than `1` or the provided `modulus` was chosen too small.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    ///
    /// let sample = PolyOverZq::sample_uniform(3, 17).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    /// if the given `modulus` isn't bigger than `1`, i.e. the interval size is at most `1`.
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// the `nr_coeffs` is negative or it does not fit into an [`i64`].
    ///
    /// # Panics ...
    /// - if the provided modulus is not greater than `1`.
    pub fn sample_uniform(
        nr_coeffs: impl TryInto<i64> + Display + Copy,
        modulus: impl Into<Z>,
    ) -> Result<Self, MathError> {
        let nr_coeffs = evaluate_index(nr_coeffs)?;
        let interval_size = modulus.into();
        let modulus = Modulus::from(&interval_size);
        let mut poly_zq = PolyOverZq::from(&modulus);

        for index in 0..nr_coeffs {
            let sample = sample_uniform_rejection(&interval_size)?;
            poly_zq.set_coeff(index, &sample)?;
        }
        Ok(poly_zq)
    }
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
    fn invalid_nr_coeffs() {
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
