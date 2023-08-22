// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling
//! according to the binomial distribution.

use crate::{
    error::MathError,
    integer::Z,
    integer_mod_q::{Modulus, PolyOverZq},
    rational::Q,
    traits::SetCoefficient,
    utils::{index::evaluate_index, sample::binomial::sample_binomial},
};
use std::fmt::Display;

impl PolyOverZq {
    /// Generates a [`PolyOverZq`] instance of maximum degree `max_degree` and
    /// coefficients chosen according to the binomial distribution
    /// parameterized by `n` and `p` with offset `offset`.
    ///
    /// Parameters:
    /// - `max_degree`: specifies the length of the polynomial,
    /// i.e. the number of coefficients
    /// - `offset`: specifies an offset applied to each sample
    /// collected from the binomial distribution
    /// - `modulus`: specifies the [`Modulus`] of the new [`PolyOverZq`] instance
    /// - `n`: specifies the number of trials
    /// - `p`: specifies the probability of success
    ///
    /// Returns a fresh [`PolyOverZq`] instance with each value sampled
    /// according to the binomial distribution or a [`MathError`]
    /// if `n < 1`, `p <= 0`, `p >= 1`, `n` does not fit into an [`i64`],
    /// or `max_degree` is negative or does not into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    ///
    /// let sample = PolyOverZq::sample_binomial(2, -1, 7, 2, 0.5).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if `n < 1`.
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    /// if `p <= 0` or `p >= 1`.
    /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
    /// if `n` does not fit into an [`i64`].
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// the `max_degree` is negative or it does not fit into an [`i64`].
    pub fn sample_binomial(
        max_degree: impl TryInto<i64> + Display,
        offset: impl Into<Z>,
        modulus: impl Into<Modulus>,
        n: impl Into<Z>,
        p: impl Into<Q>,
    ) -> Result<Self, MathError> {
        let max_degree = evaluate_index(max_degree)?;
        let offset: Z = offset.into();
        let modulus: Modulus = modulus.into();
        let n: Z = n.into();
        let p: Q = p.into();

        let mut poly_z = PolyOverZq::from(&modulus);

        for index in 0..=max_degree {
            let sample = sample_binomial(&n, &p)?;
            poly_z.set_coeff(index, &offset + sample)?;
        }

        Ok(poly_z)
    }
}

#[cfg(test)]
mod test_sample_binomial {
    use super::{PolyOverZq, Q, Z};
    use crate::traits::GetCoefficient;

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether the boundaries of the interval are kept.
    #[test]
    fn boundaries_kept() {
        for _ in 0..8 {
            let poly = PolyOverZq::sample_binomial(0, -1, 7, 2, 0.5).unwrap();
            let sample = poly.get_coeff(0).unwrap();
            assert!(Z::MINUS_ONE <= sample || sample <= Z::ONE);
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res = PolyOverZq::sample_binomial(degree, 1, 7, 2, 0.5).unwrap();

            assert_eq!(degree, res.get_degree());
        }
    }

    /// Checks whether providing a length smaller than `0` results in an error.
    #[test]
    fn invalid_max_degree() {
        let res_0 = PolyOverZq::sample_binomial(-1, -1, 7, 2, 0.5);
        let res_1 = PolyOverZq::sample_binomial(i64::MIN, -1, 7, 2, 0.5);

        assert!(res_0.is_err());
        assert!(res_1.is_err());
    }

    /// Checks whether `sample_binomial` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    #[test]
    fn availability() {
        let _ = PolyOverZq::sample_binomial(1, 0, 7u8, 1u16, 7u8);
        let _ = PolyOverZq::sample_binomial(1, 0, 7u16, 1u32, 7u16);
        let _ = PolyOverZq::sample_binomial(1, 0, 7u32, 1u64, 7u32);
        let _ = PolyOverZq::sample_binomial(1, 0, 7u64, 1i8, 7u64);
        let _ = PolyOverZq::sample_binomial(1, 0, 7i8, 1i16, 7i8);
        let _ = PolyOverZq::sample_binomial(1, 0, 7i16, 1i32, 7i16);
        let _ = PolyOverZq::sample_binomial(1, 0, 7i32, 1i64, 7i32);
        let _ = PolyOverZq::sample_binomial(1, 0, 7i64, Z::ONE, 7i64);
        let _ = PolyOverZq::sample_binomial(1, 0, 7, 1u8, 0.5f32);
        let _ = PolyOverZq::sample_binomial(1, 0, 7, 1u8, 0.5f64);
        let _ = PolyOverZq::sample_binomial(1, 0, 7, 1, Q::from((1, 2)));
    }
}
