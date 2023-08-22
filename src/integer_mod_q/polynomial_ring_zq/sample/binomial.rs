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
    integer::{PolyOverZ, Z},
    integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
    rational::Q,
};

impl PolynomialRingZq {
    /// Generates a [`PolynomialRingZq`] instance of maximum degree `modulus.get_degree() - 1` and
    /// coefficients chosen according to the binomial distribution
    /// parameterized by `n` and `p` with offset `offset`.
    ///
    /// Parameters:
    /// - `modulus`: specifies the [`ModulusPolynomialRingZq`] over which the
    /// ring of polynomials modulo `modulus.get_q()` is defined
    /// - `offset`: specifies an offset applied to each sample
    /// collected from the binomial distribution
    /// - `n`: specifies the number of trials
    /// - `p`: specifies the probability of success
    ///
    /// Returns a fresh [`PolynomialRingZq`] instance of length `modulus.get_degree() - 1`
    /// with coefficients chosen according to the binomial distribution or a [`MathError`]
    /// if `n < 1`, `p <= 0`, `p >= 1`, `n` does not fit into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let modulus = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 17").unwrap();
    ///
    /// let sample = PolynomialRingZq::sample_binomial(&modulus, -1, 2, 0.5).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if `n < 1`.
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    /// if `p <= 0` or `p >= 1`.
    /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
    /// if `n` does not fit into an [`i64`].
    ///
    /// # Panics ...
    /// - if the provided [`ModulusPolynomialRingZq`] has degree 0 or smaller.
    pub fn sample_binomial(
        modulus: &ModulusPolynomialRingZq,
        offset: impl Into<Z>,
        n: impl Into<Z>,
        p: impl Into<Q>,
    ) -> Result<Self, MathError> {
        assert!(
            modulus.get_degree() > 0,
            "ModulusPolynomial of degree 0 is insufficient to sample over."
        );

        let poly_z = PolyOverZ::sample_binomial(modulus.get_degree() - 1, offset, n, p)?;

        Ok(PolynomialRingZq {
            poly: poly_z,
            modulus: modulus.clone(),
        })
    }
}

#[cfg(test)]
mod test_sample_binomial {
    use super::{PolynomialRingZq, Z};
    use crate::{
        integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq},
        traits::{GetCoefficient, SetCoefficient},
    };
    use std::str::FromStr;

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether the boundaries of the interval are kept.
    #[test]
    fn boundaries_kept() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        for _ in 0..8 {
            let poly = PolynomialRingZq::sample_binomial(&modulus, -1, 2, 0.5).unwrap();
            let sample = poly.get_coeff(0).unwrap();
            assert!(Z::MINUS_ONE <= sample || sample <= Z::ONE);
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let mut modulus = PolyOverZq::from((1, u64::MAX));
            modulus.set_coeff(degree, 1).unwrap();
            let modulus = ModulusPolynomialRingZq::from(&modulus);

            let res = PolynomialRingZq::sample_binomial(&modulus, 1, 2, 0.5).unwrap();

            assert_eq!(modulus.get_degree(), res.get_degree() + 1);
        }
    }

    /// Checks whether 0 modulus polynomial is insufficient.
    #[test]
    #[should_panic]
    fn invalid_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("1  1 mod 17").unwrap();

        let _ = PolynomialRingZq::sample_binomial(&modulus, -1, 2, 0.5);
    }
}
