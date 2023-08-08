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
    integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
    rational::Q,
    traits::SetCoefficient,
    utils::sample::discrete_gauss::sample_z,
};

impl PolynomialRingZq {
    /// Initializes a new [`PolynomialRingZq`] with degree `modulus.get_degree() - 1`
    /// and with each entry sampled independently according to the
    /// discrete Gaussian distribution, using [`Z::sample_discrete_gauss`].
    ///
    /// Parameters:
    /// - `modulus`: specifies the [`ModulusPolynomialRingZq`] over which the
    /// ring of polynomials modulo `modulus.get_q()` is defined
    /// - `n`: specifies the range from which [`Z::sample_discrete_gauss`] samples
    /// - `center`: specifies the positions of the center with peak probability
    /// - `s`: specifies the Gaussian parameter, which is proportional
    /// to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a fresh [`PolynomialRingZq`] instance of length `modulus.get_degree() - 1`
    /// with coefficients chosen independently according the discrete Gaussian distribution or
    /// a [`MathError`] if `n <= 1` or `s <= 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let modulus = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 17").unwrap();
    ///
    /// let sample = PolynomialRingZq::sample_discrete_gauss(&modulus, 1024, 0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if `n <= 1` or `s <= 0`.
    ///
    /// # Panics ...
    /// - if the provided [`ModulusPolynomialRingZq`] has degree 0 or smaller.
    pub fn sample_discrete_gauss(
        modulus: &ModulusPolynomialRingZq,
        n: impl Into<Z>,
        center: impl Into<Q>,
        s: impl Into<Q>,
    ) -> Result<Self, MathError> {
        assert!(
            modulus.get_degree() > 0,
            "ModulusPolynomial of degree 0 is insufficient to sample over."
        );
        let n = n.into();
        let center = center.into();
        let s = s.into();
        let mut poly = PolynomialRingZq::from((&PolyOverZ::default(), modulus));

        for index in 0..modulus.get_degree() {
            let sample = sample_z(&n, &center, &s)?;
            poly.set_coeff(index, &sample)?;
        }
        Ok(poly)
    }
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::{
        integer::Z,
        integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
        rational::Q,
        traits::GetCoefficient,
    };
    use std::str::FromStr;

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let n = Z::from(1024);
        let center = Q::ZERO;
        let s = Q::ONE;
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 16u8, 0f32, 1u8);
        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 16u16, 0f64, 1u16);
        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 16u32, 0f32, 1u32);
        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 16u64, 0f64, 1u64);
        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 16u8, 0f32, 1i8);
        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 16i16, 0f32, 1i16);
        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 16i32, 0f32, 1i32);
        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 16i64, 0f64, 1i64);
        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, n, center, s);
        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 16i64, 0f32, 1f64);
    }

    /// Checks whether the boundaries of the interval are kept for small moduli.
    #[test]
    fn boundaries_kept_small() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        for _ in 0..32 {
            let poly = PolynomialRingZq::sample_discrete_gauss(&modulus, 1024, 15, 1).unwrap();

            for i in 0..3 {
                let sample: Z = poly.get_coeff(i).unwrap();
                assert!(Z::ZERO <= sample);
                assert!(sample < modulus.get_q());
            }
        }
    }

    /// Checks whether the boundaries of the interval are kept for large moduli.
    #[test]
    fn boundaries_kept_large() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();

        for _ in 0..256 {
            let poly = PolynomialRingZq::sample_discrete_gauss(&modulus, 1024, 1, 1).unwrap();

            for i in 0..3 {
                let sample: Z = poly.get_coeff(i).unwrap();
                assert!(Z::ZERO <= sample);
                assert!(sample < modulus.get_q());
            }
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let modulus = ModulusPolynomialRingZq::from_str(&format!(
                "{}  {}1 mod {}",
                degree + 1,
                "0 ".repeat(degree),
                u64::MAX
            ))
            .unwrap();

            let res = PolynomialRingZq::sample_discrete_gauss(&modulus, 1024, i64::MAX, 1).unwrap();

            assert_eq!(
                res.get_degree() + 1,
                modulus.get_degree(),
                "Could fail with negligible probability."
            );
        }
    }

    /// Checks whether 0 modulus polynomial is insufficient.
    #[test]
    #[should_panic]
    fn invalid_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("1  1 mod 17").unwrap();

        let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 1024, 0, 1).unwrap();
    }
}
