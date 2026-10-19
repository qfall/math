// Copyright 2023 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling
//! according to the discrete Gaussian distribution.

use crate::{
    error::MathError,
    integer::PolyOverZ,
    integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
    macros::seeded::seedable_function,
    rational::Q,
};

impl PolynomialRingZq {
    seedable_function!(
        /// Initializes a new [`PolynomialRingZq`] with maximum degree `modulus.get_degree() - 1`
        /// and with each entry sampled independently according to the
        /// discrete Gaussian distribution.
        ///
        /// Parameters:
        /// - `modulus`: specifies the [`ModulusPolynomialRingZq`] over which the
        ///   ring of polynomials modulo `modulus.get_q()` is defined
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
        /// Returns a fresh [`PolynomialRingZq`] instance of length `modulus.get_degree() - 1`
        /// with coefficients chosen independently according the discrete Gaussian distribution or
        /// a [`MathError`] if `s < 0`.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
        /// use std::str::FromStr;
        /// let modulus = ModulusPolynomialRingZq::from_str("3  1 2 1 mod 17").unwrap();
        ///
        #[unseeded]
        /// let sample = PolynomialRingZq::sample_discrete_gauss(&modulus, 0, 1).unwrap();
        #[seeded]
        /// let sample = PolynomialRingZq::sample_discrete_gauss_seeded(&modulus, 0, 1, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `s < 0`.
        ///
        /// # Panics ...
        /// - if the provided [`ModulusPolynomialRingZq`] has degree `0` or smaller.
        pub(crate) fn sample_discrete_gauss(
            modulus: impl Into<ModulusPolynomialRingZq>,
            center: impl Into<Q>,
            s: impl Into<Q>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let modulus = modulus.into();
            assert!(
                modulus.get_degree() > 0,
                "ModulusPolynomial of degree 0 is insufficient to sample over."
            );

            let poly_z = PolyOverZ::sample_discrete_gauss_optionally_seeded(
                modulus.get_degree() - 1,
                center,
                s,
                seed,
            )?;
            let mut poly_ringzq = PolynomialRingZq {
                poly: poly_z,
                modulus,
            };
            poly_ringzq.reduce();

            Ok(poly_ringzq)
        }
    );
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::utils::sample::test_seed;
    use crate::{
        integer::Z,
        integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq},
        rational::Q,
        traits::{GetCoefficient, SetCoefficient},
    };
    use std::str::FromStr;

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        for seeded in [false, true] {
            let center = Q::ZERO;
            let s = Q::ONE;
            let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

            let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                &modulus,
                0f32,
                1u8,
                seeded.then(test_seed),
            );
            let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                &modulus,
                0f64,
                1u16,
                seeded.then(test_seed),
            );
            let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                &modulus,
                0f32,
                1u32,
                seeded.then(test_seed),
            );
            let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                &modulus,
                0f64,
                1u64,
                seeded.then(test_seed),
            );
            let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                &modulus,
                0f32,
                1i8,
                seeded.then(test_seed),
            );
            let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                &modulus,
                0f32,
                1i16,
                seeded.then(test_seed),
            );
            let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                &modulus,
                0f32,
                1i32,
                seeded.then(test_seed),
            );
            let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                &modulus,
                0f64,
                1i64,
                seeded.then(test_seed),
            );
            let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                &modulus,
                center,
                s,
                seeded.then(test_seed),
            );
            let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                &modulus,
                0f32,
                1f64,
                seeded.then(test_seed),
            );

            // explicitly checks the existence of the unseeded and the seeded function
            if seeded {
                let _ = PolynomialRingZq::sample_discrete_gauss_seeded(
                    &modulus,
                    0f32,
                    1u8,
                    test_seed(),
                );
            } else {
                let _ = PolynomialRingZq::sample_discrete_gauss(&modulus, 0f32, 1u8);
            }
        }
    }

    /// Checks whether the boundaries of the interval are kept for small moduli.
    #[test]
    fn boundaries_kept_small() {
        for seeded in [false, true] {
            let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

            for _ in 0..32 {
                let poly = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                    &modulus,
                    15,
                    1,
                    seeded.then(test_seed),
                )
                .unwrap();

                for i in 0..3 {
                    let sample: Z = poly.get_coeff(i).unwrap();
                    assert!(Z::ZERO <= sample);
                    assert!(sample < modulus.get_q());
                }
            }
        }
    }

    /// Checks whether the boundaries of the interval are kept for large moduli.
    #[test]
    fn boundaries_kept_large() {
        for seeded in [false, true] {
            let modulus =
                ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();

            for _ in 0..256 {
                let poly = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                    &modulus,
                    1,
                    1,
                    seeded.then(test_seed),
                )
                .unwrap();

                for i in 0..3 {
                    let sample: Z = poly.get_coeff(i).unwrap();
                    assert!(Z::ZERO <= sample);
                    assert!(sample < modulus.get_q());
                }
            }
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        for seeded in [false, true] {
            let degrees = [1, 3, 7, 15, 32, 120];
            for degree in degrees {
                let mut modulus = PolyOverZq::from((1, u64::MAX));
                modulus.set_coeff(degree, 1).unwrap();
                let modulus = ModulusPolynomialRingZq::from(&modulus);

                let res = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                    &modulus,
                    i64::MAX,
                    1,
                    seeded.then(test_seed),
                )
                .unwrap();

                assert_eq!(
                    res.get_degree() + 1,
                    modulus.get_degree(),
                    "Could fail with negligible probability."
                );
            }
        }
    }

    /// Checks whether 0 degree modulus polynomial is insufficient.
    #[test]
    fn invalid_modulus() {
        for seeded in [false, true] {
            let result = std::panic::catch_unwind(|| {
                let modulus = ModulusPolynomialRingZq::from_str("1  1 mod 17").unwrap();

                let _ = PolynomialRingZq::sample_discrete_gauss_optionally_seeded(
                    &modulus,
                    0,
                    1,
                    seeded.then(test_seed),
                )
                .unwrap();
            });
            assert!(result.is_err());
        }
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq};
        use std::str::FromStr;
        let modulus = ModulusPolynomialRingZq::from_str("3  1 2 1 mod 17").unwrap();
        let sample_0 =
            PolynomialRingZq::sample_discrete_gauss_seeded(&modulus, 0, 1, [42; 32]).unwrap();
        let sample_1 =
            PolynomialRingZq::sample_discrete_gauss_seeded(&modulus, 0, 1, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }

    /// Checks whether the seeded variant outputs the known sample for a fixed seed.
    #[test]
    fn known_answer() {
        use crate::integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq};
        use std::str::FromStr;
        let modulus = ModulusPolynomialRingZq::from_str("3  1 2 1 mod 17").unwrap();
        let sample =
            PolynomialRingZq::sample_discrete_gauss_seeded(&modulus, 0, 1, [42; 32]).unwrap();

        assert_eq!("1  1 / 3  1 2 1 mod 17", sample.to_string());
    }
}
