// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the uniform distribution.

use crate::{
    integer::PolyOverZ,
    integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
};

impl PolynomialRingZq {
    /// Generates a [`PolynomialRingZq`] instance with maximum degree `modulus.get_degree() - 1`
    /// and coefficients chosen uniform at random in `[0, modulus.get_q())`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `modulus`: specifies the [`ModulusPolynomialRingZq`] over which the
    /// ring of polynomials modulo `modulus.get_q()` is defined
    ///
    /// Returns a fresh [`PolynomialRingZq`] instance of length `modulus.get_degree() - 1`
    /// with coefficients chosen uniform at random in `[0, modulus.get_q())`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let modulus = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 17").unwrap();
    ///
    /// let sample = PolynomialRingZq::sample_uniform(&modulus);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided [`ModulusPolynomialRingZq`] has degree `0` or smaller.
    pub fn sample_uniform(modulus: impl Into<ModulusPolynomialRingZq>) -> Self {
        let modulus = modulus.into();
        assert!(
            modulus.get_degree() > 0,
            "ModulusPolynomial of degree 0 is insufficient to sample over."
        );

        let poly_z =
            PolyOverZ::sample_uniform(modulus.get_degree() - 1, 0, modulus.get_q()).unwrap();

        // we do not have to reduce here, as all entries are already in the correct range
        // hence directly setting is more efficient
        PolynomialRingZq {
            poly: poly_z,
            modulus,
        }
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{
        integer::Z,
        integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq},
        traits::{GetCoefficient, SetCoefficient},
    };
    use std::str::FromStr;

    /// Checks whether the boundaries of the interval are kept for small moduli.
    #[test]
    fn boundaries_kept_small() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        for _ in 0..32 {
            let poly = PolynomialRingZq::sample_uniform(&modulus);

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
            let poly = PolynomialRingZq::sample_uniform(&modulus);

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
            let mut modulus = PolyOverZq::from((1, u64::MAX));
            modulus.set_coeff(degree, 1).unwrap();
            let modulus = ModulusPolynomialRingZq::from(&modulus);

            let res = PolynomialRingZq::sample_uniform(&modulus);

            assert_eq!(
                res.get_degree() + 1,
                modulus.get_degree(),
                "Could fail with probability 1/{}.",
                u64::MAX
            );
        }
    }

    /// Checks whether 0 modulus polynomial is insufficient.
    #[test]
    #[should_panic]
    fn invalid_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("1  1 mod 17").unwrap();

        let _ = PolynomialRingZq::sample_uniform(&modulus);
    }
}
