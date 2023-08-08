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
    traits::SetCoefficient,
    utils::sample::uniform::sample_uniform_rejection,
};

impl PolynomialRingZq {
    /// Generates a [`PolynomialRingZq`] instance of the according length
    /// from the provided `modulus.get_degree() - 1` and coefficients chosen
    /// uniform at random in `[0, modulus.get_q())`.
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
    /// - if the provided [`ModulusPolynomialRingZq`] has degree 0 or smaller.
    pub fn sample_uniform(modulus: &ModulusPolynomialRingZq) -> Self {
        assert!(
            modulus.get_degree() > 0,
            "ModulusPolynomial of degree 0 is insufficient to sample over."
        );
        let interval_size = modulus.get_q();
        let mut poly = PolynomialRingZq::from((&PolyOverZ::default(), modulus));

        for index in 0..modulus.get_degree() {
            let sample = sample_uniform_rejection(&interval_size).unwrap();
            poly.set_coeff(index, &sample).unwrap();
        }
        poly
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{
        integer::Z,
        integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
        traits::GetCoefficient,
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
            let modulus = ModulusPolynomialRingZq::from_str(&format!(
                "{}  {}1 mod {}",
                degree + 1,
                "0 ".repeat(degree),
                u64::MAX
            ))
            .unwrap();

            let res = PolynomialRingZq::sample_uniform(&modulus);

            assert_eq!(
                res.get_degree() + 1,
                modulus.get_degree(),
                "Could fail with probability 1/u64::MAX."
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
