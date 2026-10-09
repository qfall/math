// Copyright 2023 Jan Niklas Siemer
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
    macros::seeded::seedable_function,
};

impl PolynomialRingZq {
    seedable_function!(
        /// Generates a [`PolynomialRingZq`] instance with maximum degree `modulus.get_degree() - 1`
        /// and coefficients chosen uniform at random in `[0, modulus.get_q())`.
        ///
        /// The internally used uniform at random chosen bytes are generated
        #[unseeded]
        /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and is
        #[seeded]
        /// by a [`StdRng`](rand::rngs::StdRng) seeded with `seed`, which uses ChaCha12 and is
        #[optionally_seeded]
        /// by a [`StdRng`](rand::rngs::StdRng) seeded with `seed` or by [`ThreadRng`](rand::rngs::ThreadRng)
        #[optionally_seeded]
        /// if `seed` is `None`. Both use ChaCha12 and are
        /// considered cryptographically secure.
        ///
        /// Parameters:
        /// - `modulus`: specifies the [`ModulusPolynomialRingZq`] over which the
        ///   ring of polynomials modulo `modulus.get_q()` is defined
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns a fresh [`PolynomialRingZq`] instance of length `modulus.get_degree() - 1`
        /// with coefficients chosen uniform at random in `[0, modulus.get_q())`.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
        /// use std::str::FromStr;
        /// let modulus = ModulusPolynomialRingZq::from_str("3  1 2 1 mod 17").unwrap();
        ///
        #[unseeded]
        /// let sample = PolynomialRingZq::sample_uniform(&modulus);
        #[seeded]
        /// let sample = PolynomialRingZq::sample_uniform_seeded(&modulus, [42; 32]);
        /// ```
        ///
        /// # Panics ...
        /// - if the provided [`ModulusPolynomialRingZq`] has degree `0` or smaller.
        pub(crate) fn sample_uniform(
            modulus: impl Into<ModulusPolynomialRingZq>,
            seed: Option<[u8; 32]>,
        ) -> Self {
            let modulus = modulus.into();
            assert!(
                modulus.get_degree() > 0,
                "ModulusPolynomial of degree 0 is insufficient to sample over."
            );

            let poly_z = PolyOverZ::sample_uniform_optionally_seeded(
                modulus.get_degree() - 1,
                0,
                modulus.get_q(),
                seed,
            )
            .unwrap();

            // we do not have to reduce here, as all entries are already in the correct range
            // hence directly setting is more efficient
            PolynomialRingZq {
                poly: poly_z,
                modulus,
            }
        }
    );
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

#[cfg(test)]
mod test_sample_uniform_seeded {
    use crate::utils::sample::test_seed;
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
            let poly = PolynomialRingZq::sample_uniform_seeded(&modulus, test_seed());

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
            let poly = PolynomialRingZq::sample_uniform_seeded(&modulus, test_seed());

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

            let res = PolynomialRingZq::sample_uniform_seeded(&modulus, test_seed());

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

        let _ = PolynomialRingZq::sample_uniform_seeded(&modulus, test_seed());
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq};
        use std::str::FromStr;
        let modulus = ModulusPolynomialRingZq::from_str("3  1 2 1 mod 17").unwrap();
        let sample_0 = PolynomialRingZq::sample_uniform_seeded(&modulus, [42; 32]);
        let sample_1 = PolynomialRingZq::sample_uniform_seeded(&modulus, [42; 32]);

        assert_eq!(sample_0, sample_1);
    }
}
