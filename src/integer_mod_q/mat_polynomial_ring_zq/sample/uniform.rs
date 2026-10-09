// Copyright 2023 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for uniform distributions.

use crate::{
    integer::MatPolyOverZ,
    integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    macros::seeded::seedable_function,
};
use std::fmt::Display;

impl MatPolynomialRingZq {
    seedable_function!(
        /// Outputs a [`MatPolynomialRingZq`] instance with polynomials as entries,
        /// whose coefficients were chosen uniform at random in `[0, modulus.get_q())`.
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
        /// - `num_rows`: specifies the number of rows the new matrix should have
        /// - `num_cols`: specifies the number of columns the new matrix should have
        /// - `modulus`: specifies the [`ModulusPolynomialRingZq`] over which the
        ///   ring of polynomials modulo `modulus.get_q()` is defined
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns a fresh [`MatPolynomialRingZq`] instance of length `modulus.get_degree() - 1`
        /// with coefficients chosen uniform at random in `[0, modulus.get_q())`.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
        /// use std::str::FromStr;
        /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        ///
        #[unseeded]
        /// let matrix = MatPolynomialRingZq::sample_uniform(2, 2, &modulus);
        #[seeded]
        /// let matrix = MatPolynomialRingZq::sample_uniform_seeded(2, 2, &modulus, [42; 32]);
        /// ```
        ///
        /// # Panics ...
        /// - if the provided number of rows and columns are not suited to create a matrix.
        ///   For further information see [`MatPolynomialRingZq::new`].
        /// - if the provided [`ModulusPolynomialRingZq`] has degree `0`.
        pub(crate) fn sample_uniform(
            num_rows: impl TryInto<i64> + Display,
            num_cols: impl TryInto<i64> + Display,
            modulus: impl Into<ModulusPolynomialRingZq>,
            seed: Option<[u8; 32]>,
        ) -> Self {
            let modulus = modulus.into();
            assert!(
                modulus.get_degree() > 0,
                "ModulusPolynomial of degree 0 is insufficient to sample over."
            );

            let matrix = MatPolyOverZ::sample_uniform_optionally_seeded(
                num_rows,
                num_cols,
                modulus.get_degree() - 1,
                0,
                modulus.get_q(),
                seed,
            )
            .unwrap();
            MatPolynomialRingZq::from((matrix, modulus))
        }
    );
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::integer::PolyOverZ;
    use crate::integer_mod_q::PolyOverZq;
    use crate::traits::{GetCoefficient, MatrixDimensions, MatrixGetEntry, SetCoefficient};
    use crate::{
        integer::Z,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        for _ in 0..32 {
            let matrix = MatPolynomialRingZq::sample_uniform(1, 1, &modulus);
            let sample: PolyOverZ = matrix.get_entry(0, 0).unwrap();
            let coeff = sample.get_coeff(0).unwrap();

            assert!(Z::ZERO <= coeff);
            assert!(coeff < 17);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large intervals.
    #[test]
    fn boundaries_kept_large() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();

        for _ in 0..256 {
            let matrix = MatPolynomialRingZq::sample_uniform(1, 1, &modulus);
            let sample: PolyOverZ = matrix.get_entry(0, 0).unwrap();
            let coeff = sample.get_coeff(0).unwrap();

            assert!(Z::ZERO <= coeff);
            assert!(coeff < u64::MAX);
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

            let matrix = MatPolynomialRingZq::sample_uniform(1, 1, &modulus);
            let poly: PolyOverZ = matrix.get_entry(0, 0).unwrap();

            assert_eq!(
                degree,
                poly.get_degree() + 1,
                "This test can fail with probability close to 0."
            );
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too large for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let _ = MatPolynomialRingZq::sample_uniform(0, 3, &modulus);
    }

    /// Checks whether 0 modulus polynomial is insufficient.
    #[test]
    #[should_panic]
    fn invalid_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("1  1 mod 17").unwrap();

        let _ = MatPolynomialRingZq::sample_uniform(1, 1, &modulus);
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let mat_0 = MatPolynomialRingZq::sample_uniform(3, 3, &modulus);
        let mat_1 = MatPolynomialRingZq::sample_uniform(4, 1, &modulus);
        let mat_2 = MatPolynomialRingZq::sample_uniform(1, 5, &modulus);
        let mat_3 = MatPolynomialRingZq::sample_uniform(15, 20, &modulus);

        assert_eq!(3, mat_0.get_num_rows());
        assert_eq!(3, mat_0.get_num_columns());
        assert_eq!(4, mat_1.get_num_rows());
        assert_eq!(1, mat_1.get_num_columns());
        assert_eq!(1, mat_2.get_num_rows());
        assert_eq!(5, mat_2.get_num_columns());
        assert_eq!(15, mat_3.get_num_rows());
        assert_eq!(20, mat_3.get_num_columns());
    }
}

#[cfg(test)]
mod test_sample_uniform_seeded {
    use crate::integer::PolyOverZ;
    use crate::integer_mod_q::PolyOverZq;
    use crate::traits::{GetCoefficient, MatrixDimensions, MatrixGetEntry, SetCoefficient};
    use crate::utils::sample::test_seed;
    use crate::{
        integer::Z,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        for _ in 0..32 {
            let matrix = MatPolynomialRingZq::sample_uniform_seeded(1, 1, &modulus, test_seed());
            let sample: PolyOverZ = matrix.get_entry(0, 0).unwrap();
            let coeff = sample.get_coeff(0).unwrap();

            assert!(Z::ZERO <= coeff);
            assert!(coeff < 17);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large intervals.
    #[test]
    fn boundaries_kept_large() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();

        for _ in 0..256 {
            let matrix = MatPolynomialRingZq::sample_uniform_seeded(1, 1, &modulus, test_seed());
            let sample: PolyOverZ = matrix.get_entry(0, 0).unwrap();
            let coeff = sample.get_coeff(0).unwrap();

            assert!(Z::ZERO <= coeff);
            assert!(coeff < u64::MAX);
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

            let matrix = MatPolynomialRingZq::sample_uniform_seeded(1, 1, &modulus, test_seed());
            let poly: PolyOverZ = matrix.get_entry(0, 0).unwrap();

            assert_eq!(
                degree,
                poly.get_degree() + 1,
                "This test can fail with probability close to 0."
            );
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too large for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let _ = MatPolynomialRingZq::sample_uniform_seeded(0, 3, &modulus, test_seed());
    }

    /// Checks whether 0 modulus polynomial is insufficient.
    #[test]
    #[should_panic]
    fn invalid_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("1  1 mod 17").unwrap();

        let _ = MatPolynomialRingZq::sample_uniform_seeded(1, 1, &modulus, test_seed());
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let mat_0 = MatPolynomialRingZq::sample_uniform_seeded(3, 3, &modulus, test_seed());
        let mat_1 = MatPolynomialRingZq::sample_uniform_seeded(4, 1, &modulus, test_seed());
        let mat_2 = MatPolynomialRingZq::sample_uniform_seeded(1, 5, &modulus, test_seed());
        let mat_3 = MatPolynomialRingZq::sample_uniform_seeded(15, 20, &modulus, test_seed());

        assert_eq!(3, mat_0.get_num_rows());
        assert_eq!(3, mat_0.get_num_columns());
        assert_eq!(4, mat_1.get_num_rows());
        assert_eq!(1, mat_1.get_num_columns());
        assert_eq!(1, mat_2.get_num_rows());
        assert_eq!(5, mat_2.get_num_columns());
        assert_eq!(15, mat_3.get_num_rows());
        assert_eq!(20, mat_3.get_num_columns());
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
        use std::str::FromStr;
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let sample_0 = MatPolynomialRingZq::sample_uniform_seeded(2, 2, &modulus, [42; 32]);
        let sample_1 = MatPolynomialRingZq::sample_uniform_seeded(2, 2, &modulus, [42; 32]);

        assert_eq!(sample_0, sample_1);
    }
}
