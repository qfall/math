// Copyright 2024 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for Gaussian distributions over [`MatQ`].

use crate::{
    error::MathError,
    macros::seeded::seedable_function,
    rational::{MatQ, Q},
    traits::{MatrixDimensions, MatrixGetEntry, MatrixSetEntry},
    utils::sample::uniform::SamplerRng,
};
use probability::{
    prelude::{Gaussian, Sample},
    source,
};
use rand::Rng;
use std::fmt::Display;

impl MatQ {
    seedable_function!(
        /// Chooses a [`MatQ`] instance according to the continuous Gaussian distribution.
        /// Here, each entry is chosen according to the provided distribution.
        ///
        /// Parameters:
        /// - `center`: specifies the center for each entry of the matrix individually
        /// - `sigma`: specifies the standard deviation
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns new [`MatQ`] sample chosen according to the specified continuous Gaussian
        /// distribution or a [`MathError`] if the specified parameters were not chosen
        /// appropriately (`sigma > 0`).
        ///
        /// # Examples
        /// ```
        /// use qfall_math::rational::MatQ;
        ///
        #[unseeded]
        /// let sample = MatQ::sample_gauss(&MatQ::new(5, 5), 1).unwrap();
        #[seeded]
        /// let sample = MatQ::sample_gauss_seeded(&MatQ::new(5, 5), 1, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`NonPositive`](MathError::NonPositive)
        ///   if `sigma <= 0`.
        pub(crate) fn sample_gauss(
            center: &MatQ,
            sigma: impl Into<f64>,
            seed: Option<[u8; 32]>,
        ) -> Result<MatQ, MathError> {
            let mut rng = SamplerRng::new(seed);

            let mut out = MatQ::new(center.get_num_rows(), center.get_num_columns());
            let sigma = sigma.into();

            for i in 0..out.get_num_rows() {
                for j in 0..out.get_num_columns() {
                    let center_entry_ij = center.get_entry(i, j)?;
                    let sample = Q::sample_gauss_optionally_seeded(
                        center_entry_ij,
                        sigma,
                        rng.derive_seed(),
                    )?;
                    unsafe { out.set_entry_unchecked(i, j, sample) };
                }
            }

            Ok(out)
        }
    );

    seedable_function!(
        /// Chooses a [`MatQ`] instance according to the continuous Gaussian distribution.
        /// Here, each entry is chosen according to the provided distribution and each entry
        /// is sampled with the same center.
        ///
        /// Parameters:
        /// - `num_rows`: specifies the number of rows of the sampled matrix
        /// - `num_cols`: specifies the number of columns of the sampled matrix
        /// - `center`: specifies the same center for each entry of the matrix
        /// - `sigma`: specifies the standard deviation
        #[seeded]
        /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
        #[optionally_seeded]
        /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling.
        #[optionally_seeded]
        ///   If `None` is provided, a fresh [`ThreadRng`](rand::rngs::ThreadRng) is used instead.
        ///
        /// Returns new [`MatQ`] sample chosen according to the specified continuous Gaussian
        /// distribution or a [`MathError`] if the specified parameters were not chosen
        /// appropriately (`sigma > 0`).
        ///
        /// # Examples
        /// ```
        /// use qfall_math::rational::{Q, MatQ};
        ///
        /// let center = Q::from((5,2));
        ///
        #[unseeded]
        /// let sample = MatQ::sample_gauss_same_center(5, 5, &center, 1).unwrap();
        #[seeded]
        /// let sample = MatQ::sample_gauss_same_center_seeded(5, 5, &center, 1, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`NonPositive`](MathError::NonPositive)
        ///   if `sigma <= 0`.
        ///
        /// # Panics ...
        /// - if the number of rows or columns is negative, `0`, or does not fit into an [`i64`].
        pub(crate) fn sample_gauss_same_center(
            num_rows: impl TryInto<i64> + Display,
            num_cols: impl TryInto<i64> + Display,
            center: impl Into<Q>,
            sigma: impl Into<f64>,
            seed: Option<[u8; 32]>,
        ) -> Result<MatQ, MathError> {
            let mut out = MatQ::new(num_rows, num_cols);
            let (center, sigma) = (center.into(), sigma.into());
            if sigma <= 0.0 {
                return Err(MathError::NonPositive(format!(
                    "The sigma has to be positive and not zero, but the provided value is {sigma}."
                )));
            }
            let mut rng = SamplerRng::new(seed);
            let mut source = source::default(rng.next_u64());

            // Instead of sampling with a center of c, we sample with center 0 and add the
            // center later. These are equivalent and this way we can sample in larger ranges
            let sampler = Gaussian::new(0.0, sigma);

            for i in 0..out.get_num_rows() {
                for j in 0..out.get_num_columns() {
                    let mut sample = Q::from(sampler.sample(&mut source));
                    sample += &center;
                    unsafe { out.set_entry_unchecked(i, j, sample) };
                }
            }

            Ok(out)
        }
    );
}

#[cfg(test)]
mod test_sample_gauss {
    use crate::utils::sample::test_seed;
    use crate::{rational::MatQ, traits::MatrixDimensions};

    /// Ensure that an error is returned if `sigma` is not positive
    #[test]
    fn non_positive_sigma() {
        for seeded in [false, true] {
            let center = MatQ::new(5, 5);
            for sigma in [0, -1] {
                assert!(
                    MatQ::sample_gauss_optionally_seeded(&center, sigma, seeded.then(test_seed))
                        .is_err()
                )
            }
        }
    }

    /// Ensure that the samples are of correct dimension
    #[test]
    fn correct_dimension() {
        for seeded in [false, true] {
            for (x, y) in [(5, 5), (1, 10), (10, 1)] {
                let center = MatQ::new(x, y);
                let sample =
                    MatQ::sample_gauss_optionally_seeded(&center, 1, seeded.then(test_seed))
                        .unwrap();
                assert_eq!(center.get_num_rows(), sample.get_num_rows());
                assert_eq!(center.get_num_columns(), sample.get_num_columns());
            }
        }
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::rational::MatQ;
        let sample_0 = MatQ::sample_gauss_seeded(&MatQ::new(5, 5), 1, [42; 32]).unwrap();
        let sample_1 = MatQ::sample_gauss_seeded(&MatQ::new(5, 5), 1, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }

    /// Checks whether the seeded variant outputs the known sample for a fixed seed.
    #[test]
    fn known_answer() {
        use crate::rational::MatQ;
        let sample = MatQ::sample_gauss_seeded(&MatQ::new(5, 5), 1, [42; 32]).unwrap();

        assert_eq!(
            "[[-4945271350741753/2251799813685248, 1117106275816641/2251799813685248, 4434555541986695/4503599627370496, -6539644456987479/4503599627370496, -4677571318743725/9007199254740992],[3908611230479557/4503599627370496, 5573654194347613/9007199254740992, 5403302998575453/9007199254740992, 2430733040590187/9007199254740992, 1031578748721027/4503599627370496],[-4883384444105643/9007199254740992, -3764944878914815/2251799813685248, -7161261431757703/2251799813685248, -5092217727994081/9007199254740992, -2353868661553283/4503599627370496],[4063319294552583/9007199254740992, 2715651668966247/2251799813685248, -7464330407867217/9007199254740992, -8311230105715239/72057594037927936, -4329275745410667/2251799813685248],[-3100112952240901/18014398509481984, 3412362636860941/576460752303423488, -4689787695738317/4503599627370496, 3370477389923299/2251799813685248, 1145812122695171/4503599627370496]]",
            sample.to_string()
        );
    }

    /// Checks whether the unseeded and the seeded function are available.
    #[test]
    fn availability() {
        use crate::rational::MatQ;

        // explicitly checks the existence of the unseeded and the seeded function
        let _ = MatQ::sample_gauss(&MatQ::new(5, 5), 1);
        let _ = MatQ::sample_gauss_seeded(&MatQ::new(5, 5), 1, test_seed());
    }
}

#[cfg(test)]
mod test_sample_gauss_same_center {
    use crate::utils::sample::test_seed;

    use crate::{rational::MatQ, traits::MatrixDimensions};

    /// Ensure that an error is returned if `sigma` is not positive
    #[test]
    fn non_positive_sigma() {
        for seeded in [false, true] {
            for sigma in [0, -1] {
                assert!(
                    MatQ::sample_gauss_same_center_optionally_seeded(
                        5,
                        5,
                        0,
                        sigma,
                        seeded.then(test_seed)
                    )
                    .is_err()
                )
            }
        }
    }

    /// Ensure that the samples are of correct dimension
    #[test]
    fn correct_dimension() {
        for seeded in [false, true] {
            for (x, y) in [(5, 5), (1, 10), (10, 1)] {
                let sample = MatQ::sample_gauss_same_center_optionally_seeded(
                    x,
                    y,
                    0,
                    1,
                    seeded.then(test_seed),
                )
                .unwrap();
                assert_eq!(x, sample.get_num_rows());
                assert_eq!(y, sample.get_num_columns());
            }
        }
    }

    /// Ensure that a negative number of rows causes a panic
    #[test]
    fn negative_number_rows() {
        for seeded in [false, true] {
            let result = std::panic::catch_unwind(|| {
                let _ = MatQ::sample_gauss_same_center_optionally_seeded(
                    -1,
                    1,
                    0,
                    1,
                    seeded.then(test_seed),
                )
                .unwrap();
            });
            assert!(result.is_err());
        }
    }

    /// Ensure that a negative number of columns causes a panic
    #[test]
    fn negative_number_columns() {
        for seeded in [false, true] {
            let result = std::panic::catch_unwind(|| {
                let _ = MatQ::sample_gauss_same_center_optionally_seeded(
                    1,
                    -1,
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
        use crate::rational::{MatQ, Q};
        let center = Q::from((5, 2));
        let sample_0 = MatQ::sample_gauss_same_center_seeded(5, 5, &center, 1, [42; 32]).unwrap();
        let sample_1 = MatQ::sample_gauss_same_center_seeded(5, 5, &center, 1, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }

    /// Checks whether the seeded variant outputs the known sample for a fixed seed.
    #[test]
    fn known_answer() {
        use crate::rational::{MatQ, Q};
        let center = Q::from((5, 2));
        let sample = MatQ::sample_gauss_same_center_seeded(5, 5, &center, 1, [42; 32]).unwrap();

        assert_eq!(
            "[[8525870560382491/2251799813685248, 17119947174636167/4503599627370496, 1259641011116081/1125899906842624, 39499623190823409/18014398509481984, 3385362557569009/4503599627370496],[3938234223310835/2251799813685248, 17542906212059721/4503599627370496, 16597635972078743/4503599627370496, 8266208908835155/2251799813685248, 39314002964552041/18014398509481984],[881046098121435/562949953421312, 29287177467398541/9007199254740992, 2413886157177875/562949953421312, 981581273026087/281474976710656, 43488189713909861/18014398509481984],[6127343065657779/4503599627370496, 30937068457746009/9007199254740992, 27849268867401663/9007199254740992, 2727502571816845/2251799813685248, 27040028183639271/9007199254740992],[13289162739536831/4503599627370496, 87685859291908515/36028797018963968, 93185871850127433/36028797018963968, 2111809547791415/1125899906842624, 4077230155367515/2251799813685248]]",
            sample.to_string()
        );
    }

    /// Checks whether the unseeded and the seeded function are available.
    #[test]
    fn availability() {
        use crate::rational::{MatQ, Q};
        let center = Q::from((5, 2));

        // explicitly checks the existence of the unseeded and the seeded function
        let _ = MatQ::sample_gauss_same_center(5, 5, &center, 1);
        let _ = MatQ::sample_gauss_same_center_seeded(5, 5, &center, 1, test_seed());
    }
}
