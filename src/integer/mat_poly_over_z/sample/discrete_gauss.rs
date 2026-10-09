// Copyright 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the discrete Gaussian distribution.

use crate::{
    error::MathError,
    integer::{MatPolyOverZ, MatZ, PolyOverZ},
    macros::seeded::seedable_function,
    rational::{PolyOverQ, Q},
    traits::{
        Concatenate, FromCoefficientEmbedding, IntoCoefficientEmbedding, MatrixDimensions,
        MatrixSetEntry, SetCoefficient,
    },
    utils::{
        index::evaluate_index,
        sample::discrete_gauss::{DiscreteGaussianIntegerSampler, LookupTableSetting, TAILCUT},
    },
};
use std::fmt::Display;

impl MatPolyOverZ {
    seedable_function!(
        /// Initializes a new matrix with dimensions `num_rows` x `num_columns` and with each entry
        /// sampled independently according to the discrete Gaussian distribution,
        /// using [`PolyOverZ::sample_discrete_gauss`].
        ///
        /// Parameters:
        /// - `num_rows`: specifies the number of rows the new matrix should have
        /// - `num_cols`: specifies the number of columns the new matrix should have
        /// - `max_degree`: specifies the included maximal degree the created [`PolyOverZ`] should have
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
        /// Returns a [`MatPolyOverZ`] with each entry sampled independently from the
        /// specified discrete Gaussian distribution or an error if `s < 0`.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer::MatPolyOverZ;
        ///
        #[unseeded]
        /// let matrix = MatPolyOverZ::sample_discrete_gauss(3, 1, 5, 0, 1.25f32).unwrap();
        #[seeded]
        /// let matrix = MatPolyOverZ::sample_discrete_gauss_seeded(3, 1, 5, 0, 1.25f32, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `s < 0`.
        ///
        /// # Panics ...
        /// - if the provided number of rows and columns are not suited to create a matrix.
        ///   For further information see [`MatPolyOverZ::new`].
        /// - if `max_degree` is negative, or does not fit into an [`i64`].
        pub(crate) fn sample_discrete_gauss(
            num_rows: impl TryInto<i64> + Display,
            num_cols: impl TryInto<i64> + Display,
            max_degree: impl TryInto<i64> + Display,
            center: impl Into<Q>,
            s: impl Into<Q>,
            seed: Option<[u8; 32]>,
        ) -> Result<MatPolyOverZ, MathError> {
            let max_degree = evaluate_index(max_degree).unwrap();
            let mut matrix = MatPolyOverZ::new(num_rows, num_cols);

            let mut dgis = DiscreteGaussianIntegerSampler::init(
                center,
                s,
                unsafe { TAILCUT },
                LookupTableSetting::FillOnTheFly,
                seed,
            )?;

            for row in 0..matrix.get_num_rows() {
                for col in 0..matrix.get_num_columns() {
                    let mut entry = PolyOverZ::default();
                    for index in 0..=max_degree {
                        let sample = dgis.sample_z();
                        unsafe { entry.set_coeff_unchecked(index, &sample) };
                    }

                    unsafe { matrix.set_entry_unchecked(row, col, entry) };
                }
            }

            Ok(matrix)
        }
    );

    seedable_function!(
        /// SampleD samples a discrete Gaussian from the lattice with a provided `basis`.
        ///
        /// We do not check whether `basis` is actually a basis. Hence, the callee is
        /// responsible for making sure that `basis` provides a suitable basis.
        ///
        /// Parameters:
        /// - `basis`: specifies a basis for the lattice from which is sampled
        /// - `k`: the maximal length the polynomial can have
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
        /// Returns a vector of polynomials sampled according to the
        /// discrete Gaussian distribution or an error if the basis is not a row vector,
        /// `s < 0`, or the number of rows of the `basis` and `center` differ.
        ///
        /// # Example
        /// ```
        /// use qfall_math::{
        ///     integer::MatPolyOverZ,
        ///     rational::PolyOverQ,
        /// };
        /// use std::str::FromStr;
        ///
        /// let basis = MatPolyOverZ::from_str("[[1  1, 3  0 1 -1, 2  2 2]]").unwrap();
        /// let center = vec![PolyOverQ::default()];
        ///
        #[unseeded]
        /// let sample = MatPolyOverZ::sample_d(&basis, 3, &center, 10.5_f64).unwrap();
        #[seeded]
        /// let sample = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 10.5_f64, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`VectorFunctionCalledOnNonVector`](MathError::VectorFunctionCalledOnNonVector),
        ///   if the basis is not a row vector.
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `s < 0`.
        /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
        ///   if the number of rows of the `basis` and `center` differ.
        ///
        /// This function implements SampleD according to:
        /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
        ///   Trapdoors for hard lattices and new cryptographic constructions.
        ///   In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
        ///   <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
        ///
        /// # Panics ...
        /// - if the polynomials have higher length than the provided upper bound `k`
        pub(crate) fn sample_d(
            basis: &Self,
            k: impl Into<i64>,
            center: &[PolyOverQ],
            s: impl Into<Q>,
            seed: Option<[u8; 32]>,
        ) -> Result<MatPolyOverZ, MathError> {
            let k = k.into();
            // use coefficient embedding and then call sampleD for the matrix representation
            let basis_embedded = basis.into_coefficient_embedding(k);

            // use coefficient embedding to get center
            let mut center_embedded = center[0].into_coefficient_embedding(k);
            for row in center.iter().skip(1) {
                let c_row = row.into_coefficient_embedding(k);
                center_embedded = center_embedded.concat_vertical(&c_row)?;
            }

            let sample =
                MatZ::sample_d_optionally_seeded(&basis_embedded, &center_embedded, s, seed)?;

            Ok(MatPolyOverZ::from_coefficient_embedding((&sample, k - 1)))
        }
    );
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::{integer::MatPolyOverZ, traits::MatrixGetEntry};

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let _ = MatPolyOverZ::sample_discrete_gauss(2, 3, 128, 1u16, 2);
        let _ = MatPolyOverZ::sample_discrete_gauss(1, 3, 128, 1u8, 2.0);
        let _ = MatPolyOverZ::sample_discrete_gauss(2_i64, 3, 128, 1u32, 2.0_f64);
        let _ = MatPolyOverZ::sample_discrete_gauss(2_i32, 3, 128, 1u64, 1);
        let _ = MatPolyOverZ::sample_discrete_gauss(2_i16, 3, 128, 1i64, 3_u64);
        let _ = MatPolyOverZ::sample_discrete_gauss(2_i8, 3, 128, 1i32, 1);
        let _ = MatPolyOverZ::sample_discrete_gauss(2_u64, 3, 128, 1i16, 1);
        let _ = MatPolyOverZ::sample_discrete_gauss(2_u32, 3, 128, 1i8, 1);
        let _ = MatPolyOverZ::sample_discrete_gauss(2_u16, 3, 128, 1i64, 2);
        let _ = MatPolyOverZ::sample_discrete_gauss(2_u8, 3, 128, -2, 3);
        let _ = MatPolyOverZ::sample_discrete_gauss(1, 3, 128, 4, 3);
        let _ = MatPolyOverZ::sample_discrete_gauss(3, 3, 128, 1.25f64, 3);
        let _ = MatPolyOverZ::sample_discrete_gauss(4, 3, 128, 15.75f32, 3);
    }

    /// Ensures that the resulting entries have correct degree.
    #[test]
    fn correct_degree_entries() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res = MatPolyOverZ::sample_discrete_gauss(1, 1, degree, i64::MAX, 1).unwrap();

            assert_eq!(
                res.get_entry(0, 0).unwrap().get_degree(),
                degree,
                "Could fail with negligible probability."
            );
        }
    }

    /// Checks whether the maximum degree needs to be at least 0.
    #[test]
    #[should_panic]
    fn invalid_max_degree() {
        let _ = MatPolyOverZ::sample_discrete_gauss(2, 2, -1, 0, 1).unwrap();
    }
}

#[cfg(test)]
mod test_sample_discrete_gauss_seeded {
    use crate::utils::sample::test_seed;
    use crate::{integer::MatPolyOverZ, traits::MatrixGetEntry};

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(2, 3, 128, 1u16, 2, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(1, 3, 128, 1u8, 2.0, test_seed());
        let _ =
            MatPolyOverZ::sample_discrete_gauss_seeded(2_i64, 3, 128, 1u32, 2.0_f64, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(2_i32, 3, 128, 1u64, 1, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(2_i16, 3, 128, 1i64, 3_u64, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(2_i8, 3, 128, 1i32, 1, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(2_u64, 3, 128, 1i16, 1, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(2_u32, 3, 128, 1i8, 1, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(2_u16, 3, 128, 1i64, 2, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(2_u8, 3, 128, -2, 3, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(1, 3, 128, 4, 3, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(3, 3, 128, 1.25f64, 3, test_seed());
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(4, 3, 128, 15.75f32, 3, test_seed());
    }

    /// Ensures that the resulting entries have correct degree.
    #[test]
    fn correct_degree_entries() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let res =
                MatPolyOverZ::sample_discrete_gauss_seeded(1, 1, degree, i64::MAX, 1, test_seed())
                    .unwrap();

            assert_eq!(
                res.get_entry(0, 0).unwrap().get_degree(),
                degree,
                "Could fail with negligible probability."
            );
        }
    }

    /// Checks whether the maximum degree needs to be at least 0.
    #[test]
    #[should_panic]
    fn invalid_max_degree() {
        let _ = MatPolyOverZ::sample_discrete_gauss_seeded(2, 2, -1, 0, 1, test_seed()).unwrap();
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer::MatPolyOverZ;
        let sample_0 =
            MatPolyOverZ::sample_discrete_gauss_seeded(3, 1, 5, 0, 1.25f32, [42; 32]).unwrap();
        let sample_1 =
            MatPolyOverZ::sample_discrete_gauss_seeded(3, 1, 5, 0, 1.25f32, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }
}

#[cfg(test)]
mod test_sample_d {
    use crate::{
        integer::{MatPolyOverZ, MatZ, Z},
        rational::{PolyOverQ, Q},
        traits::IntoCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the sample is from the base.
    #[test]
    fn ensure_sampled_from_base() {
        let base = MatPolyOverZ::from_str("[[1  1, 3  0 1 -1]]").unwrap();
        let center = vec![PolyOverQ::default()];

        for _ in 0..10 {
            let sample = MatPolyOverZ::sample_d(&base, 3, &center, 10.5_f64).unwrap();
            let sample_vec = sample.into_coefficient_embedding(3);
            let orthogonal = MatZ::from_str("[[0],[1],[1]]").unwrap();

            assert_eq!(Z::ZERO, sample_vec.dot_product(&orthogonal).unwrap());
        }
    }

    /// Ensure that the sample is from the base for higher dimensional bases.
    #[test]
    fn ensure_sampled_from_base_higher_dimension() {
        let base = MatPolyOverZ::from_str("[[1  1, 3  0 1 -1],[3  0 1 -1, 1  1],[0, 0]]").unwrap();
        let center = vec![
            PolyOverQ::default(),
            PolyOverQ::default(),
            PolyOverQ::default(),
        ];

        let orthogonal = MatZ::from_str("[[0, 1, 1, 0, 1, 1, 0 , 0, 0]]").unwrap();
        for _ in 0..10 {
            let sample = MatPolyOverZ::sample_d(&base, 3, &center, 10.5_f64).unwrap();
            let sample_embedded = sample.into_coefficient_embedding(3);

            assert_eq!(MatZ::new(1, 1), &orthogonal * &sample_embedded);
        }
    }

    /// Checks whether `sample_d` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let basis = MatPolyOverZ::from_str("[[1  1, 2  0 1, 3  0 0 1]]").unwrap();
        let center = vec![PolyOverQ::default()];
        let n = Z::from(1024);
        let s = Q::ONE;

        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 1u16);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 1u8);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 1u32);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 1u64);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 1i64);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 1i32);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 1i16);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 1i8);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 1i64);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, &n);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, &s);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 1.25f64);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &center, 15.75f32);
    }
}

#[cfg(test)]
mod test_sample_d_seeded {
    use crate::utils::sample::test_seed;
    use crate::{
        integer::{MatPolyOverZ, MatZ, Z},
        rational::{PolyOverQ, Q},
        traits::IntoCoefficientEmbedding,
    };
    use std::str::FromStr;

    /// Ensure that the sample is from the base.
    #[test]
    fn ensure_sampled_from_base() {
        let base = MatPolyOverZ::from_str("[[1  1, 3  0 1 -1]]").unwrap();
        let center = vec![PolyOverQ::default()];

        for _ in 0..10 {
            let sample =
                MatPolyOverZ::sample_d_seeded(&base, 3, &center, 10.5_f64, test_seed()).unwrap();
            let sample_vec = sample.into_coefficient_embedding(3);
            let orthogonal = MatZ::from_str("[[0],[1],[1]]").unwrap();

            assert_eq!(Z::ZERO, sample_vec.dot_product(&orthogonal).unwrap());
        }
    }

    /// Ensure that the sample is from the base for higher dimensional bases.
    #[test]
    fn ensure_sampled_from_base_higher_dimension() {
        let base = MatPolyOverZ::from_str("[[1  1, 3  0 1 -1],[3  0 1 -1, 1  1],[0, 0]]").unwrap();
        let center = vec![
            PolyOverQ::default(),
            PolyOverQ::default(),
            PolyOverQ::default(),
        ];

        let orthogonal = MatZ::from_str("[[0, 1, 1, 0, 1, 1, 0 , 0, 0]]").unwrap();
        for _ in 0..10 {
            let sample =
                MatPolyOverZ::sample_d_seeded(&base, 3, &center, 10.5_f64, test_seed()).unwrap();
            let sample_embedded = sample.into_coefficient_embedding(3);

            assert_eq!(MatZ::new(1, 1), &orthogonal * &sample_embedded);
        }
    }

    /// Checks whether `sample_d` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let basis = MatPolyOverZ::from_str("[[1  1, 2  0 1, 3  0 0 1]]").unwrap();
        let center = vec![PolyOverQ::default()];
        let n = Z::from(1024);
        let s = Q::ONE;

        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 1u16, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 1u8, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 1u32, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 1u64, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 1i64, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 1i32, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 1i16, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 1i8, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 1i64, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, &n, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, &s, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 1.25f64, test_seed());
        let _ = MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 15.75f32, test_seed());
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::{integer::MatPolyOverZ, rational::PolyOverQ};
        use std::str::FromStr;
        let basis = MatPolyOverZ::from_str("[[1  1, 3  0 1 -1, 2  2 2]]").unwrap();
        let center = vec![PolyOverQ::default()];
        let sample_0 =
            MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 10.5_f64, [42; 32]).unwrap();
        let sample_1 =
            MatPolyOverZ::sample_d_seeded(&basis, 3, &center, 10.5_f64, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }
}
