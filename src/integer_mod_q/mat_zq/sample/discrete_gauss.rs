// Copyright 2023 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the discrete Gaussian distribution.

use crate::{
    error::MathError,
    integer_mod_q::{MatZq, Modulus},
    macros::seeded::seedable_function,
    rational::{MatQ, Q},
    traits::{MatrixDimensions, MatrixSetEntry},
    utils::sample::discrete_gauss::{
        DiscreteGaussianIntegerSampler, LookupTableSetting, TAILCUT, sample_d,
        sample_d_precomputed_gso,
    },
};
use std::fmt::Display;

impl MatZq {
    seedable_function!(
        /// Initializes a new matrix with dimensions `num_rows` x `num_columns` and with each entry
        /// sampled independently according to the discrete Gaussian distribution,
        /// using [`Z::sample_discrete_gauss`](crate::integer::Z::sample_discrete_gauss).
        ///
        /// Parameters:
        /// - `num_rows`: specifies the number of rows the new matrix should have
        /// - `num_cols`: specifies the number of columns the new matrix should have
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
        /// Returns a matrix with each entry sampled independently from the
        /// specified discrete Gaussian distribution or an error if `s < 0`.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::integer_mod_q::MatZq;
        ///
        #[unseeded]
        /// let sample = MatZq::sample_discrete_gauss(3, 1, 83, 0, 1.25f32).unwrap();
        #[seeded]
        /// let sample = MatZq::sample_discrete_gauss_seeded(3, 1, 83, 0, 1.25f32, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `s < 0`.
        ///
        /// # Panics ...
        /// - if the provided number of rows and columns or the modulus are not suited to create a matrix.
        ///   For further information see [`MatZq::new`].
        /// - if the provided `modulus < 2`.
        pub(crate) fn sample_discrete_gauss(
            num_rows: impl TryInto<i64> + Display,
            num_cols: impl TryInto<i64> + Display,
            modulus: impl Into<Modulus>,
            center: impl Into<Q>,
            s: impl Into<Q>,
            seed: Option<[u8; 32]>,
        ) -> Result<MatZq, MathError> {
            let modulus: Modulus = modulus.into();
            let center: Q = center.into();
            let s: Q = s.into();
            let mut out = Self::new(num_rows, num_cols, &modulus);

            let mut dgis = DiscreteGaussianIntegerSampler::init(
                &center,
                &s,
                unsafe { TAILCUT },
                LookupTableSetting::FillOnTheFly,
                seed,
            )?;

            for row in 0..out.get_num_rows() {
                for col in 0..out.get_num_columns() {
                    let mut sample = dgis.sample_z();
                    sample = sample % &modulus;
                    unsafe { out.set_entry_unchecked(row, col, sample) };
                }
            }

            Ok(out)
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
        /// Returns a lattice vector sampled according to the discrete Gaussian distribution
        /// or an error if `s < 0`, the number of rows of the `basis` and `center` differ,
        /// or if `center` is not a column vector.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::{integer_mod_q::MatZq, rational::MatQ};
        /// let basis = MatZq::identity(5, 5, 17);
        /// let center = MatQ::new(5, 1);
        ///
        #[unseeded]
        /// let sample = MatZq::sample_d(&basis, &center, 1.25f32).unwrap();
        #[seeded]
        /// let sample = MatZq::sample_d_seeded(&basis, &center, 1.25f32, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `s < 0`.
        /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
        ///   if the number of rows of the `basis` and `center` differ.
        /// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
        ///   if `center` is not a column vector.
        ///
        /// This function implements SampleD according to:
        /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
        ///   Trapdoors for hard lattices and new cryptographic constructions.
        ///   In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
        ///   <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
        pub(crate) fn sample_d(
            basis: &MatZq,
            center: &MatQ,
            s: impl Into<Q>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let s: Q = s.into();

            let sample = sample_d(
                &basis.get_representative_least_nonnegative_residue(),
                center,
                &s,
                seed,
            )?;

            Ok(MatZq::from((&sample, basis.get_mod())))
        }
    );

    seedable_function!(
        /// SampleD samples a discrete Gaussian from the lattice with a provided `basis`.
        ///
        /// We do not check whether `basis` is actually a basis or whether `basis_gso` is
        /// actually the gso of `basis`. Hence, the callee is responsible for making sure
        /// that `basis` provides a suitable basis and `basis_gso` is a corresponding GSO.
        ///
        /// Parameters:
        /// - `basis`: specifies a basis for the lattice from which is sampled
        /// - `basis_gso`: specifies the precomputed gso for `basis`
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
        /// Returns a lattice vector sampled according to the discrete Gaussian distribution
        /// or an error if `s < 0`, the number of rows of the `basis` and `center` differ,
        /// or if `center` is not a column vector.
        ///
        /// # Examples
        /// ```
        /// use qfall_math::{integer_mod_q::MatZq, rational::MatQ};
        /// let basis = MatZq::identity(5, 5, 17);
        /// let center = MatQ::new(5, 1);
        /// let basis_gso = MatQ::from(&basis.get_representative_least_nonnegative_residue()).gso();
        ///
        #[unseeded]
        /// let sample = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1.25f32).unwrap();
        #[seeded]
        /// let sample = MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1.25f32, [42; 32]).unwrap();
        /// ```
        ///
        /// # Errors and Failures
        /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
        ///   if `s < 0`.
        /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
        ///   if the number of rows of the `basis` and `center` differ.
        /// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
        ///   if `center` is not a column vector.
        ///
        /// # Panics ...
        /// - if the number of rows/columns of `basis_gso` and `basis` mismatch.
        ///
        /// This function implements SampleD according to:
        /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
        ///   Trapdoors for hard lattices and new cryptographic constructions.
        ///   In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
        ///   <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
        pub(crate) fn sample_d_precomputed_gso(
            basis: &MatZq,
            basis_gso: &MatQ,
            center: &MatQ,
            s: impl Into<Q>,
            seed: Option<[u8; 32]>,
        ) -> Result<Self, MathError> {
            let s: Q = s.into();

            let sample = sample_d_precomputed_gso(
                &basis.get_representative_least_nonnegative_residue(),
                basis_gso,
                center,
                &s,
                seed,
            )?;

            Ok(MatZq::from((&sample, basis.get_mod())))
        }
    );
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::{
        integer::Z,
        integer_mod_q::{MatZq, Modulus},
        rational::Q,
        traits::MatrixGetEntry,
    };

    // This function only allows for a broader availability, which is tested here.

    /// Checks if entries are properly reduced.
    #[test]
    fn reduced() {
        let matrix = MatZq::sample_discrete_gauss(1, 1, 3, 0, 15.0).unwrap();
        let value: Z = matrix.get_entry(0, 0).unwrap();
        assert!(Z::ZERO <= value && value <= 3)
    }

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let n = Z::from(1024);
        let center = Q::ZERO;
        let s = Q::ONE;
        let modulus = Modulus::from(83);

        let _ = MatZq::sample_discrete_gauss(2u64, 3i8, &modulus, 0f32, 1u16);
        let _ = MatZq::sample_discrete_gauss(3u8, 2i16, 83u8, &center, 1u8);
        let _ = MatZq::sample_discrete_gauss(1, 1, &n, &center, 1u32);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83i8, &center, 1u64);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, &center, 1i64);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, &center, 1i32);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, &center, 1i16);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, &center, 1i8);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, &center, 1i64);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, &center, &n);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, &center, &s);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, &center, 1.25f64);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, 0, 1.25f64);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, center, 15.75f32);
    }
}

#[cfg(test)]
mod test_sample_discrete_gauss_seeded {
    use crate::utils::sample::test_seed;
    use crate::{
        integer::Z,
        integer_mod_q::{MatZq, Modulus},
        rational::Q,
        traits::MatrixGetEntry,
    };

    // This function only allows for a broader availability, which is tested here.

    /// Checks if entries are properly reduced.
    #[test]
    fn reduced() {
        let matrix = MatZq::sample_discrete_gauss_seeded(1, 1, 3, 0, 15.0, test_seed()).unwrap();
        let value: Z = matrix.get_entry(0, 0).unwrap();
        assert!(Z::ZERO <= value && value <= 3)
    }

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let n = Z::from(1024);
        let center = Q::ZERO;
        let s = Q::ONE;
        let modulus = Modulus::from(83);

        let _ = MatZq::sample_discrete_gauss_seeded(2u64, 3i8, &modulus, 0f32, 1u16, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(3u8, 2i16, 83u8, &center, 1u8, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, &n, &center, 1u32, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83i8, &center, 1u64, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83, &center, 1i64, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83, &center, 1i32, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83, &center, 1i16, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83, &center, 1i8, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83, &center, 1i64, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83, &center, &n, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83, &center, &s, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83, &center, 1.25f64, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83, 0, 1.25f64, test_seed());
        let _ = MatZq::sample_discrete_gauss_seeded(1, 1, 83, center, 15.75f32, test_seed());
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample() {
        use crate::integer_mod_q::MatZq;
        let sample_0 = MatZq::sample_discrete_gauss_seeded(3, 1, 83, 0, 1.25f32, [42; 32]).unwrap();
        let sample_1 = MatZq::sample_discrete_gauss_seeded(3, 1, 83, 0, 1.25f32, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }
}

#[cfg(test)]
mod test_sample_d {
    use crate::{
        integer::Z,
        integer_mod_q::MatZq,
        rational::{MatQ, Q},
    };

    // Appropriate inputs were tested in utils and thus omitted here.
    // This function only allows for a broader availability, which is tested here.

    /// Checks whether `sample_d` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let basis = MatZq::identity(5, 5, 17);
        let n = Z::from(1024);
        let center = MatQ::new(5, 1);
        let s = Q::ONE;

        let _ = MatZq::sample_d(&basis, &center, 1u16);
        let _ = MatZq::sample_d(&basis, &center, 1u8);
        let _ = MatZq::sample_d(&basis, &center, 1u32);
        let _ = MatZq::sample_d(&basis, &center, 1u64);
        let _ = MatZq::sample_d(&basis, &center, 1i64);
        let _ = MatZq::sample_d(&basis, &center, 1i32);
        let _ = MatZq::sample_d(&basis, &center, 1i16);
        let _ = MatZq::sample_d(&basis, &center, 1i8);
        let _ = MatZq::sample_d(&basis, &center, 1i64);
        let _ = MatZq::sample_d(&basis, &center, &n);
        let _ = MatZq::sample_d(&basis, &center, &s);
        let _ = MatZq::sample_d(&basis, &center, 1.25f64);
        let _ = MatZq::sample_d(&basis, &center, 15.75f32);
    }

    /// Checks whether `sample_d_precomputed_gso` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability_prec_gso() {
        let basis = MatZq::identity(5, 5, 17);
        let n = Z::from(1024);
        let center = MatQ::new(5, 1);
        let s = Q::ONE;
        let basis_gso = MatQ::from(&basis.get_representative_least_nonnegative_residue());

        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1u16);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1u8);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1u32);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1u64);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1i64);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1i32);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1i16);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1i8);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1i64);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, &n);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, &s);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 1.25f64);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &center, 15.75f32);
    }
}

#[cfg(test)]
mod test_sample_d_seeded {
    use crate::utils::sample::test_seed;
    use crate::{
        integer::Z,
        integer_mod_q::MatZq,
        rational::{MatQ, Q},
    };

    // Appropriate inputs were tested in utils and thus omitted here.
    // This function only allows for a broader availability, which is tested here.

    /// Checks whether `sample_d` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let basis = MatZq::identity(5, 5, 17);
        let n = Z::from(1024);
        let center = MatQ::new(5, 1);
        let s = Q::ONE;

        let _ = MatZq::sample_d_seeded(&basis, &center, 1u16, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, 1u8, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, 1u32, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, 1u64, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, 1i64, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, 1i32, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, 1i16, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, 1i8, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, 1i64, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, &n, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, &s, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, 1.25f64, test_seed());
        let _ = MatZq::sample_d_seeded(&basis, &center, 15.75f32, test_seed());
    }

    /// Checks whether `sample_d_precomputed_gso` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability_prec_gso() {
        let basis = MatZq::identity(5, 5, 17);
        let n = Z::from(1024);
        let center = MatQ::new(5, 1);
        let s = Q::ONE;
        let basis_gso = MatQ::from(&basis.get_representative_least_nonnegative_residue());

        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1u16, test_seed());
        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1u8, test_seed());
        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1u32, test_seed());
        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1u64, test_seed());
        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1i64, test_seed());
        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1i32, test_seed());
        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1i16, test_seed());
        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1i8, test_seed());
        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1i64, test_seed());
        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, &n, test_seed());
        let _ =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, &s, test_seed());
        let _ = MatZq::sample_d_precomputed_gso_seeded(
            &basis,
            &basis_gso,
            &center,
            1.25f64,
            test_seed(),
        );
        let _ = MatZq::sample_d_precomputed_gso_seeded(
            &basis,
            &basis_gso,
            &center,
            15.75f32,
            test_seed(),
        );
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample_d() {
        use crate::{integer_mod_q::MatZq, rational::MatQ};
        let basis = MatZq::identity(5, 5, 17);
        let center = MatQ::new(5, 1);
        let sample_0 = MatZq::sample_d_seeded(&basis, &center, 1.25f32, [42; 32]).unwrap();
        let sample_1 = MatZq::sample_d_seeded(&basis, &center, 1.25f32, [42; 32]).unwrap();

        assert_eq!(sample_0, sample_1);
    }

    /// Checks whether the same seed results in the same sample.
    #[test]
    fn same_seed_same_sample_d_precomputed_gso() {
        use crate::{integer_mod_q::MatZq, rational::MatQ};
        let basis = MatZq::identity(5, 5, 17);
        let center = MatQ::new(5, 1);
        let basis_gso = MatQ::from(&basis.get_representative_least_nonnegative_residue()).gso();
        let sample_0 =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1.25f32, [42; 32])
                .unwrap();
        let sample_1 =
            MatZq::sample_d_precomputed_gso_seeded(&basis, &basis_gso, &center, 1.25f32, [42; 32])
                .unwrap();

        assert_eq!(sample_0, sample_1);
    }
}
