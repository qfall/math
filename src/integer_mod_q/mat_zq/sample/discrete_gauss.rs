// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the discrete Gaussian distribution.

use crate::{
    error::MathError,
    integer::{MatZ, Z},
    integer_mod_q::{MatZq, Modulus},
    rational::{MatQ, Q},
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::sample::discrete_gauss::{sample_d, sample_d_precomputed_gso, sample_z},
};
use std::fmt::Display;

impl MatZq {
    /// Initializes a new matrix with dimensions `num_rows` x `num_columns` and with each entry
    /// sampled independently according to the discrete Gaussian distribution,
    /// using [`Z::sample_discrete_gauss`].
    ///
    /// Parameters:
    /// - `num_rows`: specifies the number of rows the new matrix should have
    /// - `num_cols`: specifies the number of columns the new matrix should have
    /// - `n`: specifies the range from which [`Z::sample_discrete_gauss`] samples
    /// - `center`: specifies the positions of the center with peak probability
    /// - `s`: specifies the Gaussian parameter, which is proportional
    /// to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a matrix with each entry sampled independently from the
    /// specified discrete Gaussian distribution.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let sample = MatZq::sample_discrete_gauss(3, 1, 83, 1024, 0, 1.25f32).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if the `n <= 1` or `s <= 0`.
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns or the modulus are not suited to create a matrix.
    /// For further information see [`MatZq::new`].
    pub fn sample_discrete_gauss(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: impl Into<Z>,
        n: impl Into<Z>,
        center: impl Into<Q>,
        s: impl Into<Q>,
    ) -> Result<MatZq, MathError> {
        let modulus: Z = modulus.into();
        let n: Z = n.into();
        let center: Q = center.into();
        let s: Q = s.into();
        let mut out = Self::new(num_rows, num_cols, modulus);

        for row in 0..out.get_num_rows() {
            for col in 0..out.get_num_columns() {
                let sample = sample_z(&n, &center, &s)?;
                out.set_entry(row, col, sample).unwrap();
            }
        }

        Ok(out)
    }

    /// SampleD samples a discrete Gaussian from the lattice with a provided `basis`.
    ///
    /// We do not check whether `basis` is actually a basis. Hence, the callee is
    /// responsible for making sure that `basis` provides a suitable basis.
    ///
    /// Parameters:
    /// - `basis`: specifies a basis for the lattice from which is sampled
    /// - `n`: specifies the range from which [`Z::sample_discrete_gauss`] samples
    /// - `center`: specifies the positions of the center with peak probability
    /// - `s`: specifies the Gaussian parameter, which is proportional
    /// to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a lattice vector sampled according to the discrete Gaussian distribution.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer_mod_q::MatZq, rational::MatQ};
    /// let basis = MatZq::identity(5, 5, 17);
    /// let center = MatQ::new(5, 1);
    ///
    /// let sample = MatZq::sample_d(&basis, 1024, &center, 1.25f32).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if the `n <= 1` or `s <= 0`.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of rows of the `basis` and `center` differ.
    /// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
    /// if `center` is not a column vector.
    ///
    /// This function implements SampleD according to:
    /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
    /// Trapdoors for hard lattices and new cryptographic constructions.
    /// In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
    /// <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
    pub fn sample_d(
        basis: &MatZq,
        n: impl Into<Z>,
        center: &MatQ,
        s: impl Into<Q>,
    ) -> Result<Self, MathError> {
        let n: Z = n.into();
        let s: Q = s.into();

        let sample = sample_d(&MatZ::from(basis), &n, center, &s)?;

        Ok(MatZq::from_mat_z_modulus(&sample, &basis.get_mod()))
    }

    /// Runs [`MatZq::sample_d`] with identity basis and center vector `0`.
    /// The full documentation can be found at [`MatZq::sample_d`].
    ///
    /// Parameters:
    /// - `dimension`: specifies the number of rows and columns
    /// that the identity basis should have
    /// - `modulus`: specifies the modulus of the new matrix
    /// - `n`: specifies the range from which
    /// [`Zq::sample_discrete_gauss`](crate::integer_mod_q::Zq::sample_discrete_gauss) samples
    /// - `s`: specifies the Gaussian parameter, which is proportional
    /// to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a lattice vector sampled according to the discrete Gaussian distribution.
    /// The lattice specified as `Z^m` for `m = dimension` and its center fixed to `0^m`.
    pub fn sample_d_common(
        dimension: impl TryInto<i64> + Display + Clone,
        modulus: impl Into<Modulus>,
        n: impl Into<Z>,
        s: impl Into<Q>,
    ) -> Result<Self, MathError> {
        let basis = MatZq::identity(dimension.clone(), dimension, modulus);
        let center = MatQ::new(basis.get_num_rows(), 1);

        Self::sample_d(&basis, n, &center, s)
    }

    /// SampleD samples a discrete Gaussian from the lattice with a provided `basis`.
    ///
    /// We do not check whether `basis` is actually a basis or whether `basis_gso` is
    /// actually the gso of `basis`. Hence, the callee is responsible for making sure
    /// that `basis` provides a suitable basis and `basis_gso` is a corresponding GSO.
    ///
    /// Parameters:
    /// - `basis`: specifies a basis for the lattice from which is sampled
    /// - `basis_gso`: specifies the precomputed gso for `basis`
    /// - `n`: specifies the range from which [`Z::sample_discrete_gauss`] samples
    /// - `center`: specifies the positions of the center with peak probability
    /// - `s`: specifies the Gaussian parameter, which is proportional
    /// to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a lattice vector sampled according to the discrete Gaussian distribution.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::MatZ, integer_mod_q::MatZq, rational::MatQ};
    /// let basis = MatZq::identity(5, 5, 17);
    /// let center = MatQ::new(5, 1);
    /// let basis_gso = MatQ::from(&MatZ::from(&basis)).gso();
    ///
    /// let sample = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 1024, &center, 1.25f32).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if the `n <= 1` or `s <= 0`.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of rows of the `basis` and `center` differ.
    /// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
    /// if `center` is not a column vector.
    ///
    /// # Panics ...
    /// - if the number of rows/columns of `basis_gso` and `basis` mismatch.
    ///
    /// This function implements SampleD according to:
    /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
    /// Trapdoors for hard lattices and new cryptographic constructions.
    /// In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
    /// <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
    pub fn sample_d_precomputed_gso(
        basis: &MatZq,
        basis_gso: &MatQ,
        n: impl Into<Z>,
        center: &MatQ,
        s: impl Into<Q>,
    ) -> Result<Self, MathError> {
        let n: Z = n.into();
        let s: Q = s.into();

        let sample = sample_d_precomputed_gso(&MatZ::from(basis), basis_gso, &n, center, &s)?;

        Ok(MatZq::from_mat_z_modulus(&sample, &basis.get_mod()))
    }
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::{
        integer::Z,
        integer_mod_q::{MatZq, Modulus},
        rational::Q,
    };

    // This function only allows for a broader availability, which is tested here.

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let n = Z::from(1024);
        let center = Q::ZERO;
        let s = Q::ONE;
        let modulus = Modulus::from(83);

        let _ = MatZq::sample_discrete_gauss(2u64, 3i8, &modulus, 16u16, 0f32, 1u16);
        let _ = MatZq::sample_discrete_gauss(3u8, 2i16, 83u8, 2u32, &center, 1u8);
        let _ = MatZq::sample_discrete_gauss(1, 1, &n, 2u64, &center, 1u32);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83i8, 2i8, &center, 1u64);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, 2i16, &center, 1i64);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, 2i32, &center, 1i32);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, 2i64, &center, 1i16);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, &n, &center, 1i8);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, 2u8, &center, 1i64);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, 2, &center, &n);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, 2, &center, &s);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, 2, &center, 1.25f64);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, 2, 0, 1.25f64);
        let _ = MatZq::sample_discrete_gauss(1, 1, 83, 2, center, 15.75f32);
    }
}

#[cfg(test)]
mod test_sample_d {
    use crate::{
        integer::{MatZ, Z},
        integer_mod_q::{MatZq, Modulus},
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

        let _ = MatZq::sample_d(&basis, 16u16, &center, 1u16);
        let _ = MatZq::sample_d(&basis, 2u32, &center, 1u8);
        let _ = MatZq::sample_d(&basis, 2u64, &center, 1u32);
        let _ = MatZq::sample_d(&basis, 2i8, &center, 1u64);
        let _ = MatZq::sample_d(&basis, 2i16, &center, 1i64);
        let _ = MatZq::sample_d(&basis, 2i32, &center, 1i32);
        let _ = MatZq::sample_d(&basis, 2i64, &center, 1i16);
        let _ = MatZq::sample_d(&basis, &n, &center, 1i8);
        let _ = MatZq::sample_d(&basis, 2u8, &center, 1i64);
        let _ = MatZq::sample_d(&basis, 2, &center, &n);
        let _ = MatZq::sample_d(&basis, 2, &center, &s);
        let _ = MatZq::sample_d(&basis, 2, &center, 1.25f64);
        let _ = MatZq::sample_d(&basis, 2, &center, 15.75f32);
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
        let basis_gso = MatQ::from(&MatZ::from(&basis));

        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 16u16, &center, 1u16);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2u32, &center, 1u8);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2u64, &center, 1u32);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2i8, &center, 1u64);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2i16, &center, 1i64);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2i32, &center, 1i32);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2i64, &center, 1i16);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, &n, &center, 1i8);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2u8, &center, 1i64);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2, &center, &n);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2, &center, &s);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2, &center, 1.25f64);
        let _ = MatZq::sample_d_precomputed_gso(&basis, &basis_gso, 2, &center, 15.75f32);
    }

    // As `sample_d_common` just calls `MatZq::sample_d` with identity basis
    // and center 0, further tests are omitted.

    /// Ensures that `sample_d_common` works properly.
    #[test]
    fn common() {
        let modulus = Modulus::from(17);

        let _ = MatZq::sample_d_common(10, &modulus, 1024, 1.25f32).unwrap();
    }
}
