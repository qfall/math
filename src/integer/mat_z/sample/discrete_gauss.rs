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
    rational::{MatQ, Q},
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::sample::discrete_gauss::{sample_d, sample_d_precomputed_gso, sample_z},
};
use std::fmt::Display;

impl MatZ {
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
    ///     to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a matrix with each entry sampled independently from the
    /// specified discrete Gaussian distribution.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let sample = MatZ::sample_discrete_gauss(3, 1, 1024, 0, 1.25f32).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///     if the `n <= 1` or `s <= 0`.
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    ///     For further information see [`MatZ::new`].
    pub fn sample_discrete_gauss(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        n: impl Into<Z>,
        center: impl Into<Q>,
        s: impl Into<Q>,
    ) -> Result<MatZ, MathError> {
        let mut out = Self::new(num_rows, num_cols);
        let n: Z = n.into();
        let center: Q = center.into();
        let s: Q = s.into();

        for row in 0..out.get_num_rows() {
            for col in 0..out.get_num_columns() {
                let sample = sample_z(&n, &center, &s)?;
                out.set_entry(row, col, sample)?;
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
    ///     to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a lattice vector sampled according to the discrete Gaussian distribution.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::{MatZ, Z}, rational::{MatQ, Q}};
    /// let basis = MatZ::identity(5, 5);
    /// let center = MatQ::new(5, 1);
    ///
    /// let sample = MatZ::sample_d(&basis, 1024, &center, 1.25f32).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///     if the `n <= 1` or `s <= 0`.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    ///     if the number of rows of the `basis` and `center` differ.
    /// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
    ///     if `center` is not a column vector.
    ///
    /// This function implements SampleD according to:
    /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
    ///     Trapdoors for hard lattices and new cryptographic constructions.
    ///     In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
    ///     <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
    pub fn sample_d(
        basis: &MatZ,
        n: impl Into<Z>,
        center: &MatQ,
        s: impl Into<Q>,
    ) -> Result<Self, MathError> {
        let n: Z = n.into();
        let s: Q = s.into();

        sample_d(basis, &n, center, &s)
    }

    /// Runs [`MatZ::sample_d`] with identity basis and center vector `0`.
    /// The full documentation can be found at [`MatZ::sample_d`].
    ///
    /// Parameters:
    /// - `dimension`: specifies the number of rows and columns
    ///     that the identity basis should have
    /// - `n`: specifies the range from which [`Z::sample_discrete_gauss`] samples
    /// - `s`: specifies the Gaussian parameter, which is proportional
    ///     to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a lattice vector sampled according to the discrete Gaussian distribution.
    /// The lattice specified as `Z^m` for `m = dimension` and its center fixed to `0^m`.
    ///
    /// # Panics ...
    /// - if the provided `dimension` is not suited to create a matrix.
    ///     For further information see [`MatZ::new`].
    pub fn sample_d_common(
        dimension: impl TryInto<i64> + Display + Clone,
        n: impl Into<Z>,
        s: impl Into<Q>,
    ) -> Result<Self, MathError> {
        let basis = MatZ::identity(dimension.clone(), dimension);
        let center = MatQ::new(basis.get_num_rows(), 1);

        MatZ::sample_d(&basis, n, &center, s)
    }

    /// Samples a (possibly) non-spherical discrete Gaussian using
    /// the standard basis and center `0`.
    ///
    /// Parameters:
    /// - `n`: specifies the range from which [`MatQ::randomized_rounding`] samples
    /// - `sigma_`: specifies the positive definite Gaussian convolution matrix
    ///     with which the *intermediate* continuous Gaussian is sampled before
    ///     the randomized rounding is applied. Here `sigma_ = sqrt(sigma^2 - r^2*I)`
    ///     where sigma is the target convolution matrix. The root can be computed using
    ///     the [`MatQ::cholesky_decomposition`].
    /// - `r`: specifies the rounding parameter for [`MatQ::randomized_rounding`].
    ///
    /// Returns a lattice vector sampled according to the discrete Gaussian distribution.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::rational::{Q, MatQ};
    /// use std::str::FromStr;
    /// use crate::qfall_math::traits::Pow;
    ///
    /// let convolution_matrix = MatQ::from_str("[[100,1],[1,17]]").unwrap();
    /// let r = Q::from(4);
    ///
    /// let sigma_ = convolution_matrix - r.pow(2).unwrap() * MatQ::identity(2, 2);
    ///
    /// let sample = MatZ::sample_d_common_non_spherical(16, &sigma_.cholesky_decomposition(), r).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///     if the `n <= 1` or `r <= 0`.
    ///
    /// # Panics ...
    /// - if `sigma_` is not a square matrix.
    ///
    /// This function implements SampleD according to Algorithm 1. in \[2\].
    /// - \[2\] Peikert, Chris.
    ///     "An efficient and parallel Gaussian sampler for lattices.
    ///     In Annual Cryptology Conference, pp. 80-97. Berlin, Heidelberg: Springer
    ///     Berlin Heidelberg, 2010.
    ///     <https://link.springer.com/chapter/10.1007/978-3-642-14623-7_5>
    pub fn sample_d_common_non_spherical(
        n: impl Into<Z>,
        sigma_: &MatQ,
        r: impl Into<Q>,
    ) -> Result<Self, MathError> {
        assert!(sigma_.is_square());
        let r = r.into();

        // sample a continuous Gaussian centered around `0` in every dimension with
        // gaussian parameter `1`.
        let d_1 = MatQ::sample_gauss_same_center(sigma_.get_num_columns(), 1, 0, 1)?;

        // compute a continuous Gaussian centered around `0` in every dimension with
        // convolution matrix `b_2` (the cholesky decomposition we computed)
        let x_2 = sigma_ * d_1;

        // perform randomized rounding
        x_2.randomized_rounding(r, n)
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
    ///     to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a lattice vector sampled according to the discrete Gaussian distribution.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::{MatZ, Z}, rational::{MatQ, Q}};
    /// let basis = MatZ::identity(5, 5);
    /// let center = MatQ::new(5, 1);
    /// let basis_gso = MatQ::from(&basis).gso();
    ///
    /// let sample = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 1024, &center, 1.25f32).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///     if the `n <= 1` or `s <= 0`.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    ///     if the number of rows of the `basis` and `center` differ.
    /// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
    ///     if `center` is not a column vector.
    ///
    /// # Panics ...
    /// - if the number of rows/columns of `basis_gso` and `basis` mismatch.
    ///
    /// This function implements SampleD according to:
    /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
    ///     Trapdoors for hard lattices and new cryptographic constructions.
    ///     In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
    ///     <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
    pub fn sample_d_precomputed_gso(
        basis: &MatZ,
        basis_gso: &MatQ,
        n: impl Into<Z>,
        center: &MatQ,
        s: impl Into<Q>,
    ) -> Result<Self, MathError> {
        let n: Z = n.into();
        let s: Q = s.into();

        sample_d_precomputed_gso(basis, basis_gso, &n, center, &s)
    }
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::{
        integer::{MatZ, Z},
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

        let _ = MatZ::sample_discrete_gauss(2u64, 3i8, 16u16, &center, 1u16);
        let _ = MatZ::sample_discrete_gauss(3u8, 2i16, 200u32, &center, 1u8);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200u64, &center, 1u32);
        let _ = MatZ::sample_discrete_gauss(1, 1, 40i8, &center, 1u64);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200i16, &center, 1i64);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200i32, &center, 1i32);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200i64, &center, 1i16);
        let _ = MatZ::sample_discrete_gauss(1, 1, &n, &center, 1i8);
        let _ = MatZ::sample_discrete_gauss(1, 1, 2u8, &center, 1i64);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200, &center, &n);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200, &center, &s);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200, 1, &s);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200, 2.25, &s);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200, &center, 1.25f64);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200, &center, 15.75f32);
    }
}

#[cfg(test)]
mod test_sample_d {
    use crate::{
        integer::{MatZ, Z},
        rational::{MatQ, Q},
    };

    // Appropriate inputs were tested in utils and thus omitted here.
    // This function only allows for a broader availability, which is tested here.

    /// Checks whether `sample_d` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let basis = MatZ::identity(5, 5);
        let n = Z::from(1024);
        let center = MatQ::new(5, 1);
        let s = Q::ONE;

        let _ = MatZ::sample_d(&basis, 16u16, &center, 1u16);
        let _ = MatZ::sample_d(&basis, 2u32, &center, 1u8);
        let _ = MatZ::sample_d(&basis, 2u64, &center, 1u32);
        let _ = MatZ::sample_d(&basis, 2i8, &center, 1u64);
        let _ = MatZ::sample_d(&basis, 2i16, &center, 1i64);
        let _ = MatZ::sample_d(&basis, 2i32, &center, 1i32);
        let _ = MatZ::sample_d(&basis, 2i64, &center, 1i16);
        let _ = MatZ::sample_d(&basis, &n, &center, 1i8);
        let _ = MatZ::sample_d(&basis, 2u8, &center, 1i64);
        let _ = MatZ::sample_d(&basis, 2, &center, &n);
        let _ = MatZ::sample_d(&basis, 2, &center, &s);
        let _ = MatZ::sample_d(&basis, 2, &center, 1.25f64);
        let _ = MatZ::sample_d(&basis, 2, &center, 15.75f32);
    }

    /// Checks whether `sample_d_precomputed_gso` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability_prec_gso() {
        let basis = MatZ::identity(5, 5);
        let n = Z::from(1024);
        let center = MatQ::new(5, 1);
        let s = Q::ONE;
        let basis_gso = MatQ::from(&basis);

        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 16u16, &center, 1u16);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2u32, &center, 1u8);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2u64, &center, 1u32);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2i8, &center, 1u64);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2i16, &center, 1i64);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2i32, &center, 1i32);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2i64, &center, 1i16);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, &n, &center, 1i8);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2u8, &center, 1i64);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2, &center, &n);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2, &center, &s);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2, &center, 1.25f64);
        let _ = MatZ::sample_d_precomputed_gso(&basis, &basis_gso, 2, &center, 15.75f32);
    }

    // As `sample_d_common` just calls `MatZ::sample_d` with identity basis
    // and center 0, further tests are omitted.

    /// Ensures that `sample_d_common` works properly.
    #[test]
    fn common() {
        let _ = MatZ::sample_d_common(10, 1024, 1.25f32).unwrap();
    }
}

#[cfg(test)]
mod test_sample_d_common_non_spherical {
    use crate::{
        integer::{MatZ, Z},
        rational::{MatQ, Q},
        traits::{GetNumRows, Pow},
    };
    use std::str::FromStr;

    /// Checks whether `sample_d_common_non_spherical` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    /// or [`Into<MatQ>`], i.e. MatQ, MatZ
    #[test]
    fn availability() {
        let r = Q::from(8);
        let convolution_matrix = MatQ::from_str("[[100,1],[1,65]]").unwrap();
        let convolution_matrix = (convolution_matrix - r.pow(2).unwrap() * MatQ::identity(2, 2))
            .cholesky_decomposition();

        let _ = MatZ::sample_d_common_non_spherical(16, &convolution_matrix, 8).unwrap();

        let _ = MatZ::sample_d_common_non_spherical(16u16, &convolution_matrix, 8_u16).unwrap();
        let _ = MatZ::sample_d_common_non_spherical(16u32, &convolution_matrix, 8_u32).unwrap();
        let _ = MatZ::sample_d_common_non_spherical(16u64, &convolution_matrix, 8_u64).unwrap();
        let _ = MatZ::sample_d_common_non_spherical(16i8, &convolution_matrix, 8_i8).unwrap();
        let _ = MatZ::sample_d_common_non_spherical(16i16, &convolution_matrix, 8_i16).unwrap();
        let _ = MatZ::sample_d_common_non_spherical(16i32, &convolution_matrix, 8_i32).unwrap();
        let _ = MatZ::sample_d_common_non_spherical(16i64, &convolution_matrix, 8_i64).unwrap();
        let _ = MatZ::sample_d_common_non_spherical(Z::from(16), &convolution_matrix, Q::from(8))
            .unwrap();
        let _ = MatZ::sample_d_common_non_spherical(16, &convolution_matrix, Z::from(8)).unwrap();
        let _ = MatZ::sample_d_common_non_spherical(16, &convolution_matrix, 8f32).unwrap();
        let _ = MatZ::sample_d_common_non_spherical(16, &convolution_matrix, 8f64).unwrap();
    }

    /// Checks whether the function panics if a non positive-definite matrix is provided.
    #[test]
    #[should_panic]
    fn no_convolution_matrix_1() {
        let r = Q::from(4);
        let convolution_matrix = MatQ::from_str("[[-1,1],[1,1]]").unwrap();
        let convolution_matrix = (convolution_matrix - r.pow(2).unwrap() * MatQ::identity(2, 2))
            .cholesky_decomposition();

        let _ = MatZ::sample_d_common_non_spherical(16, &convolution_matrix, r).unwrap();
    }

    /// Checks whether the function panics if a non-square matrix is provided.
    /// anymore
    #[test]
    #[should_panic]
    fn not_square() {
        let convolution_matrix = MatQ::from_str("[[100,1,1],[1,64,2]]").unwrap();

        let _ = MatZ::sample_d_common_non_spherical(16, &convolution_matrix, 8).unwrap();
    }

    /// Checks whether the function returns an error if `n` or `r` is too small.
    #[test]
    fn too_small_parameters() {
        let convolution_matrix = MatQ::from_str("[[100, 1],[1, 65]]").unwrap();

        assert!(MatZ::sample_d_common_non_spherical(16, &convolution_matrix, 0).is_err());
        assert!(MatZ::sample_d_common_non_spherical(16, &convolution_matrix, -1).is_err());
        assert!(MatZ::sample_d_common_non_spherical(1, &convolution_matrix, 8).is_err());
        assert!(MatZ::sample_d_common_non_spherical(-1, &convolution_matrix, 8).is_err());
    }

    /// Checks whether the dimension of the output matches the provided convolution matrix
    #[test]
    fn correct_dimensions() {
        let convolution_matrix_1 = MatQ::from_str("[[100,1],[1,65]]").unwrap();
        let convolution_matrix_2 = MatQ::from_str("[[100,1,0],[1,65,0],[0,0,10000]]").unwrap();

        let sample_1 = MatZ::sample_d_common_non_spherical(16, &convolution_matrix_1, 8).unwrap();
        let sample_2 = MatZ::sample_d_common_non_spherical(16, &convolution_matrix_2, 8).unwrap();

        assert_eq!(2, sample_1.get_num_rows());
        assert!(sample_1.is_column_vector());
        assert_eq!(3, sample_2.get_num_rows());
        assert!(sample_2.is_column_vector());
    }
}
