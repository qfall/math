// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the discrete Gaussian distribution.

use crate::{
    error::MathError,
    integer::{MatPolyOverZ, Z},
    integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    rational::{PolyOverQ, Q},
};
use std::fmt::Display;

impl MatPolynomialRingZq {
    /// Initializes a new matrix with dimensions `num_rows` x `num_columns` and with each entry
    /// sampled independently according to the discrete Gaussian distribution,
    /// using [`PolynomialRingZq::sample_discrete_gauss`](crate::integer_mod_q::PolynomialRingZq::sample_discrete_gauss).
    ///
    /// Parameters:
    /// - `num_rows`: specifies the number of rows the new matrix should have
    /// - `num_cols`: specifies the number of columns the new matrix should have
    /// - `modulus`: specifies the Modulus for the matrix and the maximum degree
    ///   any discrete Gaussian polynomial can have
    /// - `n`: specifies the range from which [`Z::sample_discrete_gauss`] samples
    /// - `center`: specifies the positions of the center with peak probability
    /// - `s`: specifies the Gaussian parameter, which is proportional
    ///   to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a [`MatPolynomialRingZq`] with each entry sampled independently from the
    /// specified discrete Gaussian distribution or an error if `n <= 1` or `s <= 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    ///
    /// let matrix = MatPolynomialRingZq::sample_discrete_gauss(3, 1, &modulus, 128, 0, 1.25f32).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///   if `n <= 1` or `s <= 0`.
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    ///   For further information see [`MatPolynomialRingZq::new`].
    /// - if `modulus` is not a valid choice for a [`ModulusPolynomialRingZq`], see
    ///   [`ModulusPolynomialRingZq::from`] for further information.
    pub fn sample_discrete_gauss(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: impl Into<ModulusPolynomialRingZq>,
        n: impl Into<Z>,
        center: impl Into<Q>,
        s: impl Into<Q>,
    ) -> Result<MatPolynomialRingZq, MathError> {
        let modulus: ModulusPolynomialRingZq = modulus.into();
        let sample = MatPolyOverZ::sample_discrete_gauss(
            num_rows,
            num_cols,
            modulus.get_degree() - 1,
            n,
            center,
            s,
        )?;
        Ok(MatPolynomialRingZq::from((&sample, modulus)))
    }

    /// SampleD samples a discrete Gaussian from the lattice with a provided `basis`.
    ///
    /// We do not check whether `basis` is actually a basis. Hence, the callee is
    /// responsible for making sure that `basis` provides a suitable basis.
    ///
    /// Parameters:
    /// - `basis`: specifies a basis for the lattice from which is sampled
    /// - `k`: the maximal length the polynomial can have
    /// - `n`: specifies the range from which [`Z::sample_discrete_gauss`] samples
    /// - `center`: specifies the positions of the center with peak probability
    /// - `s`: specifies the Gaussian parameter, which is proportional
    ///   to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a vector of polynomials sampled according to the
    /// discrete Gaussian distribution or an error if the basis is not a row vector,
    /// `n <= 1` or `s <= 0`, or the number of rows of the `basis` and `center` differ.
    ///
    /// # Example
    /// ```
    /// use qfall_math::{
    ///     integer::{MatPolyOverZ, Z},
    ///     integer_mod_q::{
    ///         MatPolynomialRingZq,
    ///         ModulusPolynomialRingZq,
    ///     },
    ///     rational::{PolyOverQ, Q},
    /// };
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[1  1, 3  0 0 1, 2  0 1]]").unwrap();
    /// let basis = MatPolynomialRingZq::from((&poly_mat, &modulus));
    /// let center = vec![PolyOverQ::default()];
    /// let n = Z::from(1024);
    /// let s = Q::from(8);
    ///
    /// let sample = MatPolynomialRingZq::sample_d(&basis, 3, 16, &center, s);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`VectorFunctionCalledOnNonVector`](MathError::VectorFunctionCalledOnNonVector), if the basis is not a row vector
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///   if `n <= 1` or `s <= 0`.
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
    pub fn sample_d(
        basis: &Self,
        k: impl Into<i64>,
        n: impl Into<Z>,
        center: &[PolyOverQ],
        s: impl Into<Q>,
    ) -> Result<MatPolynomialRingZq, MathError> {
        let sample = MatPolyOverZ::sample_d(&basis.matrix, k, n, center, s)?;
        Ok(MatPolynomialRingZq::from((&sample, &basis.get_mod())))
    }
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, MatZq, ModulusPolynomialRingZq},
        traits::{FromCoefficientEmbedding, MatrixGetEntry, MatrixSetEntry},
    };

    /// Ensures that the resulting entries have correct degree.
    #[test]
    fn correct_degree_entries() {
        let degrees = [1, 2, 3, 7, 15, 32, 120];
        for degree in degrees {
            let mut coeff_emb_mod = MatZq::new(degree + 1, 1, i64::MAX);
            coeff_emb_mod.set_entry(0, 0, 1).unwrap();
            coeff_emb_mod.set_entry(degree, 0, 1).unwrap();
            let modulus = ModulusPolynomialRingZq::from_coefficient_embedding(&coeff_emb_mod);
            let res = MatPolynomialRingZq::sample_discrete_gauss(1, 1, modulus, 1024, i32::MAX, 1)
                .unwrap();

            let entry: PolyOverZ = res.get_entry(0, 0).unwrap();
            assert_eq!(
                entry.get_degree(),
                degree - 1,
                "Could fail with negligible probability."
            );
        }
    }
}

#[cfg(test)]
mod test_sample_d {
    use crate::{
        integer::{MatPolyOverZ, PolyOverZ, Z},
        integer_mod_q::{MatPolynomialRingZq, MatZq, ModulusPolynomialRingZq, Zq},
        rational::{PolyOverQ, Q},
        traits::{IntoCoefficientEmbedding, MatrixGetEntry},
    };
    use std::str::FromStr;

    /// Ensure that the sample is from the base.
    #[test]
    fn ensure_sampled_from_base() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[1  1, 3  0 1 -1]]").unwrap();
        let base = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let center = vec![PolyOverQ::default()];

        for _ in 0..10 {
            let sample = MatPolynomialRingZq::sample_d(&base, 3, 100, &center, 20.5_f64).unwrap();
            let sample: PolyOverZ = sample.get_entry(0, 0).unwrap();
            let sample_vec = MatZq::from((&sample.into_coefficient_embedding(3), 17));
            let orthogonal = MatZq::from_str("[[0],[1],[1]] mod 17").unwrap();

            assert_eq!(
                Zq::from((0, 17)),
                sample_vec.dot_product(&orthogonal).unwrap()
            )
        }
    }

    /// Checks whether `sample_d` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// or [`Into<Q>`], i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[1  1, 3  0 0 1, 2  0 1]]").unwrap();
        let basis = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let center = vec![PolyOverQ::default()];
        let n = Z::from(1024);
        let s = Q::from(8);

        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 16u16, &center, 1u16);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2u32, &center, 1u8);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2u64, &center, 1u32);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2i8, &center, 1u64);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2i16, &center, 1i64);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2i32, &center, 1i32);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2i64, &center, 1i16);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, &n, &center, 1i8);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2u8, &center, 1i64);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2, &center, &n);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2, &center, &s);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2, &center, 1.25f64);
        let _ = MatPolynomialRingZq::sample_d(&basis, 3, 2, &center, 15.75f32);
    }
}
