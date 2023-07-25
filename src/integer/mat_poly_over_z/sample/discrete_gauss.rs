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
    integer::{MatPolyOverZ, MatZ, PolyOverZ, Z},
    rational::{PolyOverQ, Q},
    traits::{
        Concatenate, FromCoefficientEmbedding, GetNumRows, IntoCoefficientEmbedding, SetEntry,
    },
};

impl MatPolyOverZ {
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
    /// to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a vector of polynomials sampled according to the
    /// discrete Gaussian distribution.
    ///
    /// # Example
    /// ```
    /// use qfall_math::{
    ///     integer::MatPolyOverZ,
    ///     rational::PolyOverQ,
    /// };
    /// use std::str::FromStr;
    ///
    /// let base = MatPolyOverZ::from_str("[[1  1, 3  0 1 -1, 2  2 2]]").unwrap();
    /// let center = vec![PolyOverQ::default()];
    ///
    /// let sample = MatPolyOverZ::sample_d(&base, 3, 100, &center, 10.5_f64).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`VectorFunctionCalledOnNonVector`](MathError::VectorFunctionCalledOnNonVector), if the basis is not a row vector
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if the `n <= 1` or `s <= 0`.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of rows of the `basis` and `center` differ.
    ///
    /// This function implements SampleD according to:
    /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
    /// Trapdoors for hard lattices and new cryptographic constructions.
    /// In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
    /// <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
    ///
    /// # Panics ...
    /// - if the polynomials have higher length than the provided upper bound `k`
    pub fn sample_d(
        base: &Self,
        k: impl Into<i64>,
        n: impl Into<Z>,
        center: &[PolyOverQ],
        s: impl Into<Q>,
    ) -> Result<MatPolyOverZ, MathError> {
        let k = k.into();
        // use coefficient embedding and then call sampleD for the matrix representation
        let mut base_embedded = base.get_row(0).unwrap().into_coefficient_embedding(k);
        for row in 1..base.get_num_rows() {
            let b_row = base.get_row(row)?.into_coefficient_embedding(k);
            base_embedded = base_embedded.concat_vertical(&b_row)?;
        }

        // use coefficient embedding to get center
        let mut center_embedded = center[0].into_coefficient_embedding(k);
        for row in center.iter().skip(1) {
            let c_row = row.into_coefficient_embedding(k);
            center_embedded = center_embedded.concat_vertical(&c_row)?;
        }

        let sample = MatZ::sample_d(&base_embedded, n, &center_embedded, s)?;

        let mut out = MatPolyOverZ::new(base.get_num_rows(), 1);
        // convert sample back to a polynomial using the coefficient embedding
        for i in 0..base.get_num_rows() {
            let poly_i = PolyOverZ::from_coefficient_embedding(&sample.get_submatrix(
                i * k,
                (i + 1) * k - 1,
                0,
                0,
            )?);
            out.set_entry(i, 0, poly_i)?
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_sample_d {
    use crate::{
        integer::{MatPolyOverZ, MatZ, Z},
        rational::{PolyOverQ, Q},
        traits::{Concatenate, GetNumRows, IntoCoefficientEmbedding},
    };
    use std::str::FromStr;

    /// Ensure that the sample is from the base.
    #[test]
    fn ensure_sampled_from_base() {
        let base = MatPolyOverZ::from_str("[[1  1, 3  0 1 -1]]").unwrap();
        let center = vec![PolyOverQ::default()];

        for _ in 0..10 {
            let sample = MatPolyOverZ::sample_d(&base, 3, 100, &center, 10.5_f64).unwrap();
            let sample_vec = sample.into_coefficient_embedding(3);
            let orthogonal = MatZ::from_str("[[0],[1],[1]]").unwrap();

            assert_eq!(Z::ZERO, sample_vec.dot_product(&orthogonal).unwrap())
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

        let orthogonal = MatZ::from_str("[[0, 1, 1, 0, 1, 1, 0 ,0, 0]]").unwrap();
        for _ in 0..10 {
            let sample = MatPolyOverZ::sample_d(&base, 3, 100, &center, 10.5_f64).unwrap();
            let mut sample_embedded = sample.get_row(0).unwrap().into_coefficient_embedding(3);
            for row in 1..sample.get_num_rows() {
                let b_row = sample.get_row(row).unwrap().into_coefficient_embedding(3);
                sample_embedded = sample_embedded.concat_vertical(&b_row).unwrap();
            }

            assert_eq!(MatZ::new(1, 1), &orthogonal * &sample_embedded)
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

        let _ = MatPolyOverZ::sample_d(&basis, 3, 16u16, &center, 1u16);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2u32, &center, 1u8);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2u64, &center, 1u32);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2i8, &center, 1u64);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2i16, &center, 1i64);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2i32, &center, 1i32);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2i64, &center, 1i16);
        let _ = MatPolyOverZ::sample_d(&basis, 3, &n, &center, 1i8);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2u8, &center, 1i64);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2, &center, &n);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2, &center, &s);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2, &center, 1.25f64);
        let _ = MatPolyOverZ::sample_d(&basis, 3, 2, &center, 15.75f32);
    }
}
