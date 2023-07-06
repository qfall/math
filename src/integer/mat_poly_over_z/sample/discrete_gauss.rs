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
    traits::{FromCoefficientEmbedding, IntoCoefficientEmbedding},
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
    /// Returns a polynomial sampled according to the discrete Gaussian distribution.
    ///
    /// # Example
    /// ```
    /// todo!()
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
        basis: &Self,
        k: impl Into<i64>,
        n: impl Into<Z>,
        center: &PolyOverQ,
        s: impl Into<Q>,
    ) -> Result<PolyOverZ, MathError> {
        let k = k.into();
        // use coefficient embedding and then call sampleD for the matrix representation
        let basis = basis.into_coefficient_embedding(k);
        let center = center.into_coefficient_embedding(k);
        let sample = MatZ::sample_d(&basis, n, &center, s)?;

        // convert sample back to a polynomial using the coefficient embedding
        Ok(PolyOverZ::from_coefficient_embedding(&sample))
    }
}
