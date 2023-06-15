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
    utils::sample::discrete_gauss::{sample_d, sample_z},
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
    /// to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a matrix with each entry sampled independently from the
    /// specified discrete Gaussian distribution.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let sample = MatZ::sample_discrete_gauss(3, 1, 1024, 0, 1.25f32).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if the `n <= 1` or `s <= 0`.
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    /// For further information see [`MatZ::new`].
    pub fn sample_discrete_gauss<T1, T2, T3>(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        n: T1,
        center: T2,
        s: T3,
    ) -> Result<MatZ, MathError>
    where
        T1: Into<Z>,
        T2: Into<Q>,
        T3: Into<Q>,
    {
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
    /// to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a vector with discrete gaussian error based on a lattice point.
    ///
    /// # Example
    /// ```
    /// use qfall_math::{integer::{MatZ, Z}, rational::{MatQ, Q}};
    /// let basis = MatZ::identity(5, 5);
    /// let center = MatQ::new(5, 1).unwrap();
    ///
    /// let sample = MatZ::sample_d(&basis, 1024, &center, 1.25f32).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if the `n <= 1` or `s <= 0`.
    /// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
    /// if the number of rows of the `basis` and `center` differ.
    /// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
    /// if `center` is not a column vector.
    ///
    /// This function implements SampleD according to:
    /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
    /// Trapdoors for hard lattices and new cryptographic constructions.
    /// In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
    /// <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
    pub fn sample_d<T1, T2>(basis: &MatZ, n: T1, center: &MatQ, s: T2) -> Result<Self, MathError>
    where
        T1: Into<Z>,
        T2: Into<Q>,
    {
        let n: Z = n.into();
        let s: Q = s.into();

        sample_d(basis, &n, center, &s)
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
    /// implementing Into<Z>, i.e. u8, u16, u32, u64, i8, ...
    /// or Into<Q>, i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let n = Z::from(1024);
        let center = Q::from(0);
        let s = Q::ONE;

        let _ = MatZ::sample_discrete_gauss(2u64, 3i8, &16u16, &center, &1u16);
        let _ = MatZ::sample_discrete_gauss(3u8, 2i16, &200u32, &center, &1u8);
        let _ = MatZ::sample_discrete_gauss(1, 1, &200u64, &center, 1u32);
        let _ = MatZ::sample_discrete_gauss(1, 1, &40i8, &center, &1u64);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200i16, &center, &1i64);
        let _ = MatZ::sample_discrete_gauss(1, 1, &200i32, &center, &1i32);
        let _ = MatZ::sample_discrete_gauss(1, 1, &200i64, &center, &1i16);
        let _ = MatZ::sample_discrete_gauss(1, 1, &n, &center, &1i8);
        let _ = MatZ::sample_discrete_gauss(1, 1, 2u8, &center, &1i64);
        let _ = MatZ::sample_discrete_gauss(1, 1, &200, &center, &n);
        let _ = MatZ::sample_discrete_gauss(1, 1, 200, &center, &s);
        let _ = MatZ::sample_discrete_gauss(1, 1, &200, &1, &s);
        let _ = MatZ::sample_discrete_gauss(1, 1, &200, 2.25, &s);
        let _ = MatZ::sample_discrete_gauss(1, 1, &200, &center, 1.25f64);
        let _ = MatZ::sample_discrete_gauss(1, 1, &200, &center, 15.75f32);
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
    /// implementing Into<Z>, i.e. u8, u16, u32, u64, i8, ...
    /// or Into<Q>, i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let basis = MatZ::identity(5, 5);
        let n = Z::from(1024);
        let center = MatQ::new(5, 1).unwrap();
        let s = Q::ONE;

        let _ = MatZ::sample_d(&basis, &16u16, &center, &1u16);
        let _ = MatZ::sample_d(&basis, &2u32, &center, &1u8);
        let _ = MatZ::sample_d(&basis, &2u64, &center, &1u32);
        let _ = MatZ::sample_d(&basis, &2i8, &center, &1u64);
        let _ = MatZ::sample_d(&basis, &2i16, &center, &1i64);
        let _ = MatZ::sample_d(&basis, &2i32, &center, &1i32);
        let _ = MatZ::sample_d(&basis, &2i64, &center, &1i16);
        let _ = MatZ::sample_d(&basis, &n, &center, &1i8);
        let _ = MatZ::sample_d(&basis, &2u8, &center, &1i64);
        let _ = MatZ::sample_d(&basis, &2, &center, &n);
        let _ = MatZ::sample_d(&basis, &2, &center, &s);
        let _ = MatZ::sample_d(&basis, &2, &center, 1.25f64);
        let _ = MatZ::sample_d(&basis, &2, &center, 15.75f32);
    }
}
