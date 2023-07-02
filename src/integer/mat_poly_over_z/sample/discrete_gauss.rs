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
    rational::{MatQ, PolyOverQ, Q},
    traits::{GetCoefficient, GetEntry, GetNumColumns, GetNumRows, SetCoefficient, SetEntry},
    utils::sample::discrete_gauss::sample_d,
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
    pub fn sample_d(
        basis: &Self,
        k: i64,
        n: impl Into<Z>,
        center: &PolyOverQ,
        s: impl Into<Q>,
    ) -> Result<PolyOverZ, MathError> {
        let n: Z = n.into();
        let s: Q = s.into();

        let basis = polyz_vector_to_matz(basis, k)?;
        let center = polyq_to_matq_vector(center, k)?;

        let sample = sample_d(&basis, &n, &center, &s)?;

        matz_vector_to_polyz(&sample)
    }
}

fn polyz_vector_to_matz(poly_vec: &MatPolyOverZ, k: i64) -> Result<MatZ, MathError> {
    if !poly_vec.is_row_vector() {
        return Err(MathError::VectorFunctionCalledOnNonVector(
            String::from("polyz_vector_to_matz"),
            poly_vec.get_num_rows(),
            poly_vec.get_num_columns(),
        ));
    }

    let mut poly: Vec<PolyOverZ> = Vec::new();
    for i in 0..poly_vec.get_num_columns() {
        let entry = poly_vec.get_entry(0, i).unwrap();
        assert!(entry.get_degree() < k);
        poly.push(entry);
    }
    let mut out = MatZ::new(k, poly.len());

    for (i, entry) in poly.iter().enumerate() {
        for j in 0..k {
            match entry.get_coeff(j) {
                Ok(value) => out.set_entry(j, i, &value)?,
                Err(_) => break,
            }
        }
    }

    Ok(out)
}

fn polyq_to_matq_vector(polyq: &PolyOverQ, k: i64) -> Result<MatQ, MathError> {
    assert!(polyq.get_degree() < k);
    let mut out = MatQ::new(k, 1);
    for j in 0..k {
        match polyq.get_coeff(j) {
            Ok(value) => out.set_entry(j, 0, &value)?,
            Err(_) => break,
        }
    }
    Ok(out)
}

fn matz_vector_to_polyz(matz_vector: &MatZ) -> Result<PolyOverZ, MathError> {
    if !matz_vector.is_column_vector() {
        return Err(MathError::VectorFunctionCalledOnNonVector(
            String::from("matz_vector_to_polyz"),
            matz_vector.get_num_rows(),
            matz_vector.get_num_columns(),
        ));
    }
    let mut out = PolyOverZ::default();
    for i in 0..matz_vector.get_num_rows() {
        out.set_coeff(i, matz_vector.get_entry(i, 0)?)?
    }
    Ok(out)
}

#[cfg(test)]
mod test_helper_conversions {
    use super::{polyq_to_matq_vector, polyz_vector_to_matz};
    use crate::{
        integer::{
            mat_poly_over_z::sample::discrete_gauss::matz_vector_to_polyz, MatPolyOverZ, MatZ,
            PolyOverZ,
        },
        rational::{MatQ, PolyOverQ},
    };
    use std::str::FromStr;

    #[test]
    fn standard_basis() {
        let standard_basis = MatPolyOverZ::from_str("[[1  1, 2  0 1]]").unwrap();
        let basis = polyz_vector_to_matz(&standard_basis, 3).unwrap();

        assert_eq!(MatZ::identity(3, 2), basis)
    }

    #[test]
    fn convert_center() {
        let poly = PolyOverQ::from_str("3  1/2 5 17/3").unwrap();
        let center = polyq_to_matq_vector(&poly, 3).unwrap();

        let cmp_center = MatQ::from_str("[[1/2],[5],[17/3]]").unwrap();
        assert_eq!(cmp_center, center)
    }

    #[test]
    fn convert_vector_to_poly() {
        let vector = MatZ::from_str("[[17],[3],[-5]]").unwrap();
        let poly = matz_vector_to_polyz(&vector).unwrap();

        let cmp_poly = PolyOverZ::from_str("3  17 3 -5").unwrap();
        assert_eq!(cmp_poly, poly)
    }
}
