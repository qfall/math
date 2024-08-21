// Copyright © 2024 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for Gaussian distributions over [`MatQ`].

use crate::{
    error::MathError,
    rational::{MatQ, Q},
    traits::{GetEntry, GetNumColumns, GetNumRows, SetEntry},
};

impl MatQ {
    /// Chooses a [`MatQ`] instance according to the continuous Gaussian distribution.
    /// Here, each entry is chosen according to the provided distribution.
    ///
    /// Parameters:
    /// - `center`: specifies the center for each entry of the matrix
    /// - `sigma`: specifies the standard deviation
    ///
    /// Returns new [`MatQ`] sample chosen according to the specified continuous Gaussian
    /// distribution or a [`MathError`] if the specified parameters were not chosen
    /// appropriately (`sigma > 0`).
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    ///
    /// let sample = MatQ::sample_gauss(5, 5, 0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`NonPositive`](MathError::NonPositive)
    ///     if `sigma <= 0`.
    pub fn sample_gauss(center: &MatQ, sigma: impl Into<f64>) -> Result<MatQ, MathError> {
        let mut out = MatQ::new(center.get_num_rows(), center.get_num_columns());
        let sigma = sigma.into();

        for i in 0..out.get_num_rows() {
            for j in 0..out.get_num_columns() {
                let center_entry_ij = center.get_entry(i, j)?;
                let sample = Q::sample_gauss(center_entry_ij, sigma)?;
                out.set_entry(i, j, sample)?
            }
        }

        Ok(out)
    }
}

#[cfg(test)]
mod test_sample_gauss {
    use crate::{
        rational::MatQ,
        traits::{GetNumColumns, GetNumRows},
    };

    /// Ensure that an error is returned if `sigma` is not positive
    #[test]
    fn non_positive_sigma() {
        let center = MatQ::new(5, 5);
        for sigma in [0, -1] {
            assert!(MatQ::sample_gauss(&center, sigma).is_err())
        }
    }

    /// Ensure that the samples are of correct dimension
    #[test]
    fn correct_dimension() {
        for (x, y) in [(5, 5), (1, 10), (10, 1)] {
            let center = MatQ::new(x, y);
            let sample = MatQ::sample_gauss(&center, 1).unwrap();
            assert_eq!(center.get_num_rows(), sample.get_num_rows());
            assert_eq!(center.get_num_columns(), sample.get_num_columns());
        }
    }
}
