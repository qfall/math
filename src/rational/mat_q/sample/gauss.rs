// Copyright © 2024 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for gaussian distributions over [`MatQ`].

use crate::{
    error::MathError,
    rational::{MatQ, Q},
    traits::{GetNumColumns, GetNumRows, SetEntry},
};
use std::fmt::Display;

impl MatQ {
    /// Chooses a [`MatQ`] instance according to the continuous Gaussian distribution.
    /// Here, each entry is chosen according to the provided distribution.
    ///
    /// Parameters:
    /// - `num_rows`: specifies the number of rows the new matrix should have
    /// - `num_cols`: specifies the number of columns the new matrix should have
    /// - `center`: specifies the position of the center
    /// - `sigma`: specifies the standard deviation
    ///
    /// Returns new [`MatQ`] sample chosen according to the specified continuous Gaussian
    /// distribution or a [`MathError`] if the specified parameters were not chosen
    /// appropriately, `sigma > 0`.
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
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    ///     For further information see [`MatQ::new`].
    pub fn sample_gauss(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        center: impl Into<f64>,
        sigma: impl Into<f64>,
    ) -> Result<MatQ, MathError> {
        let mut out = MatQ::new(num_rows, num_cols);
        let (center, sigma) = (center.into(), sigma.into());

        for i in 0..out.get_num_rows() {
            for j in 0..out.get_num_columns() {
                let sample = Q::sample_gauss(center, sigma)?;
                out.set_entry(i, j, sample)?
            }
        }

        Ok(out)
    }
}

#[cfg(test)]
mod test_sample_gauss {
    use crate::rational::MatQ;

    /// Ensure that an error is returned if `sigma` is not positive
    #[test]
    fn non_positive_sigma() {
        let sample = MatQ::sample_gauss(5, 5, 0, 1).unwrap();
        println!("{sample}");
        for (mu, sigma) in [(0, 0), (0, -1)] {
            assert!(MatQ::sample_gauss(2, 2, mu, sigma).is_err())
        }
    }

    /// Ensure that the function panics, if a negative number of rows is provided.
    #[test]
    #[should_panic]
    fn negative_rows() {
        let _ = MatQ::sample_gauss(-1, 1, 0, 1);
    }

    /// Ensure that the function panics, if a negative number of columns is provided.
    #[test]
    #[should_panic]
    fn negative_columns() {
        let _ = MatQ::sample_gauss(1, -1, 0, 1);
    }

    /// Ensure that the function panics, if the number of columns is zero.
    #[test]
    #[should_panic]
    fn zero_columns() {
        let _ = MatQ::sample_gauss(1, 0, 0, 1);
    }

    /// Ensure that the function panics, if the number of rows is zero.
    #[test]
    #[should_panic]
    fn zero_rows() {
        let _ = MatQ::sample_gauss(0, 1, 0, 1);
    }
}
