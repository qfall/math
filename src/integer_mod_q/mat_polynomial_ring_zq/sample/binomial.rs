// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling
//! according to the binomial distribution.

use crate::{
    error::MathError,
    integer::{MatPolyOverZ, Z},
    integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    rational::Q,
};
use std::fmt::Display;

impl MatPolynomialRingZq {
    /// Outputs a [`MatPolynomialRingZq`] instance with entries chosen according to the binomial
    /// distribution parameterized by `n` and `p`.
    ///
    /// Parameters:
    /// - `num_rows`: specifies the number of rows the new matrix should have
    /// - `num_cols`: specifies the number of columns the new matrix should have
    /// - `modulus`: specifies the [`ModulusPolynomialRingZq`] over which the
    /// ring of polynomials modulo `modulus.get_q()` is defined
    /// - `n`: specifies the number of trials
    /// - `p`: specifies the probability of success
    ///
    /// Returns a new [`MatPolynomialRingZq`] instance with entries chosen
    /// according to the binomial distribution or a [`MathError`]
    /// if `n < 1`, `p ∉ (0,1)`, `n` does not fit into an [`i64`],
    /// or the dimensions of the matrix were chosen too small.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    ///
    /// let sample = MatPolynomialRingZq::sample_binomial(2, 2, &modulus, 2, 0.5).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if `n < 1` or `p ∉ (0,1)`.
    /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
    /// if `n` does not fit into an [`i64`].
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    /// For further information see [`MatPolynomialRingZq::new`].
    /// - if the provided [`ModulusPolynomialRingZq`] has degree `0` or smaller.
    pub fn sample_binomial(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: impl Into<ModulusPolynomialRingZq>,
        n: impl Into<Z>,
        p: impl Into<Q>,
    ) -> Result<Self, MathError> {
        Self::sample_binomial_with_offset(num_rows, num_cols, modulus, 0, n, p)
    }

    /// Outputs a [`MatPolynomialRingZq`] instance with entries chosen according to the binomial
    /// distribution parameterized by `n` and `p` with given `offset`.
    ///
    /// Parameters:
    /// - `num_rows`: specifies the number of rows the new matrix should have
    /// - `num_cols`: specifies the number of columns the new matrix should have
    /// - `modulus`: specifies the [`ModulusPolynomialRingZq`] over which the
    /// ring of polynomials modulo `modulus.get_q()` is defined
    /// - `offset`: specifies an offset applied to each sample
    /// collected from the binomial distribution
    /// - `n`: specifies the number of trials
    /// - `p`: specifies the probability of success
    ///
    /// Returns a new [`MatPolynomialRingZq`] instance with entries chosen
    /// according to the binomial distribution or a [`MathError`]
    /// if `n < 1`, `p ∉ (0,1)`, `n` does not fit into an [`i64`],
    /// or the dimensions of the matrix were chosen too small.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    ///
    /// let sample = MatPolynomialRingZq::sample_binomial_with_offset(2, 2, &modulus, -1, 2, 0.5).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if `n < 1` or `p ∉ (0,1)`.
    /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
    /// if `n` does not fit into an [`i64`].
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    /// For further information see [`MatPolynomialRingZq::new`].
    /// - if the provided [`ModulusPolynomialRingZq`] has degree `0`.
    pub fn sample_binomial_with_offset(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: impl Into<ModulusPolynomialRingZq>,
        offset: impl Into<Z>,
        n: impl Into<Z>,
        p: impl Into<Q>,
    ) -> Result<Self, MathError> {
        let modulus = modulus.into();
        assert!(
            modulus.get_degree() > 0,
            "ModulusPolynomial of degree 0 is insufficient to sample over."
        );

        let matrix = MatPolyOverZ::sample_binomial_with_offset(
            num_rows,
            num_cols,
            modulus.get_degree() - 1,
            offset,
            n,
            p,
        )?;
        Ok(MatPolynomialRingZq::from((matrix, modulus)))
    }
}

#[cfg(test)]
mod test_sample_binomial {
    use super::{MatPolynomialRingZq, ModulusPolynomialRingZq, Q, Z};
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::PolyOverZq,
        traits::{GetCoefficient, GetEntry, GetNumColumns, GetNumRows, SetCoefficient},
    };
    use std::str::FromStr;

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether the boundaries of the interval are kept.
    #[test]
    fn boundaries_kept() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        for _ in 0..8 {
            let matrix = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 2, 0.5).unwrap();
            let entry: PolyOverZ = matrix.get_entry(0, 0).unwrap();
            let poly = entry.get_coeff(0).unwrap();

            assert!(Z::ZERO <= poly);
            assert!(poly <= Z::from(2));
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let mut modulus = PolyOverZq::from((1, u64::MAX));
            modulus.set_coeff(degree, 1).unwrap();
            let modulus = ModulusPolynomialRingZq::from(&modulus);

            let matrix = MatPolynomialRingZq::sample_binomial(1, 1, modulus, 256, 0.99999).unwrap();
            let poly: PolyOverZ = matrix.get_entry(0, 0).unwrap();

            assert_eq!(
                degree,
                poly.get_degree() + 1,
                "This test can fail with probability close to 0."
            );
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let _ = MatPolynomialRingZq::sample_binomial(0, 3, modulus, 1, 0.5);
    }

    /// Checks whether 0 modulus polynomial is insufficient.
    #[test]
    #[should_panic]
    fn invalid_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("1  1 mod 17").unwrap();

        let _ = MatPolynomialRingZq::sample_binomial(1, 1, modulus, 1, 0.5);
    }

    /// Checks whether `sample_binomial` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    #[test]
    fn availability() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 1u16, 7u8);
        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 1u32, 7u16);
        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 1u64, 7u32);
        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 1i8, 7u64);
        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 1i16, 7i8);
        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 1i32, 7i16);
        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 1i64, 7i32);
        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, Z::ONE, 7i64);
        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 1u8, 0.5f32);
        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 1u8, 0.5f64);
        let _ = MatPolynomialRingZq::sample_binomial(1, 1, &modulus, 1, Q::from((1, 2)));
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let mat_0 = MatPolynomialRingZq::sample_binomial(3, 3, &modulus, 1, 0.5).unwrap();
        let mat_1 = MatPolynomialRingZq::sample_binomial(4, 1, &modulus, 1, 0.5).unwrap();
        let mat_2 = MatPolynomialRingZq::sample_binomial(1, 5, &modulus, 1, 0.5).unwrap();
        let mat_3 = MatPolynomialRingZq::sample_binomial(15, 20, &modulus, 1, 0.5).unwrap();

        assert_eq!(3, mat_0.get_num_rows());
        assert_eq!(3, mat_0.get_num_columns());
        assert_eq!(4, mat_1.get_num_rows());
        assert_eq!(1, mat_1.get_num_columns());
        assert_eq!(1, mat_2.get_num_rows());
        assert_eq!(5, mat_2.get_num_columns());
        assert_eq!(15, mat_3.get_num_rows());
        assert_eq!(20, mat_3.get_num_columns());
    }
}

#[cfg(test)]
mod test_sample_binomial_with_offset {
    use super::{MatPolynomialRingZq, ModulusPolynomialRingZq, Q, Z};
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::PolyOverZq,
        traits::{GetCoefficient, GetEntry, GetNumColumns, GetNumRows, SetCoefficient},
    };
    use std::str::FromStr;

    // As all major tests regarding an appropriate binomial distribution,
    // whether the correct interval is kept, and if the errors are thrown correctly,
    // are performed in the `utils` module, we omit these tests here.

    /// Checks whether the boundaries of the interval are kept.
    #[test]
    fn boundaries_kept() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        for _ in 0..8 {
            let matrix =
                MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, -1, 2, 0.5)
                    .unwrap();
            let poly: PolyOverZ = matrix.get_entry(0, 0).unwrap();
            let value = poly.get_coeff(0).unwrap();

            assert!(Z::from(16) <= value || value <= Z::ONE);
        }
    }

    /// Checks whether the number of coefficients is correct.
    #[test]
    fn nr_coeffs() {
        let degrees = [1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let mut modulus = PolyOverZq::from((1, u64::MAX));
            modulus.set_coeff(degree, 1).unwrap();
            let modulus = ModulusPolynomialRingZq::from(&modulus);

            let matrix =
                MatPolynomialRingZq::sample_binomial_with_offset(1, 1, modulus, 1, 256, 0.99999)
                    .unwrap();
            let poly: PolyOverZ = matrix.get_entry(0, 0).unwrap();

            assert_eq!(degree, poly.get_degree() + 1,);
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in an error.
    #[should_panic]
    #[test]
    fn false_size() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let _ = MatPolynomialRingZq::sample_binomial_with_offset(0, 3, modulus, -1, 1, 0.5);
    }

    /// Checks whether 0 modulus polynomial is insufficient.
    #[test]
    #[should_panic]
    fn invalid_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("1  1 mod 17").unwrap();

        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, modulus, -1, 1, 0.5);
    }

    /// Checks whether `sample_binomial_with_offset` is available for all types
    /// implementing [`Into<Z>`], i.e. u8, u16, u32, u64, i8, ...
    /// and [`Into<Q>`], i.e. u8, u16, i8, i16, f32, f64, ...
    #[test]
    fn availability() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, -1, 1u16, 7u8);
        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, 0, 1u32, 7u16);
        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, -1, 1u64, 7u32);
        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, -1, 1i8, 7u64);
        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, -1, 1i16, 7i8);
        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, -1, 1i32, 7i16);
        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, -1, 1i64, 7i32);
        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, -1, Z::ONE, 7i64);
        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, -1, 1u8, 0.5f32);
        let _ = MatPolynomialRingZq::sample_binomial_with_offset(1, 1, &modulus, 1, 1u8, 0.5f64);
        let _ = MatPolynomialRingZq::sample_binomial_with_offset(
            1,
            1,
            &modulus,
            Z::ONE,
            1,
            Q::from((1, 2)),
        );
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let mat_0 =
            MatPolynomialRingZq::sample_binomial_with_offset(3, 3, &modulus, -1, 1, 0.5).unwrap();
        let mat_1 =
            MatPolynomialRingZq::sample_binomial_with_offset(4, 1, &modulus, -1, 1, 0.5).unwrap();
        let mat_2 =
            MatPolynomialRingZq::sample_binomial_with_offset(1, 5, &modulus, -1, 1, 0.5).unwrap();
        let mat_3 =
            MatPolynomialRingZq::sample_binomial_with_offset(15, 20, &modulus, -1, 1, 0.5).unwrap();

        assert_eq!(3, mat_0.get_num_rows());
        assert_eq!(3, mat_0.get_num_columns());
        assert_eq!(4, mat_1.get_num_rows());
        assert_eq!(1, mat_1.get_num_columns());
        assert_eq!(1, mat_2.get_num_rows());
        assert_eq!(5, mat_2.get_num_columns());
        assert_eq!(15, mat_3.get_num_rows());
        assert_eq!(20, mat_3.get_num_columns());
    }
}
