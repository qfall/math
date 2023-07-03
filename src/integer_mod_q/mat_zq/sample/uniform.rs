// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for the uniform distributions.

use crate::{
    integer::Z,
    integer_mod_q::MatZq,
    traits::{GetNumColumns, GetNumRows, SetEntry},
    utils::sample::uniform::sample_uniform_rejection,
};
use std::fmt::Display;

impl MatZq {
    /// Outputs a [`MatZq`] instance with entries chosen uniform at random
    /// in `[0, modulus)`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `num_rows`: specifies the number of rows the new matrix should have
    /// - `num_cols`: specifies the number of columns the new matrix should have
    /// - `modulus`: specifies the modulus of the matrix and defines the interval
    /// over which is sampled
    ///
    /// Returns a new [`MatZq`] instance with entries chosen
    /// uniformly at random in `[0, modulus)`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    ///
    /// let matrix = MatZq::sample_uniform(3, 3, &17);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns or the modulus are not suited to create a matrix.
    /// For further information see [`MatZq::new`].
    pub fn sample_uniform(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: impl Into<Z>,
    ) -> Self {
        let modulus: Z = modulus.into();
        let mut matrix = MatZq::new(num_rows, num_cols, modulus.clone());

        for row in 0..matrix.get_num_rows() {
            for col in 0..matrix.get_num_columns() {
                let sample = sample_uniform_rejection(&modulus).unwrap();
                matrix.set_entry(row, col, sample).unwrap();
            }
        }

        matrix
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::traits::{GetEntry, GetNumColumns, GetNumRows};
    use crate::{
        integer::Z,
        integer_mod_q::{MatZq, Modulus},
    };

    /// Checks whether the boundaries of the interval are kept for small moduli.
    #[test]
    fn boundaries_kept_small() {
        for _ in 0..32 {
            let matrix = MatZq::sample_uniform(1, 1, 17);
            let sample = matrix.get_entry(0, 0).unwrap();
            assert!(Z::ZERO <= sample);
            assert!(sample < Z::from(17));
        }
    }

    /// Checks whether the boundaries of the interval are kept for large moduli.
    #[test]
    fn boundaries_kept_large() {
        let modulus = Z::from(u64::MAX);
        for _ in 0..256 {
            let matrix = MatZq::sample_uniform(1, 1, &modulus);
            let sample = matrix.get_entry(0, 0).unwrap();
            assert!(Z::ZERO <= sample);
            assert!(sample < modulus);
        }
    }

    /// Checks whether matrices with at least one dimension chosen smaller than `1`
    /// or too big for an [`i64`] results in a panic.
    #[should_panic]
    #[test]
    fn false_size() {
        let modulus = Z::from(15);

        let _ = MatZq::sample_uniform(0, 3, &modulus);
    }

    /// Checks whether providing an invalid interval/ modulus results in a panic.
    #[should_panic]
    #[test]
    fn invalid_modulus() {
        let _ = MatZq::sample_uniform(4, 1, 1);
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing Into<Z> + Clone, i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from(7);
        let z = Z::from(7);

        let _ = MatZq::sample_uniform(1, 1, 7u8);
        let _ = MatZq::sample_uniform(1, 1, 7u16);
        let _ = MatZq::sample_uniform(1, 1, 7u32);
        let _ = MatZq::sample_uniform(1, 1, 7u64);
        let _ = MatZq::sample_uniform(1, 1, 7i8);
        let _ = MatZq::sample_uniform(1, 1, 7i16);
        let _ = MatZq::sample_uniform(1, 1, 7i32);
        let _ = MatZq::sample_uniform(1, 1, 7i64);
        let _ = MatZq::sample_uniform(1, 1, &modulus);
        let _ = MatZq::sample_uniform(1, 1, &z);
    }

    /// Checks whether the size of uniformly random sampled matrices
    /// fits the specified dimensions.
    #[test]
    fn matrix_size() {
        let modulus = Z::from(15);

        let mat_0 = MatZq::sample_uniform(3, 3, &modulus);
        let mat_1 = MatZq::sample_uniform(4, 1, &modulus);
        let mat_2 = MatZq::sample_uniform(1, 5, &modulus);
        let mat_3 = MatZq::sample_uniform(15, 20, &modulus);

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
