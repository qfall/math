// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`MatNTTPolynomialRingZq`] matrix.

use crate::{
    integer::Z,
    integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq},
    traits::MatrixDimensions,
};

impl MatrixDimensions for MatNTTPolynomialRingZq {
    /// Returns the number of rows of the matrix as an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq}, traits::MatrixDimensions};
    /// use std::str::FromStr;
    /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
    /// modulus.set_ntt_unchecked(64);
    ///
    /// let matrix = MatNTTPolynomialRingZq::sample_uniform(3, 2, &modulus);
    /// let nr_rows = matrix.get_num_rows();
    /// ```
    fn get_num_rows(&self) -> i64 {
        self.nr_rows as i64
    }

    /// Returns the number of columns of the matrix as an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq}, traits::MatrixDimensions};
    /// use std::str::FromStr;
    /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
    /// modulus.set_ntt_unchecked(64);
    ///
    /// let matrix = MatNTTPolynomialRingZq::sample_uniform(3, 2, &modulus);
    /// let nr_columns = matrix.get_num_columns();
    /// ```
    fn get_num_columns(&self) -> i64 {
        self.nr_columns as i64
    }
}

impl MatNTTPolynomialRingZq {
    /// Returns the modulus of the matrix in NTT representation as a [`ModulusPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 17").unwrap();
    /// let matrix = MatNTTPolynomialRingZq::sample_uniform(2, 2, &modulus);
    ///
    /// let modulus = matrix.get_mod();
    /// ```
    pub fn get_mod(&self) -> ModulusPolynomialRingZq {
        self.modulus.clone()
    }

    /// Returns the slice of `matrix` corresponding to the entry in row `row` and column `column`.
    ///
    /// Parameters:
    /// - `row`: defines the row where the entry to fetch is located
    /// - `column`: defines the column where the entry to fetch is located
    ///
    /// Returns a slice `&[Z]` containing the requested entry.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
    /// modulus.set_ntt_unchecked(64);
    ///
    /// let matrix = MatNTTPolynomialRingZq::sample_uniform(2, 2, &modulus);
    /// let entry = matrix.get_entry(0, 0);
    ///
    /// assert_eq!(4, entry.len());
    /// ```
    ///
    /// # Panics ...
    /// - if `row >= self.get_num_rows()` or `column >= self.get_num_columns()`.
    pub fn get_entry(&self, row: usize, column: usize) -> &[Z] {
        assert!(
            row < self.nr_rows,
            "`row` needs to be smaller than `nr_rows`."
        );
        assert!(
            column < self.nr_columns,
            "`column` needs to be smaller than `nr_columns`."
        );

        let index = self.modulus.get_degree() as usize * row
            + self.modulus.get_degree() as usize * self.nr_rows * column;
        &self.matrix[index..index + self.modulus.get_degree() as usize]
    }
}

#[cfg(test)]
mod test_matrix_dimensions {
    use crate::{
        integer::{MatPolyOverZ, Z},
        integer_mod_q::{MatNTTPolynomialRingZq, MatPolynomialRingZq, ModulusPolynomialRingZq},
        traits::MatrixDimensions,
    };
    use std::str::FromStr;

    /// Ensures that the correct number of rows is returned.
    #[test]
    fn nr_rows() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        let matrix = MatNTTPolynomialRingZq::sample_uniform(17, 2, &modulus);
        let nr_rows = matrix.get_num_rows();

        assert_eq!(17, nr_rows);
    }

    /// Ensures that the correct number of columns is returned.
    #[test]
    fn nr_columns() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        let matrix = MatNTTPolynomialRingZq::sample_uniform(2, 13, &modulus);
        let nr_columns = matrix.get_num_columns();

        assert_eq!(13, nr_columns);
    }

    /// Ensures that the correct entries are returned.
    #[test]
    fn get_entry() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);
        let mat_poly = MatPolyOverZ::from_str("[[4  15 17 19 21],[4  1 2 3 4]]").unwrap();
        let matrix = MatPolynomialRingZq::from((&mat_poly, &modulus));

        let ntt_matrix = MatNTTPolynomialRingZq::from(&matrix);

        assert_eq!(
            [Z::from(112), Z::from(189), Z::from(81), Z::from(192)],
            ntt_matrix.get_entry(0, 0)
        );
        assert_eq!(
            [Z::from(97), Z::from(56), Z::from(66), Z::from(42)],
            ntt_matrix.get_entry(1, 0)
        );
    }
}
