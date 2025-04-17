// Copyright © 2024 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module implements the Cholesky Decomposition for Hermitian positive-definite
//! matrices.

use super::MatQ;
use crate::{
    rational::Q,
    traits::{
        Concatenate, MatrixDimensions, MatrixGetEntry, MatrixGetSubmatrix, MatrixSetEntry,
        MatrixSetSubmatrix,
    },
};

impl MatQ {
    /// This function performs the Cholesky decomposition (the Cholesky algorithm) and
    /// produces a matrix `L` such that `self = L * L^T`.
    /// This function relies on the precision of [`Q::sqrt`] and will not provide
    /// perfect results in all cases.
    /// Furthermore, the Cholesky decomposition requires a Hermitian positive-definite
    /// matrix.
    ///
    /// Returns the Cholesky decomposition of a Hermitian positive-definite matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[4, 12, -16],[12,37,-43],[-16,-43,98]]").unwrap();
    ///
    /// let l = matrix.cholesky_decomposition();
    /// assert_eq!(matrix, &l * l.transpose());
    /// ```
    ///
    /// # Panics ...
    /// - if `self` is not a symmetric matrix,
    /// - if `self` has eigenvalues smaller than `0`.
    pub fn cholesky_decomposition(&self) -> MatQ {
        assert!(self.is_symmetric(), "The provided matrix is not symmetric.");
        let n = self.get_num_columns();

        let mut a = self.clone();
        let mut l = MatQ::identity(n, n);

        for i in 0..n {
            // get first entry and ith column
            let a_ii = unsafe { a.get_entry_unchecked(0, 0) };
            assert!(a_ii > Q::ZERO, "The matrix is not positive-definite.");
            let column_a_i = match i {
                0 => unsafe { a.get_column_unchecked(0) },
                _ => unsafe { MatQ::new(i, 1).get_column_unchecked(0) }
                    .concat_vertical(&unsafe { a.get_column_unchecked(0) })
                    .unwrap(),
            } * (1 / (a_ii.sqrt()));
            // in the previous line: sqrt panics if `a_ii` is negative, i.e. if an
            // eigenvalue is negative.

            // produce L matrix recursively
            let mut l_i = MatQ::identity(n, n);
            l_i.set_column(i, &column_a_i, 0).unwrap();
            l = l * l_i;

            // update matrix A recursively
            if i < n - 1 {
                let b = a.get_submatrix(1, -1, 1, -1).unwrap();
                let b_minus = (1 / a_ii)
                    * a.get_submatrix(1, -1, 0, 0).unwrap()
                    * a.get_submatrix(0, 0, 1, -1).unwrap();
                a = b - b_minus;
            }
        }
        l
    }

    /// This function implements the Cholesky decomposition according to FLINTs
    /// implementation. As FLINTs algorithm is not (yet) accessible through flint-sys,
    /// this implementation follows the implementation of the algorithm from FLINT.
    /// This, however, also means that we will work with less precision as we will work
    /// with conversions to [`f64`] and not use [`Q`].
    /// In turn, this makes the function much more efficient, but *not* applicable to
    /// large numbers.
    ///
    /// This function relies on the precision of [`f64::sqrt`] and will not provide
    /// perfect results in all cases.
    /// Furthermore, the Cholesky decomposition requires a Hermitian positive-definite
    /// matrix.
    ///
    /// Returns the Cholesky decomposition of a Hermitian positive-definite matrix.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatQ::from_str("[[4, 12, -16],[12,37,-43],[-16,-43,98]]").unwrap();
    ///
    /// let l = matrix.cholesky_decomposition_flint();
    /// assert_eq!(matrix, &l * l.transpose());
    /// ```
    ///
    /// # Panics ...
    /// - if `self` is not a symmetric matrix,
    /// - if `self` has eigenvalues smaller than `0`.
    pub fn cholesky_decomposition_flint(&self) -> MatQ {
        assert!(self.is_symmetric(), "The provided matrix is not symmetric.");
        let mat_dimension = self.get_num_rows() as usize;

        let mut out = vec![vec![0.0; mat_dimension]; mat_dimension];
        let mat = self.collect_entries_f64();

        // This code snippet originates from [flint](https://github.com/flintlib/flint/blob/main/src/fmpz_mat/chol_d.c)
        // it is not part of [flint-sys] as it requires a specific data-type `d_mat_t`
        for i in 0..mat_dimension {
            for j in 0..=i {
                let mut s: f64 = 0.0;
                for k in 0..j {
                    s += out[i][k] * out[j][k]
                }
                if i == j {
                    // Find this requirement in https://en.wikipedia.org/wiki/Cholesky_decomposition#The_Cholesky_algorithm
                    // a_ii > 0 as `self` needs to be positive definite
                    assert!(
                        mat[i][i] > s,
                        "The provided matrix is not positive definite."
                    );

                    out[i][j] = (mat[i][i] - s).sqrt();
                } else {
                    out[i][j] = (mat[i][j] - s) / out[j][j];
                }
            }
        }

        // Assemble Cholesky decomposition as MatQ
        let mut res = MatQ::new(mat_dimension, mat_dimension);
        for (i, row) in out.iter().enumerate().take(mat_dimension) {
            for (j, entry) in row.iter().enumerate().take(mat_dimension) {
                unsafe { res.set_entry_unchecked(i as i64, j as i64, *entry) };
            }
        }

        res
    }
}

#[cfg(test)]
mod test_cholesky_decomposition {
    use crate::{
        rational::{MatQ, Q},
        traits::MatrixSetEntry,
    };
    use std::str::FromStr;

    /// Ensure that a basic example (from Wikipedia) works.
    #[test]
    fn valid_input() {
        let matrix = MatQ::from_str("[[4, 12, -16],[12,37,-43],[-16,-43,98]]").unwrap();

        let l = MatQ::from_str("[[2, 0, 0],[6, 1, 0],[-8, 5, 3]]").unwrap();
        assert_eq!(l, matrix.cholesky_decomposition());
    }

    /// Ensure that the function panics if a non-square matrix is provided
    #[test]
    #[should_panic]
    fn non_square() {
        let matrix = MatQ::new(3, 2);

        matrix.cholesky_decomposition();
    }

    /// Ensure that the function panics if a matrix with negative eigenvalues is provided
    #[test]
    #[should_panic]
    fn non_positive_definite() {
        let matrix: MatQ = -1 * MatQ::identity(2, 2);

        matrix.cholesky_decomposition();
    }

    /// Ensure that the function panics if a non-symmetric matrix is provided
    #[test]
    #[should_panic]
    fn non_symmetric() {
        let mut matrix: MatQ = MatQ::identity(2, 2);
        matrix.set_entry(1, 0, Q::MINUS_ONE).unwrap();

        matrix.cholesky_decomposition();
    }

    /// Ensure that the function works with large entries
    #[test]
    fn large_entries() {
        // matrix = [[1,-2^32],[-2^{32},2^64+1]] -> L = [[1,0],[-2^32,1]]
        let matrix: MatQ = MatQ::from_str(&format!(
            "[[{},-{}],[-{},{}]]",
            -1,
            2_i64.pow(32),
            2_i64.pow(32),
            u64::MAX
        ))
        .unwrap()
            + 2 * MatQ::identity(2, 2);

        assert_eq!(
            matrix,
            (matrix.cholesky_decomposition() * matrix.cholesky_decomposition().transpose())
        );
    }
}

#[cfg(test)]
mod test_cholesky_decomposition_flint {
    use crate::{
        rational::{MatQ, Q},
        traits::MatrixSetEntry,
    };
    use std::str::FromStr;

    /// Ensure that a basic example (from Wikipedia) works.
    #[test]
    fn valid_input() {
        let matrix = MatQ::from_str("[[4, 12, -16],[12,37,-43],[-16,-43,98]]").unwrap();

        let l = MatQ::from_str("[[2, 0, 0],[6, 1, 0],[-8, 5, 3]]").unwrap();
        assert_eq!(l, matrix.cholesky_decomposition_flint());
    }

    /// Ensure that the function panics if a non-square matrix is provided
    #[test]
    #[should_panic]
    fn non_square() {
        let matrix = MatQ::new(3, 2);

        matrix.cholesky_decomposition_flint();
    }

    /// Ensure that the function panics if a matrix with negative eigenvalues is provided
    #[test]
    #[should_panic]
    fn non_positive_definite() {
        let matrix: MatQ = -1 * MatQ::identity(2, 2);

        matrix.cholesky_decomposition_flint();
    }

    /// Ensure that the function panics if a non-symmetric matrix is provided
    #[test]
    #[should_panic]
    fn non_symmetric() {
        let mut matrix: MatQ = MatQ::identity(2, 2);
        matrix.set_entry(1, 0, Q::MINUS_ONE).unwrap();

        matrix.cholesky_decomposition_flint();
    }
}
