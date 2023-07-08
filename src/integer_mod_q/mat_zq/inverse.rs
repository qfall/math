// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `inverse` function.

use super::MatZq;
use crate::{
    integer::{MatZ, Z},
    integer_mod_q::Zq,
    traits::{Concatenate, Gcd, GetEntry, GetNumColumns, GetNumRows, Pow},
};

impl MatZq {
    /// Returns the inverse of the matrix if it exists (is square and
    /// has a determinant unequal to zero) and `None` otherwise.
    ///
    /// Note that the modulus is assumed to be prime.
    /// If it is not, it can happen that the function panics.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZq::from_str("[[1,2],[3,4]] mod 7").unwrap();
    /// let matrix_invert = matrix.inverse_prime().unwrap();
    ///
    /// let id = &matrix_invert * &matrix;
    ///
    /// assert_eq!("[[5, 1],[5, 3]] mod 7", matrix_invert.to_string());
    /// assert_eq!("[[1, 0],[0, 1]] mod 7", id.to_string());
    /// ```
    ///
    /// # Panics ...
    /// - if the number of rows is not equal to the number of columns.
    /// - if the inverse of an entry can not be computed because the modulus is not prime.
    pub fn inverse_prime(&self) -> Option<MatZq> {
        // check if determinant is coprime to modulus
        let det = MatZ::from(self).det().ok()?;
        if det.gcd(Z::from(self.get_mod())) != Z::ONE {
            None
        } else {
            // concatenate the matrix with the identity matrix
            let matrix_identity = self
                .concat_horizontal(&MatZq::identity(
                    self.get_num_rows(),
                    self.get_num_columns(),
                    self.get_mod(),
                ))
                .unwrap();

            let identity_inverse = matrix_identity.gaussian_elimination_prime();

            // the inverse is now the right half of the matrix `identity_inverse`
            let mut inverse =
                MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());
            for i in 0..self.get_num_columns() {
                inverse
                    .set_column(i, &identity_inverse, self.get_num_columns() + i)
                    .unwrap();
            }
            Some(inverse)
        }
    }

    /// Returns the `row echelon form` of the matrix using gaussian elimination.
    ///
    /// Note that the modulus is assumed to be prime.
    /// If it is not, it can happen that the function panics.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZq::from_str("[[1,2],[3,4]] mod 7").unwrap();
    /// let matrix_invert = matrix.gaussian_elimination_prime();
    /// ```
    ///
    /// # Panics ...
    /// - if the inverse of an entry can not be computed because the modulus is not prime
    pub fn gaussian_elimination_prime(&self) -> MatZq {
        let mut out = self.clone();
        // row_count is the number of rows where we have a 1 entry already
        let mut row_count = 0;
        // we iterate over all columns and try to find an entry that is not 0
        for column_nr in 0..self.get_num_columns() {
            if row_count >= self.get_num_rows() {
                break;
            }

            let mut current_row = -1;
            let mut entry = Zq::from((1, self.get_mod()));
            for row_nr in row_count..self.get_num_rows() {
                entry = out.get_entry(row_nr, column_nr).unwrap();
                if !Zq::is_zero(&entry) {
                    current_row = row_nr;
                    break;
                }
            }
            if current_row == -1 {
                continue;
            }

            if let Ok(inv) = entry.pow(-1) {
                let row = inv * out.get_row(current_row).unwrap();
                out.set_row(current_row, &row, 0).unwrap();

                // set all other entries in that column to `0` (gaussian elimination)
                for row_nr_other in (0..self.get_num_rows()).filter(|x| *x != current_row) {
                    let old_row = out.get_row(row_nr_other).unwrap();
                    let entry: Z = old_row.get_entry(0, column_nr).unwrap();
                    let new_row = &old_row - entry * &row;
                    out.set_row(row_nr_other, &new_row, 0).unwrap();
                }

                if row_count != current_row {
                    out.swap_rows(row_count, current_row).unwrap();
                }
                row_count += 1;
            } else {
                panic!("The modulus {} is not prime", self.get_mod());
            }
        }

        out
    }
}

#[cfg(test)]
mod test_inverse {
    use crate::{integer::MatZ, integer_mod_q::MatZq, rational::MatQ};
    use std::str::FromStr;

    /// Test whether `inverse` correctly calculates an inverse matrix.
    #[test]
    fn inverse_works() {
        let mat1 = MatZq::from_str("[[5,2],[2,1]] mod 7").unwrap();
        let cmp_inv1 = MatZq::from_str("[[1, 5],[5, 5]] mod 7").unwrap();

        let inv1 = mat1.inverse_prime().unwrap();

        assert_eq!(cmp_inv1, inv1);
    }

    /// Check if the multiplication of inverse and matrix result in an identity matrix.
    #[test]
    fn inverse_correct() {
        let mat = MatZ::from_str("[[5,2],[2,1]]").unwrap();
        let mat_q = MatQ::from(&mat);
        let cmp = MatQ::from_str("[[1,0],[0,1]]").unwrap();

        let inv = mat.inverse().unwrap();
        let diag = &mat_q * &inv;

        assert_eq!(cmp, diag);
    }

    /// Check if the multiplication of inverse and matrix result in an identity matrix.
    #[test]
    fn inverse_correct_2() {
        let mat = MatZ::from_str("[[0,2],[2,1]]").unwrap();
        let mat_q = MatQ::from(&mat);
        let cmp = MatQ::from_str("[[1,0],[0,1]]").unwrap();

        let inv = mat.inverse().unwrap();
        let diag = &mat_q * &inv;

        assert_eq!(cmp, diag);
    }

    /// Ensure that a matrix that is not square yields `None` on inversion.
    #[test]
    fn inv_none_not_squared() {
        let mat1 = MatZ::from_str("[[1,0,1],[0,1,1]]").unwrap();
        let mat2 = MatZ::from_str("[[1,0],[0,1],[1,0]]").unwrap();

        assert!(mat1.inverse().is_none());
        assert!(mat2.inverse().is_none());
    }

    /// Ensure that a matrix that has a determinant of `0` yields `None` on inversion.
    #[test]
    fn inv_none_det_zero() {
        let mat = MatZ::from_str("[[2,0],[0,0]]").unwrap();

        assert!(mat.inverse().is_none());
    }
}

#[cfg(test)]
mod test_gauss {
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Test whether `gaussian_elimination_prime` works correctly.
    #[test]
    fn gauss_works() {
        let mat1 = MatZq::from_str("[[5,2,1,0],[2,1,0,1]] mod 7").unwrap();
        let mat2 = MatZq::from_str("[[1,3,1,9],[1,1,130,1],[3,11,5,35]] mod 131").unwrap();
        let mat3 = MatZq::from_str("[[5,0,2,1,0],[5,0,2,1,0],[2,0,1,0,1]] mod 7").unwrap();

        let gauss_1 = mat1.gaussian_elimination_prime();
        let gauss_2 = mat2.gaussian_elimination_prime();
        let gauss_3 = mat3.gaussian_elimination_prime();

        assert_eq!(
            gauss_1,
            MatZq::from_str("[[1, 0, 1, 5],[0, 1, 5, 5]] mod 7").unwrap()
        );
        assert_eq!(
            gauss_2,
            MatZq::from_str("[[1, 0, 129, 128],[0, 1, 1, 4],[0, 0, 0, 0]] mod 131").unwrap()
        );
        assert_eq!(
            gauss_3,
            MatZq::from_str("[[1, 0, 0, 1, 5],[0, 0, 1, 5, 5],[0, 0, 0, 0, 0]] mod 7").unwrap()
        );
    }

    /// Test whether `gaussian_elimination_prime` yields an error if the inverse
    /// of an entry can not be computed because the modulus is not prime.
    #[test]
    #[should_panic]
    fn gauss_error() {
        let mat1 = MatZq::from_str("[[5,2,1,0],[2,1,0,1]] mod 10").unwrap();
        let _ = mat1.gaussian_elimination_prime();
    }
}
