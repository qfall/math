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
    traits::{Concatenate, GetNumRows},
};
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_rref;

impl MatZq {
    /// Returns the inverse of the matrix if it exists (is square and
    /// has a determinant unequal to zero) and `None` otherwise.
    ///
    /// Note that the modulus is assumed to be prime, otherwise the function panics.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZq::from_str("[[1, 2],[3, 4]] mod 7").unwrap();
    ///
    /// let matrix_invert = matrix.inverse_prime().unwrap();
    ///
    /// let id = &matrix_invert * &matrix;
    /// assert_eq!("[[5, 1],[5, 3]] mod 7", matrix_invert.to_string());
    /// assert_eq!("[[1, 0],[0, 1]] mod 7", id.to_string());
    /// ```
    ///
    /// # Panics ...
    /// - if the modulus is not prime.
    pub fn inverse_prime(&self) -> Option<MatZq> {
        assert!(
            self.get_mod().is_prime(),
            "The modulus of the matrix is not prime"
        );

        // Check if the matrix is spare and compute determinant
        if let Ok(det) = MatZ::from(self).det() {
            if det == Z::ZERO {
                None
            } else {
                let dimensions = self.get_num_rows();

                // Concatenate the matrix with the identity matrix.
                let matrix_identity = self
                    .concat_horizontal(&MatZq::identity(dimensions, dimensions, self.get_mod()))
                    .unwrap();

                let identity_inverse = matrix_identity.gaussian_elimination_prime();

                // The inverse is now the right half of the matrix `identity_inverse`.
                let mut inverse = MatZq::new(dimensions, dimensions, self.get_mod());
                for i in 0..dimensions {
                    inverse
                        .set_column(i, &identity_inverse, dimensions + i)
                        .unwrap();
                }
                Some(inverse)
            }
        } else {
            None
        }
    }

    /// Returns the `row echelon form` of the matrix using gaussian elimination.
    ///
    /// Note that the modulus is assumed to be prime, otherwise the function panics.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZq::from_str("[[1, 2],[3, 4]] mod 7").unwrap();
    ///
    /// let matrix_gauss = matrix.gaussian_elimination_prime();
    ///
    /// assert_eq!("[[1, 0],[0, 1]] mod 7", matrix_gauss.to_string());
    /// ```
    ///
    /// # Panics ...
    /// - if the modulus is not prime.
    pub fn gaussian_elimination_prime(self) -> MatZq {
        assert!(
            self.get_mod().is_prime(),
            "The modulus of the matrix is not prime"
        );

        // Since we only want the echelon form, the permutation `perm` is not relevant.
        let mut perm: i64 = 1;
        unsafe { fmpz_mod_mat_rref(&mut perm, &self.matrix) };

        self
    }
}

#[cfg(test)]
mod test_inverse {
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Test whether `inverse` correctly calculates an inverse matrix.
    #[test]
    fn inverse_works() {
        let mat = MatZq::from_str("[[5, 2],[2, 1]] mod 7").unwrap();

        let inv = mat.inverse_prime().unwrap();

        let cmp_inv = MatZq::from_str("[[1, 5],[5, 5]] mod 7").unwrap();
        assert_eq!(cmp_inv, inv);
    }

    /// Check if the multiplication of inverse and matrix result in an identity matrix.
    #[test]
    fn inverse_correct() {
        let mat = MatZq::from_str("[[5, 2],[2, 1]] mod 11").unwrap();

        let inv = mat.inverse_prime().unwrap();

        let diag = mat * inv;
        let cmp = MatZq::identity(2, 2, 11);
        assert_eq!(cmp, diag);
    }

    /// Check if the multiplication of inverse and matrix result in an identity matrix.
    #[test]
    fn inverse_correct_2() {
        let mat = MatZq::from_str("[[0, 2],[2, 1]] mod 3").unwrap();

        let inv = mat.inverse_prime().unwrap();
        let diag = mat * inv;

        let cmp = MatZq::from_str("[[1, 0],[0, 1]] mod 3").unwrap();
        assert_eq!(cmp, diag);
    }

    /// Ensure that a matrix that is not square yields `None` on inversion.
    #[test]
    fn inv_none_not_squared() {
        let mat_1 = MatZq::from_str("[[1, 0, 1],[0, 1, 1]] mod 3").unwrap();
        let mat_2 = MatZq::from_str("[[1, 0],[0, 1],[1, 0]] mod 17").unwrap();

        assert!(mat_1.inverse_prime().is_none());
        assert!(mat_2.inverse_prime().is_none());
    }

    /// Ensure that a matrix that has a determinant of `0` yields `None` on inversion.
    #[test]
    fn inv_none_det_zero() {
        let mat = MatZq::from_str("[[2, 0],[0, 0]] mod 11").unwrap();

        assert!(mat.inverse_prime().is_none());
    }

    /// Ensure that the function panics if a matrix with a non prime modulus is given as input.
    #[test]
    #[should_panic]
    fn not_prime_error() {
        let mat = MatZq::from_str("[[2, 0],[0, 2]] mod 10").unwrap();

        let _inv = mat.inverse_prime().unwrap();
    }
}

#[cfg(test)]
mod test_gauss {
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Test whether `gaussian_elimination_prime` works correctly.
    #[test]
    fn gauss_works() {
        let mat_1 = MatZq::from_str("[[5, 2, 1, 0],[2, 1, 0, 1]] mod 7").unwrap();
        let mat_2 =
            MatZq::from_str("[[1, 3, 1, 9],[1, 1, 130, 1],[3, 11, 5, 35]] mod 131").unwrap();
        let mat_3 =
            MatZq::from_str("[[5, 0, 2, 1, 0],[5, 0, 2, 1, 0],[2, 0, 1, 0, 1]] mod 7").unwrap();

        let gauss_1 = mat_1.gaussian_elimination_prime();
        let gauss_2 = mat_2.gaussian_elimination_prime();
        let gauss_3 = mat_3.gaussian_elimination_prime();

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
        let mat_1 = MatZq::from_str("[[5, 2, 1, 0],[2, 1, 0, 1]] mod 10").unwrap();
        let _ = mat_1.gaussian_elimination_prime();
    }
}
