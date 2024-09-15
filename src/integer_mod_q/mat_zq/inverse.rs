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
    integer::Z,
    traits::{Concatenate, Gcd, GetNumRows},
};
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_rref;

impl MatZq {
    /// Returns the inverse of the matrix if it exists (is square and
    /// has a determinant co-prime to the modulus) and `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mut matrix = MatZq::from_str("[[1, 2],[3, 4]] mod 7").unwrap();
    ///
    /// let matrix_invert = matrix.inverse().unwrap();
    ///
    /// let id = &matrix_invert * &matrix;
    /// assert_eq!("[[5, 1],[5, 3]] mod 7", matrix_invert.to_string());
    /// assert!(id.is_identity());
    /// ```
    pub fn inverse(&self) -> Option<MatZq> {
        // Check if the matrix is square and compute the determinant.
        if let Ok(det) = self.get_mat().det() {
            // Check whether the square matrix is invertible or not.
            if det.gcd(self.get_mod()) != Z::ONE {
                None
            } else {
                let dimensions = self.get_num_rows();
                let mut inverse = MatZq::new(dimensions, dimensions, self.get_mod());

                // The i`th unit vector in the for loop.
                let mut e_i = MatZq::identity(dimensions, 1, self.get_mod());

                // Use solve for all unit vectors.
                for i in 0..dimensions {
                    if let Some(column_i) = self.solve_gaussian_elimination(&e_i) {
                        inverse.set_column(i, &column_i, 0).unwrap();
                    } else {
                        return None;
                    }

                    if i != dimensions - 1 {
                        e_i.swap_entries(i, 0, i + 1, 0).unwrap();
                    }
                }

                Some(inverse)
            }
        } else {
            None
        }
    }

    /// Returns the inverse of the matrix if it exists (is square and
    /// has a determinant unequal to `0`) and `None` otherwise.
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
    /// assert!(id.is_identity());
    /// ```
    ///
    /// # Panics ...
    /// - if the modulus is not prime.
    pub fn inverse_prime(&self) -> Option<MatZq> {
        assert!(
            self.get_mod().is_prime(),
            "The modulus of the matrix is not prime"
        );

        // Check if the matrix is square and compute the determinant.
        if let Ok(det) = self.get_mat().det() {
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
    use crate::{
        integer::Z,
        integer_mod_q::{MatZq, Modulus},
    };
    use std::str::FromStr;

    /// Test whether `inverse` correctly calculates an inverse matrix.
    #[test]
    fn inverse_works() {
        let mat = MatZq::from_str("[[5, 2],[2, 1]] mod 14").unwrap();

        let inv = mat.inverse().unwrap();

        let cmp_inv = MatZq::from_str("[[1, 12],[12, 5]] mod 14").unwrap();
        assert_eq!(cmp_inv, inv);
    }

    /// Check if the multiplication of inverse and matrix result in an identity matrix.
    #[test]
    fn inverse_correct() {
        let mat = MatZq::from_str("[[5, 2],[2, 1]] mod 8").unwrap();

        let inv = mat.inverse().unwrap();

        let diag = mat * inv;
        assert!(diag.is_identity());
    }

    /// Test whether `inverse` correctly calculates an inverse matrix of an identity.
    #[test]
    fn inverse_identity() {
        let mat = MatZq::identity(3, 3, 8);

        let inv = mat.inverse().unwrap();

        assert_eq!(mat, inv);
    }

    /// Test whether `inverse` correctly calculates an inverse matrix for big numbers.
    #[test]
    fn inverse_big() {
        let mat = MatZq::from_str(&format!("[[{}, 0],[0, 1]] mod {}", i64::MAX, u64::MAX)).unwrap();

        let inv = mat.inverse().unwrap();

        let cmp_inv =
            MatZq::from_str(&format!("[[{}, 0],[0, 1]] mod {}", u64::MAX - 2, u64::MAX)).unwrap();
        assert_eq!(cmp_inv, inv);
    }

    /// Ensure that a matrix that is not square yields `None` on inversion.
    #[test]
    fn inv_none_not_squared() {
        let mat_1 = MatZq::from_str("[[1, 0, 1],[0, 1, 1]] mod 4").unwrap();
        let mat_2 = MatZq::from_str("[[1, 0],[0, 1],[1, 0]] mod 82").unwrap();

        assert!(mat_1.inverse().is_none());
        assert!(mat_2.inverse().is_none());
    }

    /// Ensure that a matrix that has a determinant of `0` yields `None` on inversion.
    #[test]
    fn inv_none_det_zero() {
        let mat = MatZq::from_str("[[2, 0],[0, 0]] mod 12").unwrap();

        assert!(mat.inverse().is_none());
    }

    /// Ensure that a matrix that has a determinant co-prime to the modulus
    /// and not `0` yields `None` on inversion.
    #[test]
    fn inv_none_det_coprime() {
        let mat = MatZq::from_str("[[2, 0],[0, 2]] mod 4").unwrap();

        assert!(mat.inverse().is_none());
    }

    /// Ensure that a solution is found in random matrices (for testing purposes).
    #[test]
    #[ignore]
    fn random_matrix_modulus() {
        let mut none_count = 0;
        let mut correct_count = 0;
        let mut false_count = 0;

        for i in 0..10000 {
            let modulus_sample = Z::sample_uniform(2, 10000).unwrap();
            let row_sample = &Z::sample_uniform(1, 10).unwrap();

            let modulus = Modulus::from(modulus_sample);
            let mat = MatZq::sample_uniform(row_sample, row_sample, &modulus);
            if let Some(inverse) = mat.inverse() {
                let id = &mat * &inverse;

                if id == MatZq::identity(row_sample, row_sample, modulus) {
                    correct_count += 1;
                    println!("{}: Correct", i);
                } else {
                    false_count += 1;
                    println!("{}: False", i);
                }
            } else {
                none_count += 1;
                println!("{}: None", i);
            }
        }

        println!("Nones: {}", none_count);
        println!("Corrects: {}", correct_count);
        println!("False: {}", false_count);
    }
}

#[cfg(test)]
mod test_inverse_prime {
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Test whether `inverse_prime` correctly calculates an inverse matrix.
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
        assert!(diag.is_identity());
    }

    /// Check if the multiplication of inverse and matrix result in an identity matrix.
    #[test]
    fn inverse_correct_2() {
        let mat = MatZq::from_str("[[0, 2],[2, 1]] mod 3").unwrap();

        let inv = mat.inverse_prime().unwrap();

        let diag = mat * inv;
        assert!(diag.is_identity());
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
