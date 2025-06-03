// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations of basis reduction algorithms.

use super::MatZ;
use crate::{rational::Q, traits::MatrixDimensions};
use flint_sys::fmpz_mat::{fmpz_mat_is_reduced, fmpz_mat_lll_storjohann};

impl MatZ {
    /// Performs the (modified Storjohann) LLL algorithm on the matrix `self`.
    /// This algorithm expects `self` to be a basis.
    /// The reduced matrix is a (δ, η)-reduced basis.
    ///
    /// Let the matrix be [b_1, b_2, ..., b_n]. Then, it is (δ, η)-LLL-reduced if
    /// - for any i > j, we have |μ_{i,j}| <= η,
    /// - for any i < n, we have δ|b_i*|^2 <= |b_{i+1}* + μ_{i+1,i}b_i*|^2,
    ///
    /// where μ_{i,j} =〈b_i, b_j*〉/〈b_j*, b_j*〉and b_i* is the i-th vector
    /// of the Gram-Schmidt orthogonalization of our matrix.
    ///
    /// Parameters:
    /// - `delta`: mainly defines the quality of the reduced
    ///   basis with higher quality the closer it's chosen to 1.
    ///   Needs to be chosen between 0.25 < δ <= 1.
    /// - `eta`: defines the maximum deviation per vector
    ///   from the Gram-Schmidt orthogonalisation.
    ///   Needs to be chosen between 0.5 <= η < √δ.
    ///
    /// Choosing δ=0.99 and η=0.501 optimizes the quality of the basis and
    /// is a good choice to start from. Decreasing δ or increasing η will
    /// increase efficiency but decrease the quality of the reduced basis.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let mut matrix = MatZ::sample_uniform(2, 2, 0, 65537).unwrap();
    ///
    /// matrix.lll(0.75, 0.501);
    /// ```
    ///
    /// # Panics ...
    /// - if δ is not in (0.25, 1].
    /// - if η is not in [0.5, √δ).
    /// - if `self` can't be a basis, i.e. #rows < #columns.
    pub fn lll(&self, delta: impl Into<Q>, eta: impl Into<Q>) -> MatZ {
        let delta: Q = delta.into();
        let eta: Q = eta.into();

        if delta > Q::ONE || delta <= Q::from(0.25) {
            panic!("δ needs to be chosen between 0.25 < δ <= 1.");
        }
        if eta < Q::from(0.5) || eta >= delta.sqrt() {
            panic!("η needs to be chosen between 0.5 <= η < √δ.");
        }
        if self.get_num_rows() < self.get_num_columns() {
            panic!("The n-by-m matrix is required to form a basis, i.e. n can't be larger than m.");
        }

        // ensure that LLL operates on column vectors as basis vectors
        let mut transposed = self.transpose();
        unsafe {
            fmpz_mat_lll_storjohann(&mut transposed.matrix, &delta.value, &eta.value);
        };

        transposed.transpose()
    }

    /// Checks if the basis `self` is (δ, η)-reduced.
    ///
    /// Definition of (δ, η)-reduced:
    /// Let the matrix be [b_1, b_2, ..., b_n]. Then, it is (δ, η)-LLL-reduced if
    /// - for any i > j, we have |μ_{i,j}| <= η,
    /// - for any i < n, we have δ|b_i*|^2 <= |b_{i+1}* + μ_{i+1,i}b_i*|^2,
    ///
    /// where μ_{i,j} =〈b_i, b_j*〉/〈b_j*, b_j*〉and b_i* is the i-th vector
    /// of the Gram-Schmidt orthogonalization of our matrix.
    ///
    /// Parameters:
    /// - `delta`: mainly defines the quality of the reduced
    ///   basis with higher quality the closer it's chosen to 1.
    ///   If δ > 1, the output will always be `false`.
    /// - `eta`: defines the maximum deviation per vector
    ///   from the Gram-Schmidt orthogonalisation.
    ///   If η < 0, the output will always be `false`.
    ///
    /// If `self` has `|rows| > |columns|`, it can't be a basis and therefore,
    /// the output of this algorithm will always be `false`.
    ///
    /// Returns `true` if the matrix is a basis that is (δ, η)-reduced.
    /// Otherwise, it returns `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    ///
    /// let mut matrix = MatZ::sample_uniform(2, 2, 0, 65537).unwrap();
    /// matrix.lll(0.75, 0.501);
    ///
    /// let check = matrix.is_reduced(0.75, 0.501);
    ///
    /// assert!(check);
    /// ```
    pub fn is_reduced(&self, delta: impl Into<Q>, eta: impl Into<Q>) -> bool {
        let delta: Q = delta.into();
        let eta: Q = eta.into();
        let delta = f64::from(&delta);
        let eta = f64::from(&eta);

        // ensure that LLL-check operates on column vectors as basis vectors
        let transposed = self.transpose();

        0 != unsafe { fmpz_mat_is_reduced(&transposed.matrix, delta, eta) }
    }
}

#[cfg(test)]
mod test_lll {
    use crate::integer::MatZ;

    /// Ensure that a (0.99, 0.501)-LLL-reduced matrix is (0.99, 0.501)-reduced.
    #[test]
    fn reduction_works() {
        let mat = MatZ::sample_uniform(5, 4, 0, 257).unwrap();

        let reduced_mat = mat.lll(0.99, 0.501);

        assert!(reduced_mat.is_reduced(0.99, 0.501));
    }

    /// Ensure that a (0.75, 0.75)-LLL-reduced matrix is (0.75, 0.75)-reduced
    /// for large numbers.
    #[test]
    fn large_number() {
        let mat = MatZ::sample_uniform(3, 3, i64::MAX, u64::MAX).unwrap();

        let reduced_mat = mat.lll(0.75, 0.75);

        assert!(reduced_mat.is_reduced(0.75, 0.75));
    }

    /// Ensures that choosing δ <= 0.25 will result in a panic.
    #[test]
    #[should_panic]
    fn small_delta() {
        let mat = MatZ::identity(2, 2);

        mat.lll(0.25, 0.501);
    }

    /// Ensures that choosing δ > 1 will result in a panic.
    #[test]
    #[should_panic]
    fn large_delta() {
        let mat = MatZ::identity(3, 5);

        mat.lll(1.01, 0.501);
    }

    /// Ensures that choosing η < 0.5 will result in a panic.
    #[test]
    #[should_panic]
    fn small_eta() {
        let mat = MatZ::identity(2, 2);

        mat.lll(0.75, 0.499);
    }

    /// Ensures that choosing η > √δ will result in a panic.
    #[test]
    #[should_panic]
    fn large_eta() {
        let mat = MatZ::identity(4, 4);

        mat.lll(0.75, 0.867);
    }

    /// Ensures that choosing the number of rows smaller than the number of columns results in a panic.
    #[test]
    #[should_panic]
    fn not_basis() {
        let mat = MatZ::identity(3, 4);

        mat.lll(0.75, 0.75);
    }
}

#[cfg(test)]
mod test_is_reduced {
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensure that the identity matrix is optimally reduced.
    #[test]
    fn identity_reduced() {
        let mat = MatZ::identity(4, 4);

        assert!(mat.is_reduced(1.0, 0.0));
    }

    /// Ensure that a (0.75, 0.75)-LLL-reduced matrix is (0.75, 0.75)-reduced.
    #[test]
    fn reduced_lll() {
        let mat = MatZ::sample_uniform(3, 3, 0, 257).unwrap();
        let reduced_mat = mat.lll(0.75, 0.75);

        assert!(reduced_mat.is_reduced(0.75, 0.75));
    }

    /// Ensures that a fixed matrix that was previously uniformly generated within [0,257)
    /// is not (0.75, 0.75)-reduced.
    #[test]
    fn not_reduced() {
        let mat = MatZ::from_str("[[55, 115, 28],[115, 86, 60],[134, 141, 67]]").unwrap();

        assert!(!mat.is_reduced(0.75, 0.75));
    }

    /// Ensures that [`MatZ::is_reduced`] always outputs `false`
    /// for nonsense parameters, i.e.
    /// - δ > 1,
    /// - η < 0,
    /// - #rows > #columns.
    #[test]
    fn nonsense_parameters() {
        let square_mat = MatZ::identity(2, 2);
        let non_square_mat = MatZ::identity(2, 3);

        assert!(!square_mat.is_reduced(1.01, 0.75));
        assert!(!square_mat.is_reduced(0.75, -0.01));
        assert!(!non_square_mat.is_reduced(0.75, 0.75));
    }
}
