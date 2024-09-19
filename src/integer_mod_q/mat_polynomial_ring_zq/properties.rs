// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`MatPolynomialRingZq`] instances.

use super::MatPolynomialRingZq;

impl MatPolynomialRingZq {
    /// Checks if a [`MatPolynomialRingZq`] is the identity matrix.
    ///
    /// Returns `true` if every diagonal entry of the  matrix is
    /// the constant polynomial `1` and all other entries are `0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, PolyOverZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = PolyOverZq::from_str("5  1 0 0 0 1 mod 17").unwrap();
    /// let id_mat = MatPolyOverZ::identity(2, 2);
    ///
    /// let poly_ring_mat = MatPolynomialRingZq::from((id_mat, modulus));
    /// assert!(poly_ring_mat.is_identity());
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, PolyOverZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = PolyOverZq::from_str("5  1 0 0 0 1 mod 17").unwrap();
    /// let id_mat = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1],[0, 0]]").unwrap();
    ///
    /// let poly_ring_mat = MatPolynomialRingZq::from((id_mat, modulus));
    /// assert!(poly_ring_mat.is_identity());
    /// ```
    pub fn is_identity(&self) -> bool {
        self.matrix.is_identity()
    }

    /// Checks if a [`MatPolynomialRingZq`] is a square matrix.
    ///
    /// Returns `true` if the number of rows and columns is identical.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, PolyOverZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = PolyOverZq::from_str("5  1 0 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[1  13, 0],[2  1 1, 1  1]]").unwrap();
    ///
    /// let poly_ring_mat = MatPolynomialRingZq::from((poly_mat, modulus));
    /// assert!(poly_ring_mat.is_square());
    /// ```
    pub fn is_square(&self) -> bool {
        self.matrix.is_square()
    }

    /// Checks if every entry of a [`MatPolynomialRingZq`] is `0`.
    ///
    /// Returns `true` if every entry is `0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, PolyOverZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = PolyOverZq::from_str("5  1 0 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::new(2,2);
    ///
    /// let poly_ring_mat = MatPolynomialRingZq::from((poly_mat, modulus));
    /// assert!(poly_ring_mat.is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        self.matrix.is_zero()
    }
}

#[cfg(test)]
mod test_is_identity {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, PolyOverZq},
    };
    use std::str::FromStr;

    /// Ensure that is_identity returns `true` for identity matrices.
    #[test]
    fn identity_detection() {
        let modulus = PolyOverZq::from_str("5  1 0 0 0 1 mod 17").unwrap();

        let ident_1 = MatPolynomialRingZq::identity(2, 2, &modulus);
        let ident_2 = MatPolynomialRingZq::identity(2, 3, modulus);

        assert!(ident_1.is_identity());
        assert!(ident_2.is_identity());
    }

    /// Ensure that is_identity returns `false` for non-identity matrices.
    #[test]
    fn identity_rejection() {
        let modulus = PolyOverZq::from_str(&format!("5  1 0 0 0 1 mod {}", u64::MAX)).unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[0, 0],[0, 1  2]]").unwrap();
        let poly_mat_2 =
            MatPolyOverZ::from_str(&format!("[[1  1, 0],[2  1 {}, 1  1]]", i64::MAX)).unwrap();

        let small = MatPolynomialRingZq::from((poly_mat_1, &modulus));
        let large = MatPolynomialRingZq::from((poly_mat_2, modulus));

        assert!(!small.is_identity());
        assert!(!large.is_identity());
    }
}

#[cfg(test)]
mod test_is_zero {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, PolyOverZq},
    };
    use std::str::FromStr;

    /// Ensure that is_zero returns `true` for all zero matrices.
    #[test]
    fn zero_detection() {
        let modulus = PolyOverZq::from_str("5  1 0 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::new(2, 2);
        let poly_mat_2 = MatPolyOverZ::new(4, 2);

        let zero_1 = MatPolynomialRingZq::from((poly_mat_1, &modulus));
        let zero_2 = MatPolynomialRingZq::from((poly_mat_2, modulus));

        assert!(zero_1.is_zero());
        assert!(zero_2.is_zero());
    }

    /// Ensure that is_zero returns `false` for non-zero matrices.
    #[test]
    fn zero_rejection() {
        let modulus = PolyOverZq::from_str(&format!("5  1 0 0 0 1 mod {}", u64::MAX)).unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[0, 0],[0, 1  2]]").unwrap();
        let poly_mat_2 =
            MatPolyOverZ::from_str(&format!("[[1  1, 0],[2  1 {}, 0]]", i64::MAX)).unwrap();

        let small = MatPolynomialRingZq::from((poly_mat_1, &modulus));
        let large = MatPolynomialRingZq::from((poly_mat_2, modulus));

        assert!(!small.is_zero());
        assert!(!large.is_zero());
    }
}

#[cfg(test)]
mod test_is_square {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, PolyOverZq},
    };
    use std::str::FromStr;

    /// Ensure that is_square returns `true` for square matrices.
    #[test]
    fn square_detection() {
        let modulus = PolyOverZq::from_str("5  1 0 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[1  3, 0],[0, 2  7 1]]").unwrap();
        let poly_mat_2 =
            MatPolyOverZ::from_str("[[0, 1  1, 2  2 3],[0, 0, 1  15],[0, 0, 0]]").unwrap();

        let square_1 = MatPolynomialRingZq::from((poly_mat_1, &modulus));
        let square_2 = MatPolynomialRingZq::from((poly_mat_2, modulus));

        assert!(square_1.is_square());
        assert!(square_2.is_square());
    }

    /// Ensure that is_square returns `false` for non-square matrices.
    #[test]
    fn square_rejection() {
        let modulus = PolyOverZq::from_str(&format!("5  1 0 0 0 1 mod {}", u64::MAX)).unwrap();
        let poly_mat_1 = MatPolyOverZ::new(1, 2);
        let poly_mat_2 =
            MatPolyOverZ::from_str(&format!("[[1  1, 0, 1  7],[2  1 {}, 0, 0]]", i64::MAX))
                .unwrap();

        let small = MatPolynomialRingZq::from((poly_mat_1, &modulus));
        let large = MatPolynomialRingZq::from((poly_mat_2, modulus));

        assert!(!small.is_square());
        assert!(!large.is_square());
    }
}
