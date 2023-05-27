// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to reduce a [`MatPolynomialRingZq`] with the
//! [`ModulusPolynomialRingZq`](crate::integer_mod_q::ModulusPolynomialRingZq).
//!
//! **For Developers** note: The [`ModulusPolynomialRingZq`](crate::integer_mod_q::ModulusPolynomialRingZq)
//! is not applied automatically, and has to be called in the functions individually.
//! Additionally the comparisons assume that the entries are reduced,
//! hence no reduction is performed in the check.

use super::MatPolynomialRingZq;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::{fmpz_poly_mat::fmpz_poly_mat_entry, fq::fq_reduce};

impl MatPolynomialRingZq {
    /// This function manually applies the modulus
    /// [`ModulusPolynomialRingZq`](crate::integer_mod_q::ModulusPolynomialRingZq)
    /// to the given polynomial matrix [`MatPolyOverZ`](crate::integer::MatPolyOverZ)
    /// in the [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// poly_ring_mat.reduce()
    /// ```
    #[allow(dead_code)]
    pub(crate) fn reduce(&mut self) {
        for row_num in 0..self.matrix.get_num_rows() {
            for column_num in 0..self.matrix.get_num_columns() {
                unsafe {
                    let entry = fmpz_poly_mat_entry(&self.matrix.matrix, row_num, column_num);
                    fq_reduce(entry, self.modulus.get_fq_ctx_struct())
                };
            }
        }
    }
}

#[cfg(test)]
mod test_reduced {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{mat_polynomial_ring_zq::MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    const BITPRIME64: u64 = u64::MAX - 58;

    /// ensure that the entries are reduced
    #[test]
    fn reduces() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 11").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq {
            matrix: poly_mat,
            modulus,
        };

        let cmp_modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 11").unwrap();
        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  9 0 1, 1  9],[0, 2  1 2]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq {
            matrix: cmp_poly_mat.clone(),
            modulus: cmp_modulus,
        };

        // we only compare the parts individually, not under the modulus, hence they should not be the same
        // unless they have been reduced
        assert_ne!(poly_ring_mat.matrix, cmp_poly_mat);
        assert_ne!(poly_ring_mat, cmp_poly_ring_mat);

        poly_ring_mat.reduce();
        assert_eq!(poly_ring_mat.matrix, cmp_poly_mat);
        assert_eq!(poly_ring_mat, cmp_poly_ring_mat);
    }

    /// ensure that reduce works with large entries and moduli
    #[test]
    fn large_values() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  {} 0 0 1 mod {}", i64::MAX, BITPRIME64))
                .unwrap();
        let poly_mat =
            MatPolyOverZ::from_str(&format!("[[4  -1 0 {} 1, 1  42],[0, 2  1 2]]", i64::MAX))
                .unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq {
            matrix: poly_mat,
            modulus,
        };

        let cmp_modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  {} 0 0 1 mod {}", i64::MAX, BITPRIME64))
                .unwrap();
        let cmp_poly_mat = MatPolyOverZ::from_str(&format!(
            "[[3  {} 0 {}, 1  42],[0, 2  1 2]]",
            BITPRIME64 - i64::MAX as u64 - 1,
            i64::MAX
        ))
        .unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq {
            matrix: cmp_poly_mat.clone(),
            modulus: cmp_modulus,
        };

        // we only compare the parts individually, not under the modulus, hence they should not be the same
        // unless they have been reduced
        assert_ne!(poly_ring_mat.matrix, cmp_poly_mat);
        assert_ne!(poly_ring_mat, cmp_poly_ring_mat);

        poly_ring_mat.reduce();

        assert_eq!(poly_ring_mat.matrix, cmp_poly_mat);
        assert_eq!(poly_ring_mat, cmp_poly_ring_mat);
    }
}
