// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`NTTBasisPolynomialRingZq`] serves as an optional context object for
//! [`PolynomialRingZq`]. If it is set for the matrix, then the multiplication of polynomials
//! is performed using the NTT transform, and otherwise the multiplication is kept as it is.

use super::{MatZq, Modulus, Zq};
use crate::traits::{Pow, SetEntry};

/// [`NTTBasisPolynomialRingZq`] is an object, that given a polynomial
/// `X^n - 1 mod q` computes two transformation matrices.
/// With these matrices, one can utilize efficient matrix multiplication O(n log n) instead of
/// O(n^2) in the trivial polynomial multiplication for [`PolynomialRingZq`] objects.
/// This implementation currently only supports cyclotomic polynomials, where there is an `n`-th root of unity.
///
/// Attributes:
/// - `ntt_matrix`: describes the conversion matrix to transform a polynomial in coefficient representation into ntt format
/// - `ntt_matrix_inv`: the inverse of the previous conversion matrix
#[derive(Debug)]
pub struct NTTBasisPolynomialRingZq {
    pub ntt_matrix: MatZq,
    pub ntt_matrix_inv: MatZq,
}

impl NTTBasisPolynomialRingZq {
    /// Given a cyclotomic polynomial `X^n - 1 mod q` with `n`-th root of unity `root_of_unity`, it computes the
    /// ntt matrix transform and its inverse operation.
    ///
    /// Parameters:
    /// - `n`: the degree of the polynomial
    /// - `root_of_unity`: the `n`-th root of unity
    /// - `q`: the modulus of the cyclotomic polynomial
    pub fn init(n: i64, root_of_unity: &Zq, q: &Modulus) -> Self {
        // construct ntt matrix matrix based on root of unity
        let mut ntt_matrix = MatZq::new(n, n, q);
        let roots: Vec<Zq> = (0..n).map(|i| root_of_unity.pow(i).unwrap()).collect();

        for row in 0..n {
            for column in 0..n {
                let entry = roots[row as usize].pow(column).unwrap();
                ntt_matrix.set_entry(row, column, entry).unwrap()
            }
        }

        // construct inverse of the ntt matrix
        let mut ntt_matrix_inv = MatZq::new(n, n, q);
        let n_inv = Zq::from((n, q)).inverse().unwrap();
        let root_of_unity_inv = root_of_unity.inverse().unwrap();
        let roots: Vec<Zq> = (0..n).map(|i| root_of_unity_inv.pow(i).unwrap()).collect();
        for row in 0..n {
            for column in 0..n {
                let entry = &n_inv * roots[row as usize].pow(column).unwrap();
                ntt_matrix_inv.set_entry(row, column, entry).unwrap()
            }
        }

        Self {
            ntt_matrix,
            ntt_matrix_inv,
        }
    }
}

#[cfg(test)]
mod test_ntt_basis_transformation {
    use super::NTTBasisPolynomialRingZq;
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{
            MatZq, Modulus, ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq, Zq,
        },
        traits::{FromCoefficientEmbedding, GetEntry, IntoCoefficientEmbedding, SetEntry},
    };
    use std::str::FromStr;

    /// This parameters and matrix are taken from: https://eprint.iacr.org/2024/585.pdf Example 3.4
    #[test]
    fn example_34_matrix() {
        let modulus = Modulus::from(7681);
        let root_of_unity = Zq::from((3383, &modulus));

        let ntt_basis = NTTBasisPolynomialRingZq::init(4, &root_of_unity, &modulus);

        let cmp_matrix_ntt = MatZq::from_str("[[1, 1, 1, 1],[1, 3383, 7680, 4298],[1, 7680, 1, 7680],[1, 4298, 7680, 3383]] mod 7681").unwrap();
        let cmp_matrix_ntt_inv = MatZq::from_str("[[5761, 5761, 5761, 5761],[5761, 4915, 1920, 2766],[5761, 1920, 5761, 1920],[5761, 2766, 1920, 4915]] mod 7681").unwrap();
        assert_eq!(cmp_matrix_ntt, ntt_basis.ntt_matrix);
        assert_eq!(cmp_matrix_ntt_inv, ntt_basis.ntt_matrix_inv);
        assert!((ntt_basis.ntt_matrix_inv * ntt_basis.ntt_matrix).is_identity())
    }

    /// This example is taken from: https://eprint.iacr.org/2024/585.pdf Example 3.4
    #[test]
    fn example_34_multiplication_with_ntt() {
        let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
        let modulus = Modulus::from(7681);
        let root_of_unity = Zq::from((3383, &modulus));

        let ntt_basis = NTTBasisPolynomialRingZq::init(4, &root_of_unity, &modulus);

        let g = g_poly.into_coefficient_embedding(4);
        let cmp_g = MatZq::from_str("[[1],[2],[3],[4]] mod 7681").unwrap();
        assert_eq!(cmp_g, g);

        let ghat = ntt_basis.ntt_matrix * g;
        let cmp_ghat = MatZq::from_str("[[10],[913],[7679],[6764]] mod 7681").unwrap();
        assert_eq!(cmp_ghat, ghat);
    }

    /// This example is taken from: https://eprint.iacr.org/2024/585.pdf Example 3.6
    /// Ensures that multiplication utilizing the transform and multiplication notusing the transform
    /// have the same result
    #[test]
    fn example_36_multiplication_with_ntt() {
        let modulus = Modulus::from(7681);
        // todo: after the cyclotomic polynomial instantiation is added, replace the instantiation of this polynomial
        let poly_mod = ModulusPolynomialRingZq::from_str("5  -1 0 0 0 1 mod 7681").unwrap();
        let g_poly = PolyOverZ::from_str("4  1 2 3 4").unwrap();
        let h_poly = PolyOverZ::from_str("4  5 6 7 8").unwrap();
        let root_of_unity = Zq::from((3383, &modulus));

        let ntt_basis = NTTBasisPolynomialRingZq::init(4, &root_of_unity, &modulus);

        let g = g_poly.into_coefficient_embedding(4);
        let h = h_poly.into_coefficient_embedding(4);

        let ghat = &ntt_basis.ntt_matrix * g;
        let hhat = &ntt_basis.ntt_matrix * h;

        // simulate entrywise mutliplication
        // todo: after we have entrywise multiplication for vectors, remove this
        let mut ghat_hhat = MatZq::new(4, 1, &modulus);
        for i in 0..4 {
            let ghat_i: Zq = ghat.get_entry(i, 0).unwrap();
            let hhat_i: Zq = hhat.get_entry(i, 0).unwrap();
            ghat_hhat.set_entry(i, 0, ghat_i * hhat_i).unwrap();
        }

        let g_h = ntt_basis.ntt_matrix_inv * ghat_hhat;

        let g_h_poly = PolyOverZq::from_coefficient_embedding(&g_h);
        // todo: after we can instantiate Polynomialringzq also with polyzq, change this here
        let g_h_poly_ring = PolynomialRingZq::from((
            g_h_poly.get_representative_least_nonnegative_residue(),
            &poly_mod,
        ));

        // Ensure that multiplication using the NTT transform and multiplication using
        // FLINTs multiplication algorithms yield the same result.
        let g_poly_ring = PolynomialRingZq::from((g_poly, &poly_mod));
        let h_poly_ring = PolynomialRingZq::from((h_poly, &poly_mod));
        assert_eq!(g_poly_ring * h_poly_ring, g_h_poly_ring)
    }
}
