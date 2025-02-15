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

use itertools::{Either, Itertools};

use super::{MatZq, Modulus, PolyOverZq, Zq};
use crate::{
    integer::Z,
    traits::{GetCoefficient, GetEntry, GetNumRows, Pow, SetCoefficient, SetEntry},
};

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
    pub n: i64,
    pub n_inv: Zq,
    pub roots_of_unity: Vec<Zq>,
    pub roots_of_unity_inv: Vec<Zq>,
    pub modulus: Modulus,
}

fn recursive_fft(
    coefficients: Vec<&Zq>,
    roots_of_unity: &Vec<Zq>,
    depth: usize,
    modulus: &Modulus,
) -> Vec<Zq> {
    if coefficients.len() == 1 {
        return vec![coefficients[0].clone()];
    }
    // separate into even and uneven coefficients
    let (even, mut uneven): (Vec<&Zq>, Vec<&Zq>) =
        coefficients
            .iter()
            .enumerate()
            .partition_map(|(index, value)| {
                if index % 2 == 0 {
                    Either::Left(value)
                } else {
                    Either::Right(value)
                }
            });
    // pad if the number of elements is uneven
    let padding = Zq::from((Z::ZERO, modulus));
    if even.len() != uneven.len() {
        uneven.push(&padding);
    }
    // recursively perform fft
    let even = recursive_fft(even, roots_of_unity, depth * 2, modulus);
    let uneven = recursive_fft(uneven, roots_of_unity, depth * 2, modulus);
    let mut out = vec![Zq::from((Z::ZERO, modulus)); even.len() + uneven.len()];

    // compute final entries
    let mut twindle_factor = Zq::from((Z::ONE, modulus));
    for i in 0..even.len() {
        let t = &twindle_factor * &uneven[i];
        out[i] = &even[i] + &t;
        out[i + even.len()] = &even[i] - &t;
        twindle_factor = twindle_factor * &roots_of_unity[depth];
    }
    out
}

impl NTTBasisPolynomialRingZq {
    pub fn ntt(&self, poly: &PolyOverZq) -> MatZq {
        let mut out = MatZq::new(self.n, 1, &self.modulus);

        let poly_coeffs: Vec<Zq> = (0..self.n).map(|i| poly.get_coeff(i).unwrap()).collect();
        let borrowed_coeffs: Vec<&Zq> = poly_coeffs.iter().collect();

        let res = recursive_fft(borrowed_coeffs, &self.roots_of_unity, 1, &self.modulus);
        for i in 0..self.n {
            out.set_entry(i, 0, &res[i as usize]).unwrap()
        }

        out
    }

    pub fn intt(&self, vector: &MatZq) -> PolyOverZq {
        assert!(vector.is_column_vector());
        assert!(vector.get_num_rows() == self.n);

        let coeffs: Vec<Zq> = (0..self.n)
            .map(|i| vector.get_entry(i, 0).unwrap())
            .collect();
        let borrowed_coeffs: Vec<&Zq> = coeffs.iter().collect();

        let res = recursive_fft(borrowed_coeffs, &self.roots_of_unity_inv, 1, &self.modulus);

        // call fft, but with the powers of the inverse of the root of unity
        // and at last, multiply each new entry with `n_inv`
        let mut out = PolyOverZq::from(&self.modulus);
        for i in 0..self.n {
            out.set_coeff(i, &self.n_inv * &res[i as usize]).unwrap()
        }

        out
    }

    /// Given a cyclotomic polynomial `X^n - 1 mod q` with `n`-th root of unity `root_of_unity`, it computes the
    /// ntt matrix transform and its inverse operation.
    ///
    /// Parameters:
    /// - `n`: the degree of the polynomial
    /// - `root_of_unity`: the `n`-th root of unity
    /// - `q`: the modulus of the cyclotomic polynomial
    pub fn init(n: i64, root_of_unity: &Zq, modulus: &Modulus) -> Self {
        // construct ntt matrix matrix based on root of unity
        let roots: Vec<Zq> = (0..n).map(|i| root_of_unity.pow(i).unwrap()).collect();

        let n_inv = Zq::from((n, modulus)).inverse().unwrap();
        let root_of_unity_inv = root_of_unity.inverse().unwrap();
        let roots_inv: Vec<Zq> = (0..n).map(|i| root_of_unity_inv.pow(i).unwrap()).collect();

        Self {
            n,
            n_inv,
            roots_of_unity: roots,
            roots_of_unity_inv: roots_inv,
            modulus: modulus.clone(),
        }
    }
}

#[cfg(test)]
mod test_ntt_basis_transformation {
    use super::NTTBasisPolynomialRingZq;
    use crate::{
        integer_mod_q::{
            MatZq, Modulus, ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq, Zq,
        },
        traits::{GetEntry, SetEntry},
    };
    use std::str::FromStr;

    /// This example is taken from: https://eprint.iacr.org/2024/585.pdf Example 3.4
    #[test]
    fn example_34_multiplication_with_ntt() {
        let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
        let modulus = Modulus::from(7681);
        let root_of_unity = Zq::from((3383, &modulus));

        let ntt_basis = NTTBasisPolynomialRingZq::init(4, &root_of_unity, &modulus);

        let ghat = ntt_basis.ntt(&g_poly);
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
        let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
        let h_poly = PolyOverZq::from_str("4  5 6 7 8 mod 7681").unwrap();
        let root_of_unity = Zq::from((3383, &modulus));

        let ntt_basis = NTTBasisPolynomialRingZq::init(4, &root_of_unity, &modulus);

        let ghat = ntt_basis.ntt(&g_poly);
        let hhat = ntt_basis.ntt(&h_poly);

        // simulate entrywise mutliplication
        // todo: after we have entrywise multiplication for vectors, remove this
        let mut ghat_hhat = MatZq::new(4, 1, &modulus);
        for i in 0..4 {
            let ghat_i: Zq = ghat.get_entry(i, 0).unwrap();
            let hhat_i: Zq = hhat.get_entry(i, 0).unwrap();
            ghat_hhat.set_entry(i, 0, ghat_i * hhat_i).unwrap();
        }

        let g_h_poly = ntt_basis.intt(&ghat_hhat);

        // todo: after we can instantiate Polynomialringzq also with polyzq, change this here
        let g_h_poly_ring = PolynomialRingZq::from((
            g_h_poly.get_representative_least_nonnegative_residue(),
            &poly_mod,
        ));

        // Ensure that multiplication using the NTT transform and multiplication using
        // FLINTs multiplication algorithms yield the same result.
        let g_poly_ring = PolynomialRingZq::from((
            g_poly.get_representative_least_nonnegative_residue(),
            &poly_mod,
        ));
        let h_poly_ring = PolynomialRingZq::from((
            h_poly.get_representative_least_nonnegative_residue(),
            &poly_mod,
        ));
        assert_eq!(g_poly_ring * h_poly_ring, g_h_poly_ring)
    }
}
