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

use super::{Modulus, PolyOverZq, Zq};
use crate::{integer::Z, traits::Pow};
use flint_sys::{
    fmpz::fmpz_swap,
    fmpz_mod::{fmpz_mod_add, fmpz_mod_mul, fmpz_mod_sub, fmpz_mod_sub_fmpz},
};

/// [`NTTBasisPolynomialRingZq`] is an object, that given a polynomial
/// `X^n - 1 mod q` or `X^n + 1 mod q` computes two transformation functions.
/// With these functions, one can utilize efficient matrix multiplication O(n log n) instead of
/// O(n^2) in the trivial polynomial multiplication for [`PolynomialRingZq`] objects.
/// This implementation currently only supports cyclotomic polynomials, where there is an `n`/2n-th root of unity.
///
/// Attributes:
/// - todo
#[derive(Debug)]
pub struct NTTBasisPolynomialRingZq {
    pub n: i64,
    pub n_inv: Zq,
    pub powers_of_omega: Vec<Zq>,
    pub powers_of_omega_inv: Vec<Zq>,
    pub powers_of_psi: Vec<Zq>,
    pub powers_of_psi_inv: Vec<Zq>,
    pub modulus: Modulus,
    pub convolution_type: ConvolutionType,
}

// Helper function to compute bit-reversed index
fn bit_reverse(mut x: usize, log_n: usize) -> usize {
    let mut res = 0;
    for _ in 0..log_n {
        res = (res << 1) | (x & 1);
        x >>= 1;
    }
    res
}

// Applies bit-reversed permutation to the input array
fn bit_reverse_permutation<T>(a: &mut Vec<T>) {
    let n = a.len();
    let log_n = n.trailing_zeros() as usize;

    for i in 0..n {
        let rev_i = bit_reverse(i, log_n);
        if i < rev_i {
            a.swap(i, rev_i);
        }
    }
}

fn iterative_ntt(coefficients: Vec<Zq>, powers_of_omega: &[Zq]) -> Vec<Zq> {
    let n = coefficients.len();
    let nr_iterations = n.ilog2() as i64;

    // compute the bit reversed order of the coefficients
    let mut res = coefficients;
    bit_reverse_permutation(&mut res);

    let mut power_pointer: i64 = nr_iterations - 1;
    let mut stride = 1;
    // iterate through all layers
    while stride < n {
        for start in (0..n).step_by(2 * stride) {
            // each pair of butterfly operations
            for i in start..(start + stride) {
                let current_pwer =
                    &powers_of_omega[2_usize.pow(power_pointer as u32) * (i - start)];

                // CT butterfly
                let mut temp = Z::default();
                unsafe {
                    fmpz_mod_mul(
                        &mut temp.value,
                        &current_pwer.value.value,
                        &res[i + stride].value.value,
                        res[0].modulus.get_fmpz_mod_ctx_struct(),
                    );
                    fmpz_mod_sub(
                        &mut res[i + stride].value.value,
                        &res[i].value.value,
                        &temp.value,
                        res[0].modulus.get_fmpz_mod_ctx_struct(),
                    );
                    fmpz_mod_add(
                        &mut res[i].value.value,
                        &res[i].value.value,
                        &temp.value,
                        res[0].modulus.get_fmpz_mod_ctx_struct(),
                    )
                }
            }
        }
        stride *= 2;
        power_pointer -= 1;
    }
    res
}

fn iterative_intt(coefficients: Vec<Zq>, powers_of_omega_inv: &Vec<Zq>, n_inv: &Zq) -> Vec<Zq> {
    let n = coefficients.len();

    let mut res = coefficients;

    let mut power_pointer = 0;
    let mut stride = n / 2;
    // iterate through all layers
    while stride > 0 {
        for start in (0..n).step_by(2 * stride) {
            // each pair of butterfly operations
            for i in start..(start + stride) {
                // compute power of the current level
                let current_power =
                    &powers_of_omega_inv[2_usize.pow(power_pointer as u32) * (i - start)];

                // CT butterfly
                // by using Z, we can manage not to initialize additional modulus objects in this part
                // and save runtime
                let mut temp = Z::default();
                unsafe {
                    fmpz_mod_add(
                        &mut temp.value,
                        &res[i].value.value,
                        &res[i + stride].value.value,
                        res[0].modulus.get_fmpz_mod_ctx_struct(),
                    );
                    fmpz_mod_sub_fmpz(
                        &mut res[i + stride].value.value,
                        &res[i].value.value,
                        &res[i + stride].value.value,
                        res[0].modulus.get_fmpz_mod_ctx_struct(),
                    );
                    fmpz_mod_mul(
                        &mut res[i + stride].value.value,
                        &mut res[i + stride].value.value,
                        &current_power.value.value,
                        res[0].modulus.get_fmpz_mod_ctx_struct(),
                    );
                    fmpz_swap(&mut res[i].value.value, &mut temp.value)
                };
            }
        }

        stride /= 2;
        power_pointer += 1;
    }

    // compute the bit reversed order of the coefficients
    bit_reverse_permutation(&mut res);
    for i in 0..res.len() {
        unsafe { res[i].mul_mut_unsafe(n_inv) };
    }
    res
}

impl NTTBasisPolynomialRingZq {
    /// todo
    pub fn ntt(&self, poly: &PolyOverZq) -> Vec<Zq> {
        // we use the unsafe getter, because we know that all indices are in the range
        // and no error can occur here
        let mut poly_coeffs: Vec<Zq> = (0..self.n)
            .map(|i| unsafe { poly.get_coeff_unsafe(i) })
            .collect();
        // todo: pad coefficients if it is not dividable by 2

        // Negacyclic: perform preprocessing
        if self.convolution_type == ConvolutionType::Negacyclic {
            for i in 0..poly_coeffs.len() {
                unsafe { poly_coeffs[i].mul_mut_unsafe(&self.powers_of_psi[i]) };
            }
        }

        iterative_ntt(poly_coeffs, &self.powers_of_omega)
    }

    /// todo
    pub fn intt(&self, vector: Vec<Zq>) -> PolyOverZq {
        // todo: pad coefficients if it is not dividable by 2

        let mut res = iterative_intt(vector, &self.powers_of_omega_inv, &self.n_inv);

        // Negacyclic: perform postprocessing
        if self.convolution_type == ConvolutionType::Negacyclic {
            for i in 0..res.len() {
                unsafe { res[i].mul_mut_unsafe(&self.powers_of_psi_inv[i]) };
            }
        }

        let mut out = PolyOverZq::from(self.modulus.clone());
        for (i, x) in res.iter().enumerate() {
            unsafe {
                // we know that the entry is reduced, and that it only addresses correct
                // entries
                out.set_coefficient_unsafe(i as i64, &x.value)
            }
        }

        out
    }

    /// Given a cyclotomic polynomial `X^n - 1 mod q` with `n`-th root of unity `root_of_unity`, it computes the
    /// ntt matrix transform and its inverse operation.
    ///
    /// Parameters:
    /// - `n`: the degree of the polynomial
    /// - `root_of_unity`: the `n`-th or `2n`-th root of unity
    /// - `q`: the modulus of the cyclotomic polynomial
    /// - `convolution_type`: defines whether convolution is cyclic or negacyclic
    ///
    /// # Examples
    /// ```
    /// todo
    /// ```
    pub fn init(
        n: i64,
        root_of_unity: &Zq,
        modulus: &Modulus,
        convolution_type: &ConvolutionType,
    ) -> Self {
        // construct ntt matrix matrix based on root of unity
        let n_inv = Zq::from((n, modulus)).inverse().unwrap();
        let root_of_unity_inv = root_of_unity.inverse().unwrap();

        let (psi, psi_inv, omega, omega_inv) = match convolution_type {
            ConvolutionType::Cyclic => (None, None, root_of_unity.clone(), root_of_unity_inv),
            ConvolutionType::Negacyclic => (
                Some(root_of_unity),
                Some(&root_of_unity_inv),
                root_of_unity.pow(2).unwrap(),
                root_of_unity.pow(-2).unwrap(),
            ),
        };

        let powers_of_omega = (0..n).map(|i| omega.pow(i).unwrap()).collect();
        let powers_of_omega_inv = (0..n).map(|i| omega_inv.pow(i).unwrap()).collect();

        let powers_of_psi = match convolution_type {
            ConvolutionType::Cyclic => Vec::new(),
            ConvolutionType::Negacyclic => (0..n).map(|i| psi.unwrap().pow(i).unwrap()).collect(),
        };
        let powers_of_psi_inv = match convolution_type {
            ConvolutionType::Cyclic => Vec::new(),
            ConvolutionType::Negacyclic => {
                (0..n).map(|i| psi_inv.unwrap().pow(i).unwrap()).collect()
            }
        };

        Self {
            n,
            n_inv,
            powers_of_omega,
            powers_of_omega_inv,
            powers_of_psi,
            powers_of_psi_inv,
            modulus: root_of_unity.get_mod(),
            convolution_type: convolution_type.clone(),
        }
    }
}

/// todo
#[derive(Debug, Clone, PartialEq)]
pub enum ConvolutionType {
    Cyclic,
    Negacyclic,
}

#[cfg(test)]
mod test_ntt_basis_transformation {
    use super::NTTBasisPolynomialRingZq;
    use crate::integer_mod_q::{
        ntt_basis_polynomial_ring_zq::ConvolutionType, Modulus, ModulusPolynomialRingZq,
        PolyOverZq, PolynomialRingZq, Zq,
    };
    use std::str::FromStr;

    /// This example is taken from: https://eprint.iacr.org/2024/585.pdf Example 3.4
    #[test]
    fn example_34_multiplication_with_ntt() {
        let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
        let modulus = Modulus::from(7681);
        let root_of_unity = Zq::from((3383, &modulus));

        let ntt_basis =
            NTTBasisPolynomialRingZq::init(4, &root_of_unity, &modulus, &ConvolutionType::Cyclic);

        let ghat = ntt_basis.ntt(&g_poly);
        let cmp_ghat = vec![
            Zq::from((10, &modulus)),
            Zq::from((913, &modulus)),
            Zq::from((7679, &modulus)),
            Zq::from((6764, &modulus)),
        ];
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

        let ntt_basis =
            NTTBasisPolynomialRingZq::init(4, &root_of_unity, &modulus, &ConvolutionType::Cyclic);

        let ghat = ntt_basis.ntt(&g_poly);
        let hhat = ntt_basis.ntt(&h_poly);

        // simulate entrywise mutliplication
        // todo: after we have entrywise multiplication for vectors, remove this
        let mut ghat_hhat = Vec::new();
        for i in 0..4 {
            ghat_hhat.push(&ghat[i] * &hhat[i]);
        }

        let g_h_poly = ntt_basis.intt(ghat_hhat);

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

    /// This example is taken from: https://eprint.iacr.org/2024/585.pdf Example 3.8
    #[test]
    fn example_38_multiplication_with_ntt() {
        let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
        let modulus = Modulus::from(7681);
        let root_of_unity = Zq::from((1925, &modulus));

        let ntt_basis = NTTBasisPolynomialRingZq::init(
            4,
            &root_of_unity,
            &modulus,
            &ConvolutionType::Negacyclic,
        );

        let ghat = ntt_basis.ntt(&g_poly);

        assert_eq!(g_poly, ntt_basis.intt(ghat));
    }

    /// This example is taken from: https://eprint.iacr.org/2024/585.pdf Example 3.12
    /// Ensures that multiplication utilizing the transform and multiplication notusing the transform
    /// have the same result
    #[test]
    fn example_312_multiplication_with_ntt() {
        let modulus = Modulus::from(7681);
        let poly_mod = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 7681").unwrap();
        let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
        let h_poly = PolyOverZq::from_str("4  5 6 7 8 mod 7681").unwrap();
        let root_of_unity = Zq::from((1925, &modulus));

        let ntt_basis = NTTBasisPolynomialRingZq::init(
            4,
            &root_of_unity,
            &modulus,
            &ConvolutionType::Negacyclic,
        );

        let ghat = ntt_basis.ntt(&g_poly);
        let hhat = ntt_basis.ntt(&h_poly);

        // simulate entrywise mutliplication
        let mut ghat_hhat = Vec::new();
        for i in 0..4 {
            ghat_hhat.push(&ghat[i] * &hhat[i])
        }

        let g_h_poly = ntt_basis.intt(ghat_hhat);

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
