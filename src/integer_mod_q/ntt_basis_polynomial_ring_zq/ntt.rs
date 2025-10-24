// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to perform the NTT for [`PolyOverZq`]
//! in the respective polynomial ring.
//! The implementation mostly follows the description in <https://higashi.blog/2023/06/23/ntt-02/>.
//!
//! The explicit functions contain the documentation.

use super::{from::ConvolutionType, NTTBasisPolynomialRingZq};
use crate::{
    integer::Z,
    integer_mod_q::{PolyOverZq, Zq},
    traits::GetCoefficient,
    utils::index::bit_reverse_permutation,
};
use flint_sys::fmpz_mod::{fmpz_mod_add, fmpz_mod_ctx, fmpz_mod_mul, fmpz_mod_sub};

impl NTTBasisPolynomialRingZq {
    /// For a given polynomial viewed in the polynomial ring defined by the `self`, it computes the NTT.
    ///
    /// It computes the iterative Cooley-Tukey transformation algorithm to compute the transform.
    /// Polynomials of degree smaller than `n-1` are with `0` coefficients.
    ///
    /// Parameters:
    /// - `poly`: The polynomial for which it is desired to compute the NTT
    ///
    /// Returns the NTT of a polynomial in the context of the polynomial ring.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::{Modulus, PolyOverZq, NTTBasisPolynomialRingZq, ConvolutionType};
    /// use std::str::FromStr;
    ///
    /// let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
    /// let modulus = Modulus::from(7681);
    ///
    /// let ntt_basis =
    ///     NTTBasisPolynomialRingZq::init(4, 3383, &modulus, ConvolutionType::Cyclic);
    ///
    /// let ghat = ntt_basis.ntt(&g_poly);
    ///
    /// let cmp_ghat = vec![
    ///     Z::from(10),
    ///     Z::from(913),
    ///     Z::from(7679),
    ///     Z::from(6764),
    /// ];
    /// assert_eq!(cmp_ghat, ghat);
    /// ```
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::{Modulus, PolyOverZq, NTTBasisPolynomialRingZq, ConvolutionType};
    /// use std::str::FromStr;
    ///
    /// let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
    /// let modulus = Modulus::from(7681);
    ///
    /// let ntt_basis =
    ///     NTTBasisPolynomialRingZq::init(4, 1925, &modulus, ConvolutionType::Negacyclic);
    ///
    /// let ghat = ntt_basis.ntt(&g_poly);
    ///
    /// let cmp_ghat = vec![
    ///     Z::from(1467),
    ///     Z::from(2807),
    ///     Z::from(3471),
    ///     Z::from(7621),
    /// ];
    /// assert_eq!(cmp_ghat, ghat);
    /// ```
    ///
    /// # Panics if ...
    /// - it is not reduced, i.e. has a coefficient of degree > n
    /// - the modulus differs from the modulus over which we view the polynomial
    ///
    /// The algorithm is based on the Cooley-Tukey algorithm:
    /// -\[1\] Cooley, James W., and John W. Tukey.
    ///     "An algorithm for the machine calculation of complex Fourier series."
    ///     Mathematics of computation 19.90 (1965): 297-301.
    pub fn ntt(&self, poly: &PolyOverZq) -> Vec<Z> {
        assert!(poly.get_degree() < self.n);
        assert_eq!(poly.get_mod(), self.modulus);
        // we use the unsafe getter, because we know that all indices are in the range
        // and no error can occur here
        let mut poly_coeffs: Vec<Z> = (0..self.n)
            .map(|i| unsafe { poly.get_coeff_unchecked(i) })
            .collect();
        for _ in poly_coeffs.len()..(self.n as usize) {
            poly_coeffs.push(Z::default());
        }

        // Negacyclic: perform preprocessing
        if self.convolution_type == ConvolutionType::Negacyclic {
            for (i, x) in poly_coeffs.iter_mut().enumerate() {
                unsafe {
                    fmpz_mod_mul(
                        &mut x.value,
                        &x.value,
                        &self.powers_of_psi[i].value.value,
                        self.modulus.get_fmpz_mod_ctx_struct(),
                    );
                }
            }
        }

        iterative_ntt(poly_coeffs, &self.powers_of_omega)
    }
}

/// This function essentially computes the included butterfly computations for each provided
/// chunk.
/// The chunk is double the size of the stride.
/// The computation currently performs the standard butterfly operation from Cooley-Tukey
unsafe fn ntt_stride_steps(
    chunk: &mut [Z],
    stride: usize,
    power_pointer: i64,
    modulus_pointer: &fmpz_mod_ctx,
    powers_of_omega_pointers: &[&Z],
) {
    for i in 0..stride {
        // compute power of the current level
        let current_power = powers_of_omega_pointers[2_usize.pow(power_pointer as u32) * (i)];

        // CT butterfly
        // by using Z, we can manage not to initialize additional modulus objects in this part
        // and save runtime
        let mut temp = Z::default();

        unsafe {
            fmpz_mod_mul(
                &mut temp.value,
                &current_power.value,
                &chunk[i + stride].value,
                modulus_pointer,
            );
            fmpz_mod_sub(
                &mut chunk[i + stride].value,
                &chunk[i].value,
                &temp.value,
                modulus_pointer,
            );
            fmpz_mod_add(
                &mut chunk[i].value,
                &chunk[i].value,
                &temp.value,
                modulus_pointer,
            )
        }
    }
}

/// This algorithm performs an iterative version of the Cooley-Tukey algorithm.
/// It takes in the coefficients of the polynomial and the precomputed powers of the
/// root of unity.
/// Here, we assume that precomputation has been done, i.e.: if the algorithm is
/// called for negatively wrapped convolution, then this has been accounted for in the previous algorithm.
///
/// The algorithm possesses the option to be multi-threaded, but benchmarking has shown,
/// that it makes the algorithm less efficient, so we turned it off.
fn iterative_ntt(coefficients: Vec<Z>, powers_of_omega: &[Zq]) -> Vec<Z> {
    let n = coefficients.len();
    let nr_iterations = n.ilog2() as i64;

    // compute the bit reversed order of the coefficients
    let mut res = coefficients;
    bit_reverse_permutation(&mut res);
    let modulus_pointer = powers_of_omega[0].modulus.get_fmpz_mod_ctx_struct();
    let powers_of_omega_pointers: Vec<&Z> = powers_of_omega.iter().map(|x| &x.value).collect();

    let mut power_pointer: i64 = nr_iterations - 1;
    let mut stride = 1;
    // iterate through all layers
    while stride < n {
        // split into strides and perform action for each respective stride
        res.chunks_mut(2 * stride).for_each(|chunk| unsafe {
            ntt_stride_steps(
                chunk,
                stride,
                power_pointer,
                modulus_pointer,
                &powers_of_omega_pointers,
            )
        });
        stride *= 2;
        power_pointer -= 1;
    }
    res
}

#[cfg(test)]
mod test_ntt {
    use crate::{
        integer::Z,
        integer_mod_q::{ConvolutionType, Modulus, NTTBasisPolynomialRingZq, PolyOverZq},
    };
    use std::str::FromStr;

    /// This example is taken from: https://eprint.iacr.org/2024/585.pdf Example 3.4
    #[test]
    fn example_34_multiplication_with_ntt() {
        let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
        let modulus = Modulus::from(7681);

        let ntt_basis = NTTBasisPolynomialRingZq::init(4, 3383, &modulus, ConvolutionType::Cyclic);

        let ghat = ntt_basis.ntt(&g_poly);
        let cmp_ghat = vec![Z::from(10), Z::from(913), Z::from(7679), Z::from(6764)];
        assert_eq!(cmp_ghat, ghat);
    }

    /// Ensure that NTT panics, if the degree of the polynomial is too high, i.e. not reduced.
    #[test]
    #[should_panic]
    fn degree_too_high() {
        let g_poly = PolyOverZq::from_str("5  1 2 3 4 5 mod 7681").unwrap();
        let modulus = Modulus::from(7681);

        let ntt_basis = NTTBasisPolynomialRingZq::init(4, 3383, &modulus, ConvolutionType::Cyclic);

        let _ = ntt_basis.ntt(&g_poly);
    }

    /// Ensure that NTT panics, if the modulus of the polynomial is different
    #[test]
    #[should_panic]
    fn different_modulus() {
        let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
        let modulus = Modulus::from(7682);

        let ntt_basis = NTTBasisPolynomialRingZq::init(4, 3383, &modulus, ConvolutionType::Cyclic);

        let _ = ntt_basis.ntt(&g_poly);
    }

    /// Ensure that NTT works for smaller degree polynomials
    #[test]
    fn small_degree() {
        let g_poly = PolyOverZq::from_str("2  1 2 mod 7681").unwrap();
        let modulus = Modulus::from(7681);

        let ntt_basis =
            NTTBasisPolynomialRingZq::init(4, 1925, &modulus, ConvolutionType::Negacyclic);

        let ghat = ntt_basis.ntt(&g_poly);
        let cmp_ghat = vec![Z::from(3851), Z::from(5256), Z::from(3832), Z::from(2427)];
        assert_eq!(cmp_ghat, ghat);
    }
}
