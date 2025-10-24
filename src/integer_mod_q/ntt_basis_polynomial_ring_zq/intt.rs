// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to compute the inverse of the
//! NTT-transform for [`PolyOverZq`] objects in the polynomial ring.
//! The implementation mostly follows the description in <https://higashi.blog/2023/06/23/ntt-02/>.
//!
//! The explicit functions contain the documentation.

use super::{from::ConvolutionType, NTTBasisPolynomialRingZq};
use crate::{
    integer::Z,
    integer_mod_q::{PolyOverZq, Zq},
    utils::index::bit_reverse_permutation,
};
use flint_sys::{
    fmpz::fmpz_swap,
    fmpz_mod::{fmpz_mod_add, fmpz_mod_ctx, fmpz_mod_mul, fmpz_mod_sub_fmpz},
    fmpz_mod_poly::fmpz_mod_poly_set_coeff_fmpz,
};

impl NTTBasisPolynomialRingZq {
    /// For a given polynomial viewed in the polynomial ring defined by the `self`, it computes the inverse NTT.
    ///
    /// It computes the iterative Gentleman-Sande transformation algorithm to compute the transform.
    ///
    /// Parameters:
    /// - `vector`: The coefficients of the polynomial when viewed in NTT.
    ///
    /// Returns the inverse of the NTT from a vector and returns it as a polynomial.
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
    /// let ghat_ntt = vec![
    ///     Z::from(10),
    ///     Z::from(913),
    ///     Z::from(7679),
    ///     Z::from(6764),
    /// ];
    ///
    /// let ghat_intt = ntt_basis.intt(ghat_ntt);
    ///
    /// assert_eq!(g_poly, ghat_intt);
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
    /// let ghat_ntt = vec![
    ///     Z::from(1467),
    ///     Z::from(2807),
    ///     Z::from(3471),
    ///     Z::from(7621),
    /// ];
    ///
    /// let ghat_intt = ntt_basis.intt(ghat_ntt);
    ///
    /// assert_eq!(g_poly, ghat_intt);
    /// ```
    ///
    /// # Panics if ...
    /// - it is not reduced, i.e. has a coefficient of degree > n
    /// - the modulus differs from the modulus over which we view the polynomial
    ///
    /// The algorithm is based on the Gentleman-Sande algorithm:
    /// -\[1\] Gentleman, W. Morven, and Gordon Sande.
    ///     "Fast fourier transforms: for fun and profit."
    ///     Proceedings of the November 7-10, 1966, fall joint computer conference. 1966.
    pub fn intt(&self, vector: Vec<Z>) -> PolyOverZq {
        assert_eq!(vector.len(), self.n as usize);
        let mut res = iterative_intt(vector, &self.powers_of_omega_inv, &self.n_inv);

        // Negacyclic: perform postprocessing
        if self.convolution_type == ConvolutionType::Negacyclic {
            for (i, x) in res.iter_mut().enumerate() {
                unsafe {
                    fmpz_mod_mul(
                        &mut x.value,
                        &x.value,
                        &self.powers_of_psi_inv[i].value.value,
                        self.modulus.get_fmpz_mod_ctx_struct(),
                    )
                };
            }
        }

        let mut out = PolyOverZq::from(self.modulus.clone());
        for (i, x) in res.iter().enumerate() {
            unsafe {
                fmpz_mod_poly_set_coeff_fmpz(
                    &mut out.poly,
                    i as i64,
                    &x.value,
                    self.modulus.get_fmpz_mod_ctx_struct(),
                );
            }
        }

        out
    }
}

/// This function essentially computes the included butterfly computations for each provided
/// chunk.
/// The chunk is double the size of the stride.
/// The computation currently performs the standard butterlfy operation from Gentleman-Sande.
unsafe fn intt_stride_steps(
    chunk: &mut [Z],
    stride: usize,
    power_pointer: usize,
    modulus_pointer: &fmpz_mod_ctx,
    powers_of_omega_inv_pointers: &[&Z],
) {
    for i in 0..stride {
        // compute power of the current level
        let current_power = powers_of_omega_inv_pointers[2_usize.pow(power_pointer as u32) * (i)];

        // GS butterfly
        // by using Z, we can manage not to initialize additional modulus objects in this part
        // and save runtime
        let mut temp = Z::default();
        unsafe {
            fmpz_mod_add(
                &mut temp.value,
                &chunk[i].value,
                &chunk[i + stride].value,
                modulus_pointer,
            );
            fmpz_mod_sub_fmpz(
                &mut chunk[i + stride].value,
                &chunk[i].value,
                &chunk[i + stride].value,
                modulus_pointer,
            );
            fmpz_mod_mul(
                &mut chunk[i + stride].value,
                &chunk[i + stride].value,
                &current_power.value,
                modulus_pointer,
            );
            fmpz_swap(&mut chunk[i].value, &mut temp.value)
        };
    }
}

/// This algorithm performs an iterative version of the Gentleman-Sande algorithm.
/// It takes in the coefficients of the polynomial and the precomputed powers of the
/// root of unity.
/// Here, we assume that precomputation has been done, i.e.: if the algorithm is
/// called for negatively wrapped convolution, then this has been accounted for in the previous algorithm.
///
/// The algorithm possesses the option to be multi-threaded, but benchmarking has shown,
/// that it makes the algorithm less efficient, so we turned it off.
fn iterative_intt(coefficients: Vec<Z>, powers_of_omega_inv: &[Zq], n_inv: &Zq) -> Vec<Z> {
    let n = coefficients.len();

    let mut res = coefficients;
    let modulus_pointer = n_inv.modulus.get_fmpz_mod_ctx_struct();
    let powers_of_omega_inv_pointers: Vec<&Z> =
        powers_of_omega_inv.iter().map(|x| &x.value).collect();

    let mut power_pointer = 0;
    let mut stride = n / 2;
    while stride > 0 {
        // split into strides and perform action for each respective stride
        res.chunks_mut(2 * stride).for_each(|chunk| unsafe {
            intt_stride_steps(
                chunk,
                stride,
                power_pointer,
                modulus_pointer,
                &powers_of_omega_inv_pointers,
            );
        });

        stride /= 2;
        power_pointer += 1;
    }

    // compute the bit reversed order of the coefficients
    bit_reverse_permutation(&mut res);
    for x in res.iter_mut() {
        unsafe {
            fmpz_mod_mul(
                &mut x.value,
                &x.value,
                &n_inv.value.value,
                n_inv.modulus.get_fmpz_mod_ctx_struct(),
            )
        }
    }
    res
}

#[cfg(test)]
mod test_intt {
    use std::str::FromStr;
    use crate::{integer::Z, integer_mod_q::{
        ConvolutionType, Modulus, NTTBasisPolynomialRingZq, PolyOverZq,
    }};

    /// Tests a loop of NTT and INTT application.
    #[test]
    fn example_loop_ntt_intt() {
        let poly = PolyOverZq::from_str("4  2532 2542 653 8 mod 7681").unwrap();
        let modulus = Modulus::from(7681);

        let ntt_basis = NTTBasisPolynomialRingZq::init(4, 3383, &modulus, ConvolutionType::Cyclic);

        assert_eq!(poly, ntt_basis.intt(ntt_basis.ntt(&poly)));
    }

    /// This example is taken from: https://eprint.iacr.org/2024/585.pdf Example 3.4
    #[test]
    fn example_34_intt() {
        let cmp_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
        let modulus = Modulus::from(7681);

        let ntt_basis = NTTBasisPolynomialRingZq::init(4, 3383, &modulus, ConvolutionType::Cyclic);

        let ghat = vec![
            Z::from(10),
            Z::from(913),
            Z::from(7679),
            Z::from(6764),
        ];
        let poly = ntt_basis.intt(ghat);
        assert_eq!(cmp_poly, poly);
    }

    /// Ensure that INTT panics, if the degree of the polynomial is too low compared to the number of provided entries.
    #[test]
    #[should_panic]
    fn degree_too_high() {
        let modulus = Modulus::from(7681);

        let ntt_basis =
            NTTBasisPolynomialRingZq::init(4, 1925, &modulus, ConvolutionType::Negacyclic);

        let ghat_ntt = vec![
            Z::from(1467,),
            Z::from(2807),
            Z::from(3471),
            Z::from(7621),
            Z::from(1),
        ];

        let _ = ntt_basis.intt(ghat_ntt);
    }

    /// Ensure that INTT works for smaller degree polynomials
    #[test]
    fn small_degree() {
        let cmp_poly = PolyOverZq::from_str("2  1 2 mod 7681").unwrap();
        let modulus = Modulus::from(7681);

        let ntt_basis =
            NTTBasisPolynomialRingZq::init(4, 1925, &modulus, ConvolutionType::Negacyclic);

        let ghat = vec![
            Z::from(3851),
            Z::from(5256),
            Z::from(3832),
            Z::from(2427),
        ];
        let poly = ntt_basis.intt(ghat);
        assert_eq!(cmp_poly, poly);
    }
}
