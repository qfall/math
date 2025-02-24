// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to perform the NTT-transform for [`PolyOverZq`]
//! in the respective polynomialring
//!
//! The explicit functions contain the documentation.

use super::{from::ConvolutionType, NTTBasisPolynomialRingZq};
use crate::{
    integer::Z,
    integer_mod_q::{PolyOverZq, Zq},
    utils::index::bit_reverse_permutation,
};
use flint_sys::fmpz_mod::{fmpz_mod_add, fmpz_mod_ctx, fmpz_mod_mul, fmpz_mod_sub};

impl NTTBasisPolynomialRingZq {
    /// For a given polynomial viewed in the polynomial ring defined by the `self`, it computes the NTT-transform.
    ///
    /// It computes the iterative Cooley-Tukey transformation algorithm to compute the transform.
    /// Polynomials of degree smaller than `n-1` are with `0` coefficients.
    ///
    /// Parameters:
    /// - `poly`: The polynomial for which it is desired to compute the NTT-form
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer_mod_q::Modulus;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    /// use qfall_math::integer_mod_q::NTTBasisPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ConvolutionType;
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
    ///     Zq::from((10, &modulus)),
    ///     Zq::from((913, &modulus)),
    ///     Zq::from((7679, &modulus)),
    ///     Zq::from((6764, &modulus)),
    /// ];
    /// assert_eq!(cmp_ghat, ghat);
    /// ```
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer_mod_q::Modulus;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    /// use qfall_math::integer_mod_q::NTTBasisPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ConvolutionType;
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
    ///     Zq::from((1467, &modulus)),
    ///     Zq::from((2807, &modulus)),
    ///     Zq::from((3471, &modulus)),
    ///     Zq::from((7621, &modulus)),
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
    pub fn ntt(&self, poly: &PolyOverZq) -> Vec<Zq> {
        assert!(poly.get_degree() <= self.n);
        assert_eq!(poly.get_mod(), self.modulus);
        // we use the unsafe getter, because we know that all indices are in the range
        // and no error can occur here
        let mut poly_coeffs: Vec<Zq> = (0..self.n)
            .map(|i| unsafe { poly.get_coeff_unsafe(i) })
            .collect();
        for _ in poly.get_degree()..(self.n - 1) {
            poly_coeffs.push(Zq {
                value: Z::default(),
                modulus: self.modulus.clone(),
            });
        }

        // Negacyclic: perform preprocessing
        if self.convolution_type == ConvolutionType::Negacyclic {
            for i in 0..poly_coeffs.len() {
                unsafe {
                    fmpz_mod_mul(
                        &mut poly_coeffs[i].value.value,
                        &poly_coeffs[i].value.value,
                        &self.powers_of_psi[i].value.value,
                        self.modulus.get_fmpz_mod_ctx_struct(),
                    );
                }
            }
        }

        iterative_ntt(poly_coeffs, &self.powers_of_omega)
    }
}

/// This function essentially computes the included butterliy computations for each provided
/// chunk.
/// The chunk is double the size of the stride.
/// The computation currently performs the standard butterly operation from Cooley-Tukey
unsafe fn ntt_stride_steps(
    chunk: &mut [&mut Z],
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
fn iterative_ntt(coefficients: Vec<Zq>, powers_of_omega: &[Zq]) -> Vec<Zq> {
    let n = coefficients.len();
    let nr_iterations = n.ilog2() as i64;

    // compute the bit reversed order of the coefficients
    let mut res = coefficients;
    bit_reverse_permutation(&mut res);
    let modulus_pointer = powers_of_omega[0].modulus.get_fmpz_mod_ctx_struct();
    let mut res_z: Vec<&mut Z> = res.iter_mut().map(|x| &mut x.value).collect();
    let powers_of_omega_pointers: Vec<&Z> = powers_of_omega.iter().map(|x| &x.value).collect();

    let mut power_pointer: i64 = nr_iterations - 1;
    let mut stride = 1;
    // iterate through all layers
    while stride < n {
        // split into strides and perform action for each respective stride
        // !!! currently the multi-threading is turned off, because it is slower... !!!
        // if stride >= n {
        // res_z.par_chunks_mut(2 * stride).for_each(|chunk| unsafe {
        //     ntt_stride_steps(
        //         chunk,
        //         stride,
        //         power_pointer,
        //         modulus_pointer,
        //         &powers_of_omega_pointers,
        //     )
        // });
        // } else {
        res_z.chunks_mut(2 * stride).for_each(|chunk| unsafe {
            ntt_stride_steps(
                chunk,
                stride,
                power_pointer,
                modulus_pointer,
                &powers_of_omega_pointers,
            )
        });
        // }
        stride *= 2;
        power_pointer -= 1;
    }
    res
}
