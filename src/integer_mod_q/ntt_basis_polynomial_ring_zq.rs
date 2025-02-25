// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`NTTBasisPolynomialRingZq`] serves as an optional context object for
//! [`PolynomialRingZq`](super::PolynomialRingZq). If it is set for the matrix, then the multiplication of polynomials
//! is performed using the NTT, and otherwise the multiplication is kept as it is.

use super::{Modulus, Zq};
pub use from::ConvolutionType;

mod from;
mod intt;
mod ntt;

/// [`NTTBasisPolynomialRingZq`] is an object, that given a polynomial
/// `X^n - 1 mod q` or `X^n + 1 mod q` computes two transformation functions.
/// With these functions, one can utilize efficient matrix multiplication O(n log n) instead of
/// O(n^2) in the trivial polynomial multiplication for [`PolynomialRingZq`](super::PolynomialRingZq) objects.
///
/// Currently this implementation *only* supports `n` that are a power of two.
///
/// Attributes:
/// - `n`: the degree of the modulus polynomials
/// - `n_inv`: the inverse of `n` when viewed `modulo q`
/// - `powers_of_omega`: contains a list of `n` elements, corresponding to the `n` powers of
///     of the `n`th root of unity
/// - `powers_of_omega`: contains a list of `n` elements, corresponding to the `n` powers of
///     of the inverse of the `n`th root of unity
/// - `powers_of_psi`: contains a list of `n` elements, corresponding to the `n` powers of
///     of the `2n`th root of unity (empty for positively wrapped convolutions)
/// - `powers_of_psi`: contains a list of `n` elements, corresponding to the `n` powers of
///     of the inverse of the `2n`th root of unity (empty for positively wrapped convolutions)
/// - `modulus`: a clone of the modulus object the transform is connected to
/// - `convolution_type`: tells subsequet algorithms if the convolution is positively or negatively wrapped
///
/// # Examples
/// This example is taken from: <https://eprint.iacr.org/2024/585.pdf> Example 3.8
/// ```
/// use qfall_math::integer_mod_q::*;
/// use std::str::FromStr;
///
/// let modulus = Modulus::from(7681);
/// let poly_mod = ModulusPolynomialRingZq::from_str("5  -1 0 0 0 1 mod 7681").unwrap();
/// let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
/// let h_poly = PolyOverZq::from_str("4  5 6 7 8 mod 7681").unwrap();
///
/// let ntt_basis = NTTBasisPolynomialRingZq::init(4, 3383, &modulus, ConvolutionType::Cyclic);
///
/// let ghat = ntt_basis.ntt(&g_poly);
/// let hhat = ntt_basis.ntt(&h_poly);
///
/// // simulate entrywise mutliplication
/// let mut ghat_hhat = Vec::new();
/// for i in 0..4 {
///     ghat_hhat.push(&ghat[i] * &hhat[i]);
/// }
///
/// let g_h_poly = ntt_basis.intt(ghat_hhat);
///
/// let g_h_poly_ring = PolynomialRingZq::from((
///     g_h_poly.get_representative_least_nonnegative_residue(),
///     &poly_mod,
/// ));
///
/// // Ensure that multiplication using the NTT and multiplication using
/// // FLINTs multiplication algorithms yield the same result.
/// let g_poly_ring = PolynomialRingZq::from((
///     g_poly.get_representative_least_nonnegative_residue(),
///     &poly_mod,
/// ));
/// let h_poly_ring = PolynomialRingZq::from((
///     h_poly.get_representative_least_nonnegative_residue(),
///     &poly_mod,
/// ));
///
/// assert_eq!(g_poly_ring * h_poly_ring, g_h_poly_ring)
/// ```
///
/// This example is taken from: <https://eprint.iacr.org/2024/585.pdf> Example 3.12
/// ```
/// use qfall_math::integer_mod_q::*;
/// use std::str::FromStr;
///
/// let modulus = Modulus::from(7681);
/// let poly_mod = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 7681").unwrap();
/// let g_poly = PolyOverZq::from_str("4  1 2 3 4 mod 7681").unwrap();
/// let h_poly = PolyOverZq::from_str("4  5 6 7 8 mod 7681").unwrap();
///
/// let ntt_basis =
///     NTTBasisPolynomialRingZq::init(4, 1925, &modulus, ConvolutionType::Negacyclic);
///
/// let ghat = ntt_basis.ntt(&g_poly);
/// let hhat = ntt_basis.ntt(&h_poly);
///
/// // simulate entrywise mutliplication
/// let mut ghat_hhat = Vec::new();
/// for i in 0..4 {
///     ghat_hhat.push(&ghat[i] * &hhat[i])
/// }
///
/// let g_h_poly = ntt_basis.intt(ghat_hhat);
///
/// let g_h_poly_ring = PolynomialRingZq::from((
///     g_h_poly.get_representative_least_nonnegative_residue(),
///     &poly_mod,
/// ));
///
/// // Ensure that multiplication using the NTT and multiplication using
/// // FLINTs multiplication algorithms yield the same result.
/// let g_poly_ring = PolynomialRingZq::from((
///     g_poly.get_representative_least_nonnegative_residue(),
///     &poly_mod,
/// ));
/// let h_poly_ring = PolynomialRingZq::from((
///     h_poly.get_representative_least_nonnegative_residue(),
///     &poly_mod,
/// ));
///
/// assert_eq!(g_poly_ring * h_poly_ring, g_h_poly_ring)
/// ```
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
