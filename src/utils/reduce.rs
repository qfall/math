// Copyright © 2026 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to reduce a [`MatPolynomialRingZq`] with the
//! [`ModulusPolynomialRingZq`](crate::integer_mod_q::ModulusPolynomialRingZq).
//! Only contains internal functions for reductions.

use flint_sys::{
    fmpz::{fmpz_submul, fmpz_zero},
    fmpz_mod::{fmpz_mod_ctx_struct, fmpz_mod_set_fmpz},
    fmpz_mod_poly::fmpz_mod_poly_struct,
    fmpz_poly::fmpz_poly_struct,
};
use std::cmp::min;

/// This is a manual implementation of the [sparse degree reduction
/// from FLINT](https://github.com/flintlib/flint/blob/2016a99ae45608e513c1b2094d37a1c3ea9c0c67/src/fq/reduce.c#L75)
/// for `fq` objects.
/// The sparse reduction works for any context object.
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
/// let entry = unsafe { fmpz_poly_mat_entry(&poly_ring_mat.matrix.matrix, 0, 0) };
/// if (unsafe { *entry }).length > 0 {
///     unsafe {
///         internal_reduce(
///             &mut *entry,
///             ((*entry).length - 1) as usize,
///             &poly_ring_mat.modulus.modulus.poly,
///             poly_ring_mat.modulus.get_degree() as usize,
///             poly_ring_mat.modulus.get_q_as_modulus().get_fmpz_mod_ctx_struct(),
///             &poly_ring_mat.modulus.non_zero,
///         )
///     }
///     unsafe {
///         _fmpz_poly_normalise(entry);
///     };
/// }
/// ```
pub(crate) unsafe fn internal_reduce(
    poly: &mut fmpz_poly_struct,
    nr_coeffs_poly: usize,
    modulus_polynomial: &fmpz_mod_poly_struct,
    nr_coeffs_modulus_poly: usize,
    modulus: &fmpz_mod_ctx_struct,
    non_zero: &Vec<usize>,
) {
    let (poly_len, modulus_polynomial_len) = (nr_coeffs_poly, nr_coeffs_modulus_poly);

    if poly_len >= modulus_polynomial_len {
        for i in (modulus_polynomial_len..=poly_len).rev() {
            for k in non_zero {
                unsafe {
                    fmpz_submul(
                        (poly.coeffs).add((i - modulus_polynomial_len) + k),
                        poly.coeffs.add(i),
                        modulus_polynomial.coeffs.add(*k),
                    )
                };
            }
            unsafe { fmpz_zero(poly.coeffs.add(i)) };
        }
    }

    for i in 0..=min(poly_len, modulus_polynomial_len - 1) {
        unsafe { fmpz_mod_set_fmpz(poly.coeffs.add(i), poly.coeffs.add(i), modulus) };
    }
}
