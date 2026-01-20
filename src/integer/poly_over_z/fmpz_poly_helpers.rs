// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains helpful functions on [`fmpz_poly_struct`].

use super::PolyOverZ;
use flint_sys::{
    fmpz::{fmpz, fmpz_is_one, fmpz_is_zero, fmpz_submul, fmpz_zero},
    fmpz_mod::{fmpz_mod_ctx_struct, fmpz_mod_set_fmpz},
    fmpz_mod_poly::fmpz_mod_poly_struct,
    fmpz_poly::{_fmpz_poly_normalise, fmpz_poly_struct},
};
use std::cmp::min;

/// Reduces an [`fmpz_poly_struct`] instance by a [`PolyOverZ`].
/// The modulus must have a leading coefficient of `1`, else the function will panic.
/// Also assumes that `poly` is nonzero.
///
/// Parameters:
/// - `poly`: Specifies the polynomial which is reduced
/// - `modulus`: Specifies the polynomial by which `poly` is reduced
///
/// # Examples
/// ```compile_fail
/// use crate::integer::{
///     poly_over_z::fmpz_poly_helpers::reduce_fmpz_poly_by_poly_over_z, PolyOverZ,
/// };
/// use std::str::FromStr;
///
/// let mut a = PolyOverZ::from_str("4  0 1 2 3").unwrap();
/// let modulus = PolyOverZ::from_str("3  0 1 1").unwrap();
///
/// unsafe { reduce_fmpz_poly_by_poly_over_z(&mut a.poly, &modulus) }
///
/// assert_eq!(PolyOverZ::from_str("2  0 2").unwrap(), a);
/// ```
///
/// # Panics ...
/// - if the modulus does not have a leading coefficient of `1`.
pub(crate) unsafe fn reduce_fmpz_poly_by_poly_over_z(
    poly: &mut fmpz_poly_struct,
    modulus: &PolyOverZ,
) {
    let modulus_nr_coeff = modulus.get_degree() as usize;

    assert!(
        1 == unsafe { fmpz_is_one(modulus.poly.coeffs.add(modulus_nr_coeff)) },
        "In order to reduce, the modulus must have a leading coefficient of 1."
    );

    let non_zero: Vec<usize> = (0..modulus_nr_coeff)
        .filter(|i| unsafe { 0 == fmpz_is_zero(modulus.poly.coeffs.add(*i)) })
        .collect();

    unsafe {
        reduce_fmpz_poly_by_fmpz_poly_sparse(
            poly.coeffs,
            poly.length as usize,
            modulus.poly.coeffs,
            modulus.poly.length as usize,
            &non_zero,
        );
    }

    poly.length = min(poly.length, modulus.poly.length - 1);
    unsafe { _fmpz_poly_normalise(poly) };
}

/// This is a manual implementation of the [sparse degree reduction
/// from FLINT](https://github.com/flintlib/flint/blob/2016a99ae45608e513c1b2094d37a1c3ea9c0c67/src/fq/reduce.c#L75)
/// for `fq` objects.
/// It assumes that the leading coefficient of the context polynomial is `1`.
/// Assumes that `poly` is non-empty, i.e., not the constant `0` polynomial.
/// The function normalises after, i.e., it changes the length of the polynomial by removing
/// the leading zero coefficients.
///
/// Parameters:
/// - `poly_coeffs`: a list with all the coefficients of the polynomial
/// - `modulus_polynomial_coeffs`: a list with all the coefficients of the modulus polynomial
/// - `non_zero`: a list with the indices where modulus_polynomial_coeffs is non_zero
///   (the leading coefficient is assumed to be 1 and does not need to be provided)
/// - `modulus`: the modulus that is applied to each coefficient
///
/// # Examples
/// ```compile_fail
/// use crate::{
///     integer::{MatPolyOverZ, fmpz_poly_helpers::reduce_fmpz_poly_by_fmpz_poly_sparse},
///     integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
/// };
/// use flint_sys::{fmpz_poly::_fmpz_poly_normalise, fmpz_poly_mat::fmpz_poly_mat_entry};
/// use std::str::FromStr;
/// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
/// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
/// let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
/// let entry = unsafe { fmpz_poly_mat_entry(&poly_ring_mat.matrix.matrix, 0, 0) };
/// if (unsafe { *entry }).length > 0 {
///     unsafe {
///         reduce_fmpz_poly_by_fmpz_poly_sparse(
///             (*entry).coeffs,
///             (*entry).length as usize,
///             poly_ring_mat.modulus.modulus.poly.coeffs,
///             (poly_ring_mat.modulus.get_degree() + 1) as usize,
///             &poly_ring_mat.modulus.non_zero,
///         )
///     }
///     unsafe {
///         _fmpz_poly_normalise(entry);
///     };
/// }
/// ```
pub(crate) unsafe fn reduce_fmpz_poly_by_fmpz_mod_poly_sparse(
    poly: &mut fmpz_poly_struct,
    modulus_poly: &fmpz_mod_poly_struct,
    non_zero: &Vec<usize>,
    modulus: &fmpz_mod_ctx_struct,
) {
    let poly_len = poly.length as usize;
    let modulus_poly_len = modulus_poly.length as usize;

    unsafe {
        reduce_fmpz_poly_by_fmpz_poly_sparse(
            poly.coeffs,
            poly_len,
            modulus_poly.coeffs,
            modulus_poly_len,
            non_zero,
        )
    };

    for i in 0..min(poly_len, modulus_poly_len - 1) {
        unsafe { fmpz_mod_set_fmpz(poly.coeffs.add(i), poly.coeffs.add(i), modulus) };
    }

    poly.length = min(poly_len, modulus_poly_len - 1) as i64;
    unsafe { _fmpz_poly_normalise(poly) };
}

/// This is a manual implementation of the [sparse degree reduction
/// from FLINT](https://github.com/flintlib/flint/blob/2016a99ae45608e513c1b2094d37a1c3ea9c0c67/src/fq/reduce.c#L75)
/// for `fq` objects.
/// This only performs the degree reduction step.
/// It assumes that the leading coefficient of the context polynomial is `1`.
/// Assumes that poly_coeffs is non-empty, i.e., not the constant `0` polynomial.
/// This function does not normalise, i.e., remove leading zero coefficients.
///
/// Parameters:
/// - `poly_coeffs`: a list with all the coefficients of the polynomial
/// - `poly_len`: the total number of coefficients of the polynomial
/// - `modulus_polynomial_coeffs`: a list with all the coefficients of the modulus polynomial
/// - `modulus_polynomial_len`: the total number of coefficients of the modulus polynomial
/// - `non_zero`: a list with the indices where modulus_polynomial_coeffs is non_zero (the leading coefficient is assumed to be 1 and does not need to be provided)
///
/// # Examples
/// ```compile_fail
/// use crate::{
///     integer::{MatPolyOverZ, fmpz_poly_helpers::reduce_fmpz_poly_by_fmpz_poly_sparse},
///     integer_mod_q::{ModulusPolynomialRingZq},
/// };
/// use flint_sys::{fmpz_poly::_fmpz_poly_normalise, fmpz_poly_mat::fmpz_poly_mat_entry};
/// use std::str::FromStr;
///
/// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
/// let mut poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
/// let entry = unsafe { fmpz_poly_mat_entry(&poly_mat.matrix, 0, 0) };
/// if (unsafe { *entry }).length > 0 {
///     unsafe {
///         reduce_fmpz_poly_by_fmpz_poly_sparse(
///             (*entry).coeffs,
///             (*entry).length as usize,
///             modulus.modulus.poly.coeffs,
///             (modulus.get_degree() + 1) as usize,
///             &modulus.non_zero,
///         )
///     }
///     unsafe {
///         _fmpz_poly_normalise(entry);
///     };
/// }
/// let cmp_poly_mat = MatPolyOverZ::from_str("[[3  -2 0 1, 1  42],[0, 2  1 2]]").unwrap();
/// assert_eq!(cmp_poly_mat, poly_mat)
/// ```
pub(crate) unsafe fn reduce_fmpz_poly_by_fmpz_poly_sparse(
    poly_coeffs: *mut fmpz,
    poly_len: usize,
    modulus_polynomial_coeffs: *mut fmpz,
    modulus_polynomial_len: usize,
    non_zero: &Vec<usize>,
) {
    let (poly_len, modulus_polynomial_len) = (poly_len - 1, modulus_polynomial_len - 1);
    if poly_len >= modulus_polynomial_len {
        for i in (modulus_polynomial_len..=poly_len).rev() {
            for k in non_zero {
                unsafe {
                    fmpz_submul(
                        poly_coeffs.add((i - modulus_polynomial_len) + k),
                        poly_coeffs.add(i),
                        modulus_polynomial_coeffs.add(*k),
                    )
                };
            }
            unsafe { fmpz_zero(poly_coeffs.add(i)) };
        }
    }
}

#[cfg(test)]
mod test_reduce_fmpz_poly_by_poly_over_z {
    use crate::integer::{
        PolyOverZ, poly_over_z::fmpz_poly_helpers::reduce_fmpz_poly_by_poly_over_z,
    };
    use std::str::FromStr;

    /// Ensures that the reduction works properly for a fixed polynomial that has to be
    /// reduce or more than one coefficient.
    #[test]
    fn reduce_more_than_once() {
        let mut a = PolyOverZ::from_str("4  0 1 2 3").unwrap();
        let modulus = PolyOverZ::from_str("3  0 1 1").unwrap();

        unsafe { reduce_fmpz_poly_by_poly_over_z(&mut a.poly, &modulus) }

        assert_eq!(PolyOverZ::from_str("2  0 2").unwrap(), a);
    }

    /// Ensures that the function panics, if the leading coefficient is not `1`.
    #[test]
    #[should_panic]
    fn no_leading_zero() {
        let mut a = PolyOverZ::from_str("3  1 2 3").unwrap();
        let modulus = PolyOverZ::from_str("2  1 2").unwrap();

        unsafe { reduce_fmpz_poly_by_poly_over_z(&mut a.poly, &modulus) }
    }

    /// Ensures that large coefficients are reduced properly.
    #[test]
    fn large_coefficients() {
        let mut a = PolyOverZ::from_str(&format!("3  1 -{} -1", u64::MAX)).unwrap();
        let modulus = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();

        unsafe { reduce_fmpz_poly_by_poly_over_z(&mut a.poly, &modulus) }

        assert_eq!(PolyOverZ::from(1), a);
    }
}

#[cfg(test)]
mod test_reduce_fmpz_poly_by_fmpz_poly {
    use crate::{
        integer::{MatPolyOverZ, fmpz_poly_helpers::reduce_fmpz_poly_by_fmpz_poly_sparse},
        integer_mod_q::ModulusPolynomialRingZq,
    };
    use flint_sys::{fmpz_poly::_fmpz_poly_normalise, fmpz_poly_mat::fmpz_poly_mat_entry};
    use std::str::FromStr;

    /// Ensures that the doc test example works.
    #[test]
    #[allow(unused_mut)] // the fmpz_poly_mat_entry gets mutable access, even though it only takes a constant pointer. Formally, it should be mutable
    fn working_example() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let mut poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();

        let entry = unsafe { fmpz_poly_mat_entry(&poly_mat.matrix, 0, 0) };
        if (unsafe { *entry }).length > 0 {
            unsafe {
                reduce_fmpz_poly_by_fmpz_poly_sparse(
                    (*entry).coeffs,
                    (*entry).length as usize,
                    modulus.modulus.poly.coeffs,
                    (modulus.get_degree() + 1) as usize,
                    &modulus.non_zero,
                )
            }
            unsafe {
                _fmpz_poly_normalise(entry);
            };
        }

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  -2 0 1, 1  42],[0, 2  1 2]]").unwrap();
        assert_eq!(cmp_poly_mat, poly_mat)
    }
}

#[cfg(test)]
mod test_reduce_fmpz_poly_by_fmpz_mod_poly {
    use crate::{
        integer::{MatPolyOverZ, fmpz_poly_helpers::reduce_fmpz_poly_by_fmpz_poly_sparse},
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use flint_sys::{fmpz_poly::_fmpz_poly_normalise, fmpz_poly_mat::fmpz_poly_mat_entry};
    use std::str::FromStr;

    /// Ensures that the doc test example works.
    #[test]
    #[allow(unused_mut)] // the fmpz_poly_mat_entry gets mutable access, even though it only takes a constant pointer. Formally, it should be mutable
    fn working_example() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let mut poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));

        let entry = unsafe { fmpz_poly_mat_entry(&poly_ring_mat.matrix.matrix, 0, 0) };
        if (unsafe { *entry }).length > 0 {
            unsafe {
                reduce_fmpz_poly_by_fmpz_poly_sparse(
                    (*entry).coeffs,
                    (*entry).length as usize,
                    poly_ring_mat.modulus.modulus.poly.coeffs,
                    (poly_ring_mat.modulus.get_degree() + 1) as usize,
                    &poly_ring_mat.modulus.non_zero,
                )
            }
            unsafe {
                _fmpz_poly_normalise(entry);
            };
        }

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  15 0 1, 1  8],[0, 2  1 2]]").unwrap();
        assert_eq!(
            cmp_poly_mat,
            poly_ring_mat.get_representative_least_nonnegative_residue()
        )
    }
}
