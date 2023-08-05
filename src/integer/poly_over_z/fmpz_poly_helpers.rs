// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains helpful functions on [`fmpz_poly_struct`].

use super::PolyOverZ;
use crate::{
    integer::Z,
    traits::{GetCoefficient, SetCoefficient},
};
use flint_sys::fmpz_poly::{fmpz_poly_get_coeff_fmpz, fmpz_poly_struct, fmpz_poly_sub};

/// Reduces an [`fmpz_poly_struct`] instance by a [`PolyOverZ`].
/// The modulus must have a leading coefficient of `1`, else the function will panic.
///
/// Parameters:
/// - `modulus`: Specifies the polynomial by which `self` is reduced
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
    poly: *mut fmpz_poly_struct,
    modulus: &PolyOverZ,
) {
    let self_nr_coeff = (*poly).length + 1;
    let modulus_nr_coeff = modulus.get_degree();

    assert_eq!(
        Z::ONE,
        modulus.get_coeff(modulus_nr_coeff).unwrap(),
        "In order to reduce, the modulus must have a leading coefficient of 1."
    );

    for i in (modulus_nr_coeff..=self_nr_coeff).rev() {
        let mut coeff = Z::default();
        unsafe { fmpz_poly_get_coeff_fmpz(&mut coeff.value, poly, i) }
        let mut degree = PolyOverZ::default();
        degree.set_coeff(i - modulus_nr_coeff, coeff).unwrap();
        let minus_poly: PolyOverZ = degree * modulus;

        unsafe { fmpz_poly_sub(poly, poly, &minus_poly.poly) }
    }
}

#[cfg(test)]
mod test_reduce_fmpz_poly_by_poly_over_z {
    use crate::integer::{
        poly_over_z::fmpz_poly_helpers::reduce_fmpz_poly_by_poly_over_z, PolyOverZ,
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
