// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to manipulate a [`PolynomialRingZq`] element.

use super::PolynomialRingZq;
use crate::{
    integer::Z, integer_mod_q::Zq, macros::for_others::implement_for_owned, traits::SetCoefficient,
};
use flint_sys::fmpz_poly::fmpz_poly_set_coeff_fmpz;

impl<Integer: Into<Z>> SetCoefficient<Integer> for PolynomialRingZq {
    /// Sets the coefficient of a [`PolynomialRingZq`] element.
    /// We advise to use small coefficients, since already 2^32 coefficients take space
    /// of roughly 34 GB. If not careful, be prepared that memory problems can occur, if
    /// the index is very high.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to set (has to be positive)
    /// - `value`: the new value the index should have
    ///
    /// # Examples
    /// ```
    /// use crate::qfall_math::traits::SetCoefficient;
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("3  0 1 1").unwrap();
    /// let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));
    ///
    /// poly_ring.set_coeff(2, 16).unwrap();
    /// unsafe{ poly_ring.set_coeff_unchecked(5, 5) };
    /// ```
    ///
    /// # Safety
    /// To use this function safely, make sure that the selected index
    /// is greater or equal than `0` and that the provided value has
    /// the same base so that they have a matching base.
    unsafe fn set_coeff_unchecked(&mut self, index: i64, value: Integer) {
        let value = value.into();

        unsafe {
            fmpz_poly_set_coeff_fmpz(&mut self.poly.poly, index, &value.value);
        };
        self.reduce();
    }
}

impl SetCoefficient<&Zq> for PolynomialRingZq {
    /// Sets the coefficient of a [`PolynomialRingZq`] element.
    /// We advise to use small coefficients, since already 2^32 coefficients take space
    /// of roughly 34 GB. If not careful, be prepared that memory problems can occur, if
    /// the index is very high.
    ///
    /// This function does not check if the modulus of the polynomial and the value match.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to set (has to be positive)
    /// - `value`: the new value the index should have
    ///
    /// # Examples
    /// ```
    /// use crate::qfall_math::traits::SetCoefficient;
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer_mod_q::Zq;
    /// use std::str::FromStr;    
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("3  0 1 1").unwrap();
    /// let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));
    /// let value = Zq::from((1000, 17));
    ///
    /// poly_ring.set_coeff(2, &value).unwrap();
    /// unsafe{ poly_ring.set_coeff_unchecked(5, &value) };
    /// ```
    ///
    /// # Safety
    /// To use this function safely, make sure that the selected index
    /// is greater or equal than `0` and that the provided value has
    /// the same base so that they have a matching base.
    unsafe fn set_coeff_unchecked(&mut self, index: i64, value: &Zq) {
        unsafe { self.set_coeff_unchecked(index, &value.value) };
    }
}

implement_for_owned!(Zq, PolynomialRingZq, SetCoefficient);

#[cfg(test)]
mod test_set_coeff {
    use crate::{
        integer::{PolyOverZ, Z},
        integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq, Zq},
        traits::SetCoefficient,
    };
    use std::str::FromStr;

    /// Ensure that setting is available for other types.
    #[test]
    fn availability() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  0 1 1").unwrap();
        let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));

        poly_ring.set_coeff(1, 3u64).unwrap();
        poly_ring.set_coeff(1, 3u32).unwrap();
        poly_ring.set_coeff(1, 3u16).unwrap();
        poly_ring.set_coeff(1, 3u8).unwrap();
        poly_ring.set_coeff(1, 3i64).unwrap();
        poly_ring.set_coeff(1, 3i32).unwrap();
        poly_ring.set_coeff(1, 3i16).unwrap();
        poly_ring.set_coeff(1, 3i8).unwrap();
        poly_ring.set_coeff(1, Z::from(3)).unwrap();
        poly_ring.set_coeff(1, &Z::from(3)).unwrap();
        poly_ring.set_coeff(1, &Zq::from((3, 17))).unwrap();
    }

    /// Ensure that large coefficients work.
    #[test]
    fn set_coeff_large() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  0 1 1").unwrap();
        let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));

        assert!(poly_ring.set_coeff(2, i32::MAX).is_ok());
        assert!(poly_ring.set_coeff(2, i64::MAX).is_ok());
    }

    /// Ensure that the max of [`u8`] and [`u16`] works as an index.
    #[test]
    fn set_index_large() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  0 1 1").unwrap();
        let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));

        assert!(poly_ring.set_coeff(u8::MAX, 2).is_ok());
        assert!(poly_ring.set_coeff(u16::MAX, 2).is_ok());
    }

    /// Ensure that a general case is working.
    #[test]
    fn set_coeff_working() {
        let modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 1 5 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  0 2 1").unwrap();
        let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));
        let value = 10000;

        poly_ring.set_coeff(0, value).unwrap();
        poly_ring.set_coeff(2, value).unwrap();

        let cmp_poly = PolyOverZ::from_str("3  10000 2 10000").unwrap();
        let cmp_poly_ring = PolynomialRingZq::from((&cmp_poly, &modulus));
        assert_eq!(cmp_poly_ring, poly_ring);
    }

    /// Ensure that the set polynomial is reduced correctly.
    #[test]
    fn set_reduce() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from(1);
        let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));

        poly_ring.set_coeff(3, 1).unwrap();

        let cmp_poly = PolyOverZ::from(0);
        let cmp_poly_ring = PolynomialRingZq::from((&cmp_poly, &modulus));
        assert_eq!(cmp_poly_ring, poly_ring);
    }

    /// Ensure that the correct coefficient is set and all others are set to `0`.
    #[test]
    fn set_coeff_rest_zero() {
        let modulus = ModulusPolynomialRingZq::from_str("7  1 8 0 0 1 0 12 mod 17").unwrap();
        let poly = PolyOverZ::from_str("2  0 2").unwrap();
        let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));

        poly_ring.set_coeff(5, 10).unwrap();

        let cmp_poly = PolyOverZ::from_str("6  0 2 0 0 0 10").unwrap();
        let cmp_poly_ring = PolynomialRingZq::from((&cmp_poly, &modulus));
        assert_eq!(cmp_poly_ring, poly_ring);
    }

    /// Ensure that the negative indices return an error.
    #[test]
    fn set_negative_index() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  0 1 1").unwrap();
        let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));

        assert!(poly_ring.set_coeff(-1, 2).is_err());
        assert!(poly_ring.set_coeff(i64::MIN, 2).is_err());
        assert!(poly_ring.set_coeff(i32::MIN, 2).is_err());
        assert!(poly_ring.set_coeff(i16::MIN, 2).is_err());
        assert!(poly_ring.set_coeff(i8::MIN, 2).is_err());
    }

    /// Ensure that a different base returns an error.
    #[test]
    fn different_base() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  0 1 1").unwrap();
        let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));
        let value = Zq::from((13, 18));

        assert!(poly_ring.set_coeff(1, &value).is_err());
    }
}
