// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This file contains functionality to instantiate and test cyclotomic polynomials over [`PolyOverZ`]

use super::PolyOverZ;
use flint_sys::fmpz_poly::{fmpz_poly_cyclotomic, fmpz_poly_is_cyclotomic};

impl PolyOverZ {
    /// Tests if a polynomial is a cyclotomic polynomial.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let poly = PolyOverZ::from_str("5  1 0 0 0 1").unwrap();
    /// assert!(poly.is_cyclotomic())
    /// ```
    pub fn is_cyclotomic(&self) -> bool {
        unsafe { 0 != fmpz_poly_is_cyclotomic(&self.poly) }
    }

    /// Instantiates the `m`th cyclotomic polynomial.
    /// If `m` is prime, then the polynomial is of degree n-1, and all coefficients are `1`.
    /// If `m` is dividible by 2, then the polynomial takes on the value of the cyclotomic polynomial of
    /// degree m/2 over `-X`.
    /// More explanations about the details can be found here:
    /// <https://flintlib.org/doc/fmpz_poly.html#c._fmpz_poly_cyclotomic>.
    ///
    /// Parameters:
    /// - `m`: The identifier of the cyclotomic polynomial.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// // m is prime
    /// let poly = PolyOverZ::from_cyclotomic(5);
    /// assert_eq!(poly, PolyOverZ::from_str("5  1 1 1 1 1").unwrap());
    ///
    /// // m can be divided by 2
    /// let poly = PolyOverZ::from_cyclotomic(10);
    /// assert_eq!(poly, PolyOverZ::from_str("5  1 -1 1 -1 1").unwrap());
    ///
    /// // m as a higher value
    /// let poly = PolyOverZ::from_str("5  1 -1 1 -1 1").unwrap();
    /// ```
    pub fn from_cyclotomic(m: u64) -> Self {
        let mut out = PolyOverZ::default();
        unsafe { fmpz_poly_cyclotomic(&mut out.poly, m) };
        out
    }
}

#[cfg(test)]
mod test_is_cyclotomic {
    use crate::integer::PolyOverZ;

    /// Ensure that polynomials that are instantiated as cyclotomics are also evaluated as being cyclotomics
    #[test]
    fn is_cylcotomic_for_constants() {
        for i in [3, 4, 5, 100, 128, 256] {
            let cycl = PolyOverZ::from_cyclotomic(i);
            assert!(cycl.is_cyclotomic())
        }
    }
}

#[cfg(test)]
mod test_init_cyclotomic {
    use std::str::FromStr;

    use crate::{integer::PolyOverZ, traits::SetCoefficient};

    /// Ensure that the degree of cyclotomic polynomials is set correctly (Euler's totient function)
    #[test]
    fn correct_degree() {
        let cycl_73 = PolyOverZ::from_cyclotomic(73);
        let cycl_184 = PolyOverZ::from_cyclotomic(184);
        let cycl_256 = PolyOverZ::from_cyclotomic(256);
        let cycl_512 = PolyOverZ::from_cyclotomic(512);

        // 73 is prime, hence phi(73)=72
        assert_eq!(cycl_73.get_degree(), 72);
        // 184 = 2^3 * 23, hence 184*(1/2)*(1-1/23) = 1/2*(184-8) = 88
        assert_eq!(cycl_184.get_degree(), 88);
        // 256 = 2^8, hence phi(256) = 1/2*256
        assert_eq!(cycl_256.get_degree(), 128);
        // 512 = 2^9, hence phi(512) = 1/2*512
        assert_eq!(cycl_512.get_degree(), 256);
    }

    /// Ensure that the cyclotomic polynomial of degree 256 is set correctly
    #[test]
    fn correct_form_256() {
        let cycl_256 = PolyOverZ::from_cyclotomic(256);
        let mut cmp_cycl_256 = PolyOverZ::from(1);
        cmp_cycl_256.set_coeff(128, 1).unwrap();

        assert_eq!(cmp_cycl_256, cycl_256)
    }

    /// Edge cases: m=0,1,2
    #[test]
    fn small_m() {
        let cycl_0 = PolyOverZ::from_cyclotomic(0);
        let cycl_1 = PolyOverZ::from_cyclotomic(1);
        let cycl_2 = PolyOverZ::from_cyclotomic(2);

        assert_eq!(PolyOverZ::from_str("1  1").unwrap(), cycl_0);
        assert_eq!(PolyOverZ::from_str("2  -1 1").unwrap(), cycl_1);
        assert_eq!(PolyOverZ::from_str("2  1 1").unwrap(), cycl_2);
    }
}
