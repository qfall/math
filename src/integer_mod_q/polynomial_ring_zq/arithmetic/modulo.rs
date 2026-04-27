// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the `mod±` function for [`PolynomialRingZq`] values.

use super::super::PolynomialRingZq;
use crate::{
    integer::{PolyOverZ, Z},
    traits::{GetCoefficient, SetCoefficient},
};
use std::ops::Rem;

impl PolynomialRingZq {
    /// Computes `self` mod± `modulus` as long as `modulus` is greater than 1, i.e.
    /// it returns a polynomial with coefficients in `[-⌈q/2⌉, ⌈q/2⌉]`.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the remainder closest to `0` is computed
    ///
    /// Returns `self` mod± `modulus` as a [`PolyOverZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
    /// let poly_1 = PolyOverZ::from(42);
    /// let mut a = PolynomialRingZq::from((&poly_1, &modulus));
    ///
    /// let c = a.mod_pm(24);
    ///
    /// assert_eq!(PolyOverZ::from(-6), c);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    pub fn mod_pm(&self, modulus: impl Into<Z>) -> PolyOverZ {
        let modulus = modulus.into();
        assert!(modulus > 1, "Modulus can not be smaller than 2.");

        let mut poly = (&self.poly).rem(&modulus);

        for i in 0..=poly.get_degree() {
            let mut coeff = unsafe { poly.get_coeff_unchecked(i) };
            if coeff > modulus.div_floor(2) {
                coeff -= &modulus;
            }
            unsafe { poly.set_coeff_unchecked(i, coeff) };
        }

        poly
    }
}

#[cfg(test)]
mod test_mod_pm {
    use super::Z;
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{Modulus, ModulusPolynomialRingZq, PolynomialRingZq},
    };
    use std::str::FromStr;

    /// Testing mod± for two owned
    #[test]
    fn mod_pm() {
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 257").unwrap();
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let a = PolynomialRingZq::from((a, &poly_mod));
        let b = Z::from(25);
        let modulus = Modulus::from(25);
        let c1 = a.clone().mod_pm(b);
        let c2 = a.clone().mod_pm(modulus);
        let cmp = PolyOverZ::from_str("2  2 -8").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
    }

    /// Testing mod± for large numbers
    #[test]
    fn mod_pm_large_numbers() {
        let poly_mod =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let a = PolyOverZ::from_str(&format!("2  2 {}", u64::MAX - 1)).unwrap();
        let a = PolynomialRingZq::from((a, &poly_mod));
        let b = Z::from(u64::MAX - 2);
        let modulus = Modulus::from(u64::MAX - 2);
        let c1 = a.clone().mod_pm(&b);
        let c2 = a.clone().mod_pm(&modulus);
        let cmp = PolyOverZ::from_str("2  2 1").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
    }

    /// Ensures that computing mod± a negative number results in a panic
    #[test]
    #[should_panic]
    fn mod_pm_negative_error() {
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let a = PolynomialRingZq::from((a, &poly_mod));
        let b = Z::from(-24);
        _ = &a.mod_pm(&b);
    }

    /// Ensures that computing mod± 0 results in a panic
    #[test]
    #[should_panic]
    fn zero_modulus() {
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let a = PolynomialRingZq::from((a, &poly_mod));
        _ = a.mod_pm(0);
    }

    /// Ensures that `mod±` is available for several types
    #[test]
    fn availability() {
        let _ = PolynomialRingZq::from_str("2  2 42 / 4  1 0 0 1 mod 7")
            .unwrap()
            .mod_pm(2u8);
        let _ = PolynomialRingZq::from_str("2  2 42 / 4  1 0 0 1 mod 7")
            .unwrap()
            .mod_pm(2u16);
        let _ = PolynomialRingZq::from_str("2  2 42 / 4  1 0 0 1 mod 7")
            .unwrap()
            .mod_pm(2u32);
        let _ = PolynomialRingZq::from_str("2  2 42 / 4  1 0 0 1 mod 7")
            .unwrap()
            .mod_pm(2u64);
        let _ = PolynomialRingZq::from_str("2  2 42 / 4  1 0 0 1 mod 7")
            .unwrap()
            .mod_pm(2i8);
        let _ = PolynomialRingZq::from_str("2  2 42 / 4  1 0 0 1 mod 7")
            .unwrap()
            .mod_pm(2i16);
        let _ = PolynomialRingZq::from_str("2  2 42 / 4  1 0 0 1 mod 7")
            .unwrap()
            .mod_pm(2i32);
        let _ = PolynomialRingZq::from_str("2  2 42 / 4  1 0 0 1 mod 7")
            .unwrap()
            .mod_pm(2i64);
        let _ = PolynomialRingZq::from_str("2  2 42 / 4  1 0 0 1 mod 7")
            .unwrap()
            .mod_pm(Z::from(2));
        let _ = PolynomialRingZq::from_str("2  2 42 / 4  1 0 0 1 mod 7")
            .unwrap()
            .mod_pm(Modulus::from(2));
    }
}
