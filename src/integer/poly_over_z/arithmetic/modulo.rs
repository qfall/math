// Copyright © 2025 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Rem`] trait for [`PolyOverZ`] values.

use super::super::PolyOverZ;
use crate::{
    integer::Z,
    integer_mod_q::{Modulus, ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq},
    macros::{
        arithmetics::{arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned},
        for_others::implement_for_others,
    },
};
use flint_sys::fmpz_poly::fmpz_poly_scalar_mod_fmpz;
use std::ops::Rem;

impl Rem<&Z> for &PolyOverZ {
    type Output = PolyOverZ;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative coefficients in `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainders are computed
    ///
    /// Returns `self` mod `modulus` as a [`PolyOverZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{PolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("2  -2 42").unwrap();
    /// let b: Z = Z::from(24);
    ///
    /// let c: PolyOverZ = a % b;
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    fn rem(self, modulus: &Z) -> Self::Output {
        assert!(modulus > &1, "Modulus can not be smaller than 2.");
        let mut out = PolyOverZ::default();
        unsafe { fmpz_poly_scalar_mod_fmpz(&mut out.poly, &self.poly, &modulus.value) };
        out
    }
}

impl Rem<&Modulus> for &PolyOverZ {
    type Output = PolyOverZ;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative values of `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainder is computed
    ///
    /// Returns `self` mod `modulus` as a [`PolyOverZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Modulus;
    /// use qfall_math::integer::{PolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("2  -2 42").unwrap();
    /// let b = Modulus::from(24);
    ///
    /// let c: PolyOverZ = a % b;
    /// ```
    fn rem(self, modulus: &Modulus) -> Self::Output {
        let out = PolyOverZq::from((self, modulus));
        out.get_representative_least_nonnegative_residue()
    }
}

impl<Mod: Into<ModulusPolynomialRingZq>> Rem<Mod> for &PolyOverZ {
    type Output = PolyOverZ;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative values of `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainder is computed
    ///
    /// Returns `self` mod `modulus` as a [`PolyOverZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::{PolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("2  -2 42").unwrap();
    /// let b = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
    ///
    /// let c: PolyOverZ = &a % b;
    /// ```
    fn rem(self, modulus: Mod) -> Self::Output {
        let out = PolynomialRingZq::from((self, modulus));
        out.get_representative_least_nonnegative_residue()
    }
}

impl<Mod: Into<ModulusPolynomialRingZq>> Rem<Mod> for PolyOverZ {
    type Output = PolyOverZ;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative values of `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainder is computed
    ///
    /// Returns `self` mod `modulus` as a [`PolyOverZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::{PolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("2  -2 42").unwrap();
    /// let b = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
    ///
    /// let c: PolyOverZ = a % b;
    /// ```
    fn rem(self, modulus: Mod) -> Self::Output {
        PolynomialRingZq::from((self, modulus)).poly
    }
}

arithmetic_trait_borrowed_to_owned!(Rem, rem, PolyOverZ, Modulus, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Rem, rem, PolyOverZ, Modulus, PolyOverZ);
arithmetic_trait_borrowed_to_owned!(Rem, rem, PolyOverZ, Z, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Rem, rem, PolyOverZ, Z, PolyOverZ);

implement_for_others!(Z, PolyOverZ, Rem for i8 i16 i32 i64 u8 u16 u32 u64);

#[cfg(test)]
mod test_rem {
    use super::Z;
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{Modulus, ModulusPolynomialRingZq, PolyOverZq},
    };
    use std::str::FromStr;

    /// Testing modulo for two owned
    #[test]
    fn rem() {
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let b = Z::from(24);
        let modulus = Modulus::from(24);
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c1 = a.clone() % b;
        let c2 = a.clone() % modulus;
        let c3 = a % poly_mod;
        let cmp = PolyOverZ::from_str("2  2 18").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Testing modulo for two borrowed
    #[test]
    fn rem_borrow() {
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let b = Z::from(24);
        let modulus = Modulus::from(24);
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c1 = &a % &b;
        let c2 = &a % &modulus;
        let c3 = &a % &poly_mod;
        let cmp = PolyOverZ::from_str("2  2 18").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Testing modulo for borrowed and owned
    #[test]
    fn rem_first_borrowed() {
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let b = Z::from(24);
        let modulus = Modulus::from(24);
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c1 = &a % b;
        let c2 = &a % modulus;
        let c3 = &a % poly_mod;
        let cmp = PolyOverZ::from_str("2  2 18").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Testing modulo for owned and borrowed
    #[test]
    fn rem_second_borrowed() {
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let b = Z::from(24);
        let modulus = Modulus::from(24);
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c1 = a.clone() % &b;
        let c2 = a.clone() % &modulus;
        let c3 = a % &poly_mod;
        let cmp = PolyOverZ::from_str("2  2 18").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Testing modulo for negative values
    #[test]
    fn rem_negative_representation() {
        let a = PolyOverZ::from_str("2  -2 42").unwrap();
        let b = Z::from(24);
        let modulus = Modulus::from(24);
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c1 = &a % &b;
        let c2 = &a % &modulus;
        let c3 = a % &poly_mod;
        let cmp = PolyOverZ::from_str("2  22 18").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Testing modulo for large numbers
    #[test]
    fn rem_large_numbers() {
        let a = PolyOverZ::from_str(&format!("2  2 {}", u64::MAX)).unwrap();
        let b = Z::from(u64::MAX - 2);
        let modulus = Modulus::from(u64::MAX - 2);
        let poly_mod =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX - 2)).unwrap();
        let c1 = a.clone() % &b;
        let c2 = a.clone() % &modulus;
        let c3 = a % &poly_mod;
        let cmp = PolyOverZ::from_str("2  2 2").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Ensure that the reduction with a polynomial modulus also reduces the polynomial degree.
    #[test]
    fn polynomial_reduction() {
        let a = PolyOverZ::from_str("4  2 42 0 1").unwrap();
        let b = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c = a % b;
        let cmp = PolyOverZ::from_str("2  1 18").unwrap();
        assert_eq!(c, cmp);
    }

    /// Ensures that computing modulo a negative number results in a panic
    #[test]
    #[should_panic]
    fn rem_negative_error() {
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let b = Z::from(-24);
        _ = &a % &b;
    }

    /// Ensures that computing modulo 0 results in a panic
    #[test]
    #[should_panic]
    fn zero_modulus() {
        _ = PolyOverZ::from_str("2  2 42").unwrap() % 0;
    }

    /// Ensures that `modulo` is available for several types
    #[test]
    fn availability() {
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % 2u8;
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % 2u16;
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % 2u32;
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % 2u64;
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % 2i8;
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % 2i16;
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % 2i32;
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % 2i64;
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % Z::from(2);
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % Modulus::from(2);
        let _ = PolyOverZ::from_str("2  2 42").unwrap()
            % ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();

        let _ = &PolyOverZ::from_str("2  2 42").unwrap() % 2u8;
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % &Z::from(2);
        let _ = &PolyOverZ::from_str("2  2 42").unwrap() % &Z::from(2);
        let _ = PolyOverZ::from_str("2  2 42").unwrap()
            % PolyOverZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let _ = PolyOverZ::from_str("2  2 42").unwrap()
            % &PolyOverZq::from_str("4  1 0 0 1 mod 24").unwrap();
    }
}
