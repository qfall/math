// Copyright © 2025 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Rem`] trait for [`MatPolyOverZ`] values.

use super::super::MatPolyOverZ;
use crate::{
    integer::Z,
    integer_mod_q::{MatPolynomialRingZq, Modulus, ModulusPolynomialRingZq},
    macros::{
        arithmetics::{arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned},
        for_others::implement_for_others,
    },
    traits::{MatrixDimensions, MatrixGetEntry, MatrixSetEntry},
};
use std::ops::Rem;

impl Rem<&Z> for &MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative entries in `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainders are computed
    ///
    /// Returns `self` mod `modulus` as a [`MatPolyOverZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatPolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[2  1 -2],[1  42]]").unwrap();
    /// let b: Z = Z::from(24);
    ///
    /// let c: MatPolyOverZ = a % b;
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    fn rem(self, modulus: &Z) -> Self::Output {
        assert!(modulus > &1, "Modulus can not be smaller than 2.");
        let num_cols = self.get_num_columns();
        let num_rows = self.get_num_rows();

        let mut out = MatPolyOverZ::new(num_rows, num_cols);

        for i in 0..num_rows {
            for j in 0..num_cols {
                let mut entry = unsafe { self.get_entry_unchecked(i, j) };
                entry = entry % modulus;
                unsafe { out.set_entry_unchecked(i, j, entry) };
            }
        }

        out
    }
}

impl Rem<&Modulus> for &MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative entries in `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainders are computed
    ///
    /// Returns `self` mod `modulus` as a [`MatPolyOverZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[2  1 -2],[1  42]]").unwrap();
    /// let b = Modulus::from(24);
    ///
    /// let c: MatPolyOverZ = &a % &b;
    /// ```
    fn rem(self, modulus: &Modulus) -> Self::Output {
        let mut out = MatPolyOverZ::new(self.get_num_rows(), self.get_num_rows());

        for i in 0..self.get_num_rows() {
            for j in 0..self.get_num_columns() {
                let mut entry = unsafe { self.get_entry_unchecked(i, j) };
                entry = entry % modulus;
                unsafe { out.set_entry_unchecked(i, j, entry) };
            }
        }

        out
    }
}

impl<Mod: Into<ModulusPolynomialRingZq>> Rem<Mod> for &MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative entries in `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainders are computed
    ///
    /// Returns `self` mod `modulus` as a [`MatPolyOverZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[2  1 -2],[1  42]]").unwrap();
    /// let b = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
    ///
    /// let c: MatPolyOverZ = &a % &b;
    /// ```
    fn rem(self, modulus: Mod) -> Self::Output {
        MatPolynomialRingZq::from((self, modulus)).matrix
    }
}

impl<Mod: Into<ModulusPolynomialRingZq>> Rem<Mod> for MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative entries in `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainders are computed
    ///
    /// Returns `self` mod `modulus` as a [`MatPolyOverZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[2  1 -2],[1  42]]").unwrap();
    /// let b = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
    ///
    /// let c: MatPolyOverZ = &a % &b;
    /// ```
    fn rem(self, modulus: Mod) -> Self::Output {
        MatPolynomialRingZq::from((self, modulus)).matrix
    }
}

arithmetic_trait_borrowed_to_owned!(Rem, rem, MatPolyOverZ, Z, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Rem, rem, MatPolyOverZ, Z, MatPolyOverZ);
arithmetic_trait_borrowed_to_owned!(Rem, rem, MatPolyOverZ, Modulus, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Rem, rem, MatPolyOverZ, Modulus, MatPolyOverZ);

implement_for_others!(Z, MatPolyOverZ, Rem for i8 i16 i32 i64 u8 u16 u32 u64);

#[cfg(test)]
mod test_rem {
    use super::Z;
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{Modulus, ModulusPolynomialRingZq, PolyOverZq},
    };
    use std::str::FromStr;

    /// Testing modulo for two owned
    #[test]
    fn rem() {
        let a = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap();
        let b = Z::from(24);
        let modulus = Modulus::from(24);
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c1 = a.clone() % b;
        let c2 = a.clone() % modulus;
        let c3 = a % poly_mod;
        let cmp = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 18, 0]]").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Testing modulo for two borrowed
    #[test]
    fn rem_borrow() {
        let a = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap();
        let b = Z::from(24);
        let modulus = Modulus::from(24);
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c1 = &a % &b;
        let c2 = &a % &modulus;
        let c3 = &a % &poly_mod;
        let cmp = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 18, 0]]").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Testing modulo for borrowed and owned
    #[test]
    fn rem_first_borrowed() {
        let a = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap();
        let b = Z::from(24);
        let modulus = Modulus::from(24);
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c1 = &a % b;
        let c2 = &a % modulus;
        let c3 = &a % poly_mod;
        let cmp = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 18, 0]]").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Testing modulo for owned and borrowed
    #[test]
    fn rem_second_borrowed() {
        let a = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap();
        let b = Z::from(24);
        let modulus = Modulus::from(24);
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c1 = a.clone() % &b;
        let c2 = a.clone() % &modulus;
        let c3 = a % &poly_mod;
        let cmp = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 18, 0]]").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Testing modulo for negative values
    #[test]
    fn rem_negative_representation() {
        let a = MatPolyOverZ::from_str("[[1  -2, 1  3],[2  3 42, 1  24]]").unwrap();
        let b = Z::from(24);
        let modulus = Modulus::from(24);
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c1 = &a % &b;
        let c2 = &a % &modulus;
        let c3 = a % &poly_mod;
        let cmp = MatPolyOverZ::from_str("[[1  22, 1  3],[2  3 18, 0]]").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Testing modulo for large numbers
    #[test]
    fn rem_large_numbers() {
        let a =
            MatPolyOverZ::from_str(&format!("[[1  2, 1  {}],[2  3 42, 1  24]]", u64::MAX)).unwrap();
        let b = Z::from(u64::MAX - 2);
        let modulus = Modulus::from(u64::MAX - 2);
        let poly_mod =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX - 2)).unwrap();
        let c1 = a.clone() % &b;
        let c2 = a.clone() % &modulus;
        let c3 = a % &poly_mod;
        let cmp = MatPolyOverZ::from_str("[[1  2, 1  2],[2  3 42, 1  24]]").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
        assert_eq!(c3, cmp);
    }

    /// Ensure that the reduction with a polynomial modulus also reduces the polynomial degree.
    #[test]
    fn polynomial_reduction() {
        let a = MatPolyOverZ::from_str("[[1  -2, 4  1 1 0 1],[2  3 42, 1  24]]").unwrap();
        let b = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let c = a % b;
        let cmp = MatPolyOverZ::from_str("[[1  22, 2  0 1],[2  3 18, 0]]").unwrap();
        assert_eq!(c, cmp);
    }

    /// Ensures that computing modulo a negative number results in a panic
    #[test]
    #[should_panic]
    fn rem_negative_error() {
        let a = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap();
        let b = Z::from(-24);
        _ = &a % &b;
    }

    /// Ensures that computing modulo 0 results in a panic
    #[test]
    #[should_panic]
    fn zero_modulus() {
        _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % 0;
    }

    /// Ensures that `modulo` is available for several types implementing [`Into<Z>`].
    #[test]
    fn availability() {
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % 2u8;
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % 2u16;
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % 2u32;
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % 2u64;
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % 2i8;
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % 2i16;
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % 2i32;
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % 2i64;
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % Z::from(2);
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap()
            % ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();

        let _ = &MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % 2u8;
        let _ = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % &Z::from(2);
        let _ = &MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap() % &Z::from(2);
        let _ = &MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap()
            % PolyOverZq::from_str("4  1 0 0 1 mod 24").unwrap();
        let _ = &MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap()
            % &PolyOverZq::from_str("4  1 0 0 1 mod 24").unwrap();
    }
}
