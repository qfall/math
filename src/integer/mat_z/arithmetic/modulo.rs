// Copyright 2025 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Rem`] trait for [`MatZ`] values.

use super::super::MatZ;
use crate::{
    integer::Z,
    integer_mod_q::Modulus,
    macros::{
        arithmetics::{arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned},
        for_others::implement_for_others,
    },
    traits::{MatrixDimensions, MatrixGetEntry, MatrixSetEntry},
};
use flint_sys::{fmpz::fmpz_mod, fmpz_mat::fmpz_mat_entry, fmpz_mod::fmpz_mod_set_fmpz};
use std::ops::Rem;

impl Rem<&Z> for &MatZ {
    type Output = MatZ;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative entries in `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainders are computed
    ///
    /// Returns `self` mod `modulus` as a [`MatZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatZ, Z};
    /// use std::str::FromStr;
    ///
    /// let a: MatZ = MatZ::from_str("[[-2],[42]]").unwrap();
    /// let b: Z = Z::from(24);
    ///
    /// let c: MatZ = a % b;
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    fn rem(self, modulus: &Z) -> Self::Output {
        assert!(modulus > &1, "Modulus can not be smaller than 2.");

        let out = self.clone();

        for i in 0..out.get_num_rows() {
            for j in 0..out.get_num_columns() {
                let entry = unsafe { fmpz_mat_entry(&out.matrix, i, j) };
                unsafe { fmpz_mod(entry, entry, &modulus.value) }
            }
        }

        out
    }
}

impl Rem<&Modulus> for &MatZ {
    type Output = MatZ;
    /// Computes `self` mod `modulus`.
    /// For negative entries in `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainders are computed
    ///
    /// Returns `self` mod `modulus` as a [`MatZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let a: MatZ = MatZ::from_str("[[-2],[42]]").unwrap();
    /// let b = Modulus::from(24);
    ///
    /// let c: MatZ = &a % &b;
    /// ```
    fn rem(self, modulus: &Modulus) -> Self::Output {
        let out = self.clone();

        for i in 0..out.get_num_rows() {
            for j in 0..out.get_num_columns() {
                let entry = unsafe { fmpz_mat_entry(&out.matrix, i, j) };
                unsafe { fmpz_mod_set_fmpz(entry, entry, modulus.get_fmpz_mod_ctx_struct()) }
            }
        }

        out
    }
}

arithmetic_trait_borrowed_to_owned!(Rem, rem, MatZ, Z, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Rem, rem, MatZ, Z, MatZ);
arithmetic_trait_borrowed_to_owned!(Rem, rem, MatZ, Modulus, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Rem, rem, MatZ, Modulus, MatZ);

implement_for_others!(Z, MatZ, Rem for i8 i16 i32 i64 u8 u16 u32 u64);

impl MatZ {
    /// Computes `self` mod± `modulus` as long as `modulus` is greater than 1, i.e.
    /// it returns a matrix with entries in `[-⌈q/2⌉, ⌈q/2⌉]`.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the remainder closest to `0` is computed
    ///
    /// Returns `self` mod± `modulus` as a [`MatZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::from_str("[[-2],[42]]").unwrap();
    ///
    /// let c = a.mod_pm(24);
    ///
    /// assert_eq!(MatZ::from_str("[[-2],[-6]]").unwrap(), c);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    pub fn mod_pm(&self, modulus: impl Into<Z>) -> Self {
        let modulus = modulus.into();
        assert!(modulus > 1, "Modulus can not be smaller than 2.");

        let mut mat = self.rem(&modulus);

        for row in 0..mat.get_num_rows() {
            for col in 0..mat.get_num_columns() {
                let mut entry = unsafe { mat.get_entry_unchecked(row, col) };
                if entry > modulus.div_floor(2) {
                    entry -= &modulus;
                }
                unsafe { mat.set_entry_unchecked(row, col, entry) };
            }
        }

        mat
    }
}

#[cfg(test)]
mod test_rem {
    use super::Z;
    use crate::{integer::MatZ, integer_mod_q::Modulus};
    use std::str::FromStr;

    /// Testing modulo for two owned
    #[test]
    fn rem() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(24);
        let c1 = a.clone() % b;
        let c2 = a % Modulus::from(24);
        assert_eq!(c1, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
        assert_eq!(c2, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
    }

    /// Testing modulo for two borrowed
    #[test]
    fn rem_borrow() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(24);
        let c1 = &a % &b;
        let c2 = &a % &Modulus::from(24);
        assert_eq!(c1, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
        assert_eq!(c2, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
    }

    /// Testing modulo for borrowed and owned
    #[test]
    fn rem_first_borrowed() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(24);
        let c1 = &a % b;
        let c2 = &a % Modulus::from(24);
        assert_eq!(c1, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
        assert_eq!(c2, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
    }

    /// Testing modulo for owned and borrowed
    #[test]
    fn rem_second_borrowed() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(24);
        let c1 = a.clone() % &b;
        let c2 = a % &Modulus::from(24);
        assert_eq!(c1, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
        assert_eq!(c2, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
    }

    /// Testing modulo for negative values
    #[test]
    fn rem_negative_representation() {
        let a = MatZ::from_str("[[-2, 3],[42, 24]]").unwrap();
        let b = Z::from(24);
        let c1 = &a % &b;
        let c2 = &a % &Modulus::from(24);
        assert_eq!(c1, MatZ::from_str("[[22, 3],[18, 0]]").unwrap());
        assert_eq!(c2, MatZ::from_str("[[22, 3],[18, 0]]").unwrap());
    }

    /// Testing modulo for large numbers
    #[test]
    fn rem_large_numbers() {
        let a = MatZ::from_str(&format!("[[2, 3],[{}, 24]]", u64::MAX)).unwrap();
        let b = Z::from(u64::MAX - 2);
        let c1 = &a % &b;
        let c2 = &a % &Modulus::from(u64::MAX - 2);
        assert_eq!(c1, MatZ::from_str("[[2, 3],[2, 24]]").unwrap());
        assert_eq!(c2, MatZ::from_str("[[2, 3],[2, 24]]").unwrap());
    }

    /// Ensures that computing modulo a negative number results in a panic
    #[test]
    #[should_panic]
    fn rem_negative_error() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(-24);
        _ = &a % &b;
    }

    /// Ensures that computing modulo 0 results in a panic
    #[test]
    #[should_panic]
    fn zero_modulus() {
        _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 0;
    }

    /// Ensures that `modulo` is available for several types.
    #[test]
    fn availability() {
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 2u8;
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 2u16;
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 2u32;
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 2u64;
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 2i8;
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 2i16;
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 2i32;
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 2i64;
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % Z::from(2);
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % Modulus::from(2);

        let _ = &MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 2u8;
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % &Z::from(2);
        let _ = &MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % &Z::from(2);
    }
}

#[cfg(test)]
mod test_mod_pm {
    use super::Z;
    use crate::{integer::MatZ, integer_mod_q::Modulus};
    use std::str::FromStr;

    /// Testing mod± for two owned
    #[test]
    fn mod_pm() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(25);
        let c1 = a.clone().mod_pm(b);
        let c2 = a.mod_pm(Modulus::from(25));
        assert_eq!(c1, MatZ::from_str("[[2, 3],[-8, -1]]").unwrap());
        assert_eq!(c2, MatZ::from_str("[[2, 3],[-8, -1]]").unwrap());
    }

    /// Testing mod± for large numbers
    #[test]
    fn mod_pm_large_numbers() {
        let a = MatZ::from_str(&format!("[[2, 3],[{}, 24]]", u64::MAX)).unwrap();
        let b = Z::from(u64::MAX - 2);
        let c1 = a.mod_pm(&b);
        let c2 = a.mod_pm(&Modulus::from(u64::MAX - 2));
        assert_eq!(c1, MatZ::from_str("[[2, 3],[2, 24]]").unwrap());
        assert_eq!(c2, MatZ::from_str("[[2, 3],[2, 24]]").unwrap());
    }

    /// Ensures that computing mod± a negative number results in a panic
    #[test]
    #[should_panic]
    fn mod_pm_negative_error() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(-24);
        _ = &a.mod_pm(&b);
    }

    /// Ensures that computing mod± 0 results in a panic
    #[test]
    #[should_panic]
    fn zero_modulus() {
        _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap().mod_pm(0);
    }

    /// Ensures that `mod±` is available for several types.
    #[test]
    fn availability() {
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap().mod_pm(2u8);
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap().mod_pm(2u16);
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap().mod_pm(2u32);
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap().mod_pm(2u64);
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap().mod_pm(2i8);
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap().mod_pm(2i16);
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap().mod_pm(2i32);
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap().mod_pm(2i64);
        let _ = MatZ::from_str("[[2, 3],[42, 24]]")
            .unwrap()
            .mod_pm(Z::from(2));
        let _ = MatZ::from_str("[[2, 3],[42, 24]]")
            .unwrap()
            .mod_pm(Modulus::from(2));
    }
}
