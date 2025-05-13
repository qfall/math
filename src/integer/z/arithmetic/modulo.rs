// Copyright © 2025 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Rem`] trait for [`Z`] values.

use flint_sys::{fmpz::fmpz_mod, fmpz_mod::fmpz_mod_set_fmpz};

use super::super::Z;
use crate::{
    integer_mod_q::Modulus,
    macros::arithmetics::{
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
};
use std::ops::Rem;

impl Rem for &Z {
    type Output = Z;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative values of `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainder is computed
    ///
    /// Returns `self` mod `modulus` as a [`Z`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Z = Z::from(24);
    ///
    /// let c: Z = a % b;
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    fn rem(self, modulus: Self) -> Self::Output {
        assert!(modulus > &1, "Modulus can not be smaller than 2.");
        let mut out = Z::default();
        unsafe { fmpz_mod(&mut out.value, &self.value, &modulus.value) };
        out
    }
}

impl Rem<&Modulus> for &Z {
    type Output = Z;
    /// Computes `self` mod `modulus` as long as `modulus` is greater than 1.
    /// For negative values of `self`, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the positive remainder is computed
    ///
    /// Returns `self` mod `modulus` as a [`Z`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::Modulus;
    ///
    /// let a: Z = Z::from(42);
    /// let b = Modulus::from(24);
    ///
    /// let c: Z = a % &b;
    /// ```
    fn rem(self, modulus: &Modulus) -> Self::Output {
        let mut out = Z::default();
        unsafe {
            fmpz_mod_set_fmpz(
                &mut out.value,
                &self.value,
                modulus.get_fmpz_mod_ctx_struct(),
            )
        };
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Rem, rem, Z, Z, Z);
arithmetic_trait_mixed_borrowed_owned!(Rem, rem, Z, Z, Z);
arithmetic_trait_borrowed_to_owned!(Rem, rem, Z, Modulus, Z);
arithmetic_trait_mixed_borrowed_owned!(Rem, rem, Z, Modulus, Z);
arithmetic_between_types!(Rem, rem, Z, Z, i64 i32 i16 i8 u64 u32 u16 u8);

#[cfg(test)]
mod test_rem {
    use super::Z;
    use crate::integer_mod_q::Modulus;

    /// Testing modulo for two [`Z`]
    #[test]
    fn rem() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c1: Z = a.clone() % b;
        let c2: Z = a % Modulus::from(24);
        assert_eq!(c1, 18);
        assert_eq!(c2, 18);
    }

    /// Testing modulo for borrowed [`Z`]
    #[test]
    fn rem_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c1: Z = &a % &b;
        let c2: Z = &a % &Modulus::from(24);
        assert_eq!(c1, 18);
        assert_eq!(c2, 18);
    }

    /// Testing modulo for borrowed and owned
    #[test]
    fn rem_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c1: Z = &a % b;
        let c2: Z = &a % Modulus::from(24);
        assert_eq!(c1, 18);
        assert_eq!(c2, 18);
    }

    /// Testing modulo for owned and borrowed
    #[test]
    fn rem_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c1: Z = a.clone() % &b;
        let c2: Z = a % &Modulus::from(24);
        assert_eq!(c1, 18);
        assert_eq!(c2, 18);
    }

    /// Testing modulo for negative values
    #[test]
    fn rem_negative_representation() {
        let a: Z = Z::from(-2);
        let b: Z = Z::from(24);
        let c1: Z = a.clone() % &b;
        let c2: Z = &a % &Modulus::from(24);
        assert_eq!(c1, 22);
        assert_eq!(c2, 22);
    }

    /// Testing modulo for large numbers
    #[test]
    fn rem_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Z = Z::from(u64::MAX - 2);

        let c1: Z = a.clone() % &b;
        let c2: Z = a % &Modulus::from(u64::MAX - 2);
        assert_eq!(c1, 2);
        assert_eq!(c2, 2);
    }

    /// Ensures that computing modulo a negative number results in a panic
    #[test]
    #[should_panic]
    fn rem_negative_error() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(-24);
        _ = &a % &b;
    }

    /// Ensures that computing modulo 0 results in a panic
    #[test]
    #[should_panic]
    fn zero_modulus() {
        _ = Z::from(15) % 0;
    }

    /// Ensures that `modulo` is available for several types.
    #[test]
    fn availability() {
        let _ = Z::ONE % 2u8;
        let _ = Z::ONE % 2u16;
        let _ = Z::ONE % 2u32;
        let _ = Z::ONE % 2u64;
        let _ = Z::ONE % 2i8;
        let _ = Z::ONE % 2i16;
        let _ = Z::ONE % 2i32;
        let _ = Z::ONE % 2i64;
        let _ = Z::ONE % Z::from(2);
        let _ = Z::ONE % Modulus::from(2);

        let _ = &Z::ONE % 2u8;
        let _ = 1u8 % Z::from(2);
        let _ = 1u8 % &Z::from(2);
    }
}
