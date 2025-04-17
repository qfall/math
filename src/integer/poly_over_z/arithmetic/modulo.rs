// Copyright © 2025 Marcel Luca Schmidt
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

arithmetic_trait_borrowed_to_owned!(Rem, rem, PolyOverZ, Z, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Rem, rem, PolyOverZ, Z, PolyOverZ);

implement_for_others!(Z, PolyOverZ, Rem for i8 i16 i32 i64 u8 u16 u32 u64);

#[cfg(test)]
mod test_rem {
    use super::Z;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Testing modulo for two owned
    #[test]
    fn rem() {
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let b = Z::from(24);
        let c = a % b;
        assert_eq!(c, PolyOverZ::from_str("2  2 18").unwrap());
    }

    /// Testing modulo for two borrowed
    #[test]
    fn rem_borrow() {
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let b = Z::from(24);
        let c = &a % &b;
        assert_eq!(c, PolyOverZ::from_str("2  2 18").unwrap());
    }

    /// Testing modulo for borrowed and owned
    #[test]
    fn rem_first_borrowed() {
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let b = Z::from(24);
        let c = &a % b;
        assert_eq!(c, PolyOverZ::from_str("2  2 18").unwrap());
    }

    /// Testing modulo for owned and borrowed
    #[test]
    fn rem_second_borrowed() {
        let a = PolyOverZ::from_str("2  2 42").unwrap();
        let b = Z::from(24);
        let c = a % &b;
        assert_eq!(c, PolyOverZ::from_str("2  2 18").unwrap());
    }

    /// Testing modulo for negative values
    #[test]
    fn rem_negative_representation() {
        let a = PolyOverZ::from_str("2  -2 42").unwrap();
        let b = Z::from(24);
        let c = &a % &b;
        assert_eq!(c, PolyOverZ::from_str("2  22 18").unwrap());
    }

    /// Testing modulo for large numbers
    #[test]
    fn rem_large_numbers() {
        let a = PolyOverZ::from_str(&format!("2  2 {}", u64::MAX)).unwrap();
        let b = Z::from(u64::MAX - 2);
        let c = &a % &b;
        assert_eq!(c, PolyOverZ::from_str("2  2 2").unwrap());
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

    /// Ensures that `modulo` is available for several types implementing [`Into<Z>`].
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

        let _ = &PolyOverZ::from_str("2  2 42").unwrap() % 2u8;
        let _ = PolyOverZ::from_str("2  2 42").unwrap() % &Z::from(2);
        let _ = &PolyOverZ::from_str("2  2 42").unwrap() % &Z::from(2);
    }
}
