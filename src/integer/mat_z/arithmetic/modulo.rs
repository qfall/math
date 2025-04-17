// Copyright © 2025 Marcel Luca Schmidt
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
    macros::{
        arithmetics::{arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned},
        for_others::implement_for_others,
    },
    traits::{MatrixDimensions, MatrixGetEntry, MatrixSetEntry},
};
use flint_sys::fmpz_mat::fmpz_mat_scalar_smod;
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
        let num_cols = self.get_num_columns();
        let num_rows = self.get_num_rows();

        let mut out = MatZ::new(num_rows, num_cols);
        unsafe { fmpz_mat_scalar_smod(&mut out.matrix, &self.matrix, &modulus.value) };

        for i in 0..num_rows {
            for j in 0..num_cols {
                let entry = unsafe { out.get_entry_unchecked(i, j) };
                if entry < 0 {
                    unsafe { out.set_entry_unchecked(i, j, entry + modulus) };
                }
            }
        }

        out
    }
}

arithmetic_trait_borrowed_to_owned!(Rem, rem, MatZ, Z, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Rem, rem, MatZ, Z, MatZ);

implement_for_others!(Z, MatZ, Rem for i8 i16 i32 i64 u8 u16 u32 u64);

#[cfg(test)]
mod test_rem {
    use super::Z;
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Testing modulo for two owned
    #[test]
    fn rem() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(24);
        let c = a % b;
        assert_eq!(c, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
    }

    /// Testing modulo for two borrowed
    #[test]
    fn rem_borrow() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(24);
        let c = &a % &b;
        assert_eq!(c, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
    }

    /// Testing modulo for borrowed and owned
    #[test]
    fn rem_first_borrowed() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(24);
        let c = &a % b;
        assert_eq!(c, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
    }

    /// Testing modulo for owned and borrowed
    #[test]
    fn rem_second_borrowed() {
        let a = MatZ::from_str("[[2, 3],[42, 24]]").unwrap();
        let b = Z::from(24);
        let c = a % &b;
        assert_eq!(c, MatZ::from_str("[[2, 3],[18, 0]]").unwrap());
    }

    /// Testing modulo for negative values
    #[test]
    fn rem_negative_representation() {
        let a = MatZ::from_str("[[-2, 3],[42, 24]]").unwrap();
        let b = Z::from(24);
        let c = &a % &b;
        assert_eq!(c, MatZ::from_str("[[22, 3],[18, 0]]").unwrap());
    }

    /// Testing modulo for large numbers
    #[test]
    fn rem_large_numbers() {
        let a = MatZ::from_str(&format!("[[2, 3],[{}, 24]]", u64::MAX)).unwrap();
        let b = Z::from(u64::MAX - 2);
        let c = &a % &b;
        assert_eq!(c, MatZ::from_str("[[2, 3],[2, 24]]").unwrap());
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

    /// Ensures that `modulo` is available for several types implementing [`Into<Z>`].
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

        let _ = &MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % 2u8;
        let _ = MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % &Z::from(2);
        let _ = &MatZ::from_str("[[2, 3],[42, 24]]").unwrap() % &Z::from(2);
    }
}
