// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the `mod±` function for [`MatZq`] values.

use crate::{
    integer::{MatZ, Z},
    integer_mod_q::MatZq,
    traits::{MatrixDimensions, MatrixGetEntry, MatrixSetEntry},
};
use std::ops::Rem;

impl MatZq {
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
    /// use qfall_math::{integer_mod_q::MatZq, integer::MatZ};
    /// use std::str::FromStr;
    ///
    /// let a = MatZq::from_str("[[2],[42]] mod 24").unwrap();
    ///
    /// let c = a.mod_pm(24);
    ///
    /// assert_eq!(MatZ::from_str("[[2],[-6]]").unwrap(), c);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    pub fn mod_pm(&self, modulus: impl Into<Z>) -> MatZ {
        let modulus = modulus.into();
        assert!(modulus > 1, "Modulus can not be smaller than 2.");

        let mut mat = self
            .get_representative_least_nonnegative_residue()
            .rem(&modulus);

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
mod test_mod_pm {
    use super::Z;
    use crate::{
        integer::MatZ,
        integer_mod_q::{MatZq, Modulus},
    };
    use std::str::FromStr;

    /// Testing mod± for two owned
    #[test]
    fn mod_pm() {
        let a = MatZq::from_str("[[2, 3],[42, 24]] mod 257").unwrap();
        let b = Z::from(25);
        let c1 = a.clone().mod_pm(b);
        let c2 = a.mod_pm(Modulus::from(25));
        assert_eq!(c1, MatZ::from_str("[[2, 3],[-8, -1]]").unwrap());
        assert_eq!(c2, MatZ::from_str("[[2, 3],[-8, -1]]").unwrap());
    }

    /// Testing mod± for large numbers
    #[test]
    fn mod_pm_large_numbers() {
        let a =
            MatZq::from_str(&format!("[[2, 3],[{}, 24]] mod {}", u64::MAX - 1, u64::MAX)).unwrap();
        let b = Z::from(u64::MAX - 2);
        let c1 = a.mod_pm(&b);
        let c2 = a.mod_pm(&Modulus::from(u64::MAX - 2));
        assert_eq!(c1, MatZ::from_str("[[2, 3],[1, 24]]").unwrap());
        assert_eq!(c2, MatZ::from_str("[[2, 3],[1, 24]]").unwrap());
    }

    /// Ensures that computing mod± a negative number results in a panic
    #[test]
    #[should_panic]
    fn mod_pm_negative_error() {
        let a = MatZq::from_str("[[2, 3],[42, 24]] mod 25").unwrap();
        let b = Z::from(-24);
        _ = &a.mod_pm(&b);
    }

    /// Ensures that computing mod± 0 results in a panic
    #[test]
    #[should_panic]
    fn zero_modulus() {
        _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(0);
    }

    /// Ensures that `mod±` is available for several types.
    #[test]
    fn availability() {
        let _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(2u8);
        let _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(2u16);
        let _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(2u32);
        let _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(2u64);
        let _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(2i8);
        let _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(2i16);
        let _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(2i32);
        let _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(2i64);
        let _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(Z::from(2));
        let _ = MatZq::from_str("[[2, 3],[42, 24]] mod 25")
            .unwrap()
            .mod_pm(Modulus::from(2));
    }
}
