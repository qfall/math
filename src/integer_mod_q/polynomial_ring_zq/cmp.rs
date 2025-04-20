// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations for comparison of [`PolynomialRingZq`].

use super::PolynomialRingZq;
use crate::{
    error::MathError,
    integer::{PolyOverZ, Z},
    integer_mod_q::{PolyOverZq, Zq},
    macros::compare_base::{
        compare_base_default, compare_base_get_mod, compare_base_get_mod_get_q, compare_base_impl,
    },
    traits::CompareBase,
};

compare_base_default!(PolynomialRingZq for PolyOverZ);
compare_base_get_mod!(PolynomialRingZq for PolynomialRingZq);
compare_base_get_mod_get_q!(PolynomialRingZq for Zq PolyOverZq);
impl<Integer: Into<Z>> CompareBase<Integer> for PolynomialRingZq {}

/// Test that the [`CompareBase`] trait uses an actual implementation.
#[cfg(test)]
mod test_compare_base {
    use crate::{
        integer::{PolyOverZ, Z},
        integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq, Zq},
        traits::CompareBase,
    };
    use std::str::FromStr;

    /// Ensures that the [`CompareBase`] is available for all types it would be checked against
    /// where no comparison is needed
    #[test]
    fn availability_without_comparisons() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let one_1 = PolynomialRingZq::from(&modulus);

        assert!(one_1.compare_base(&Z::ONE));
        assert!(one_1.compare_base(&PolyOverZ::from_str("1  3").unwrap()));
        assert!(one_1.compare_base(&0_i8));
        assert!(one_1.compare_base(&0_i16));
        assert!(one_1.compare_base(&0_i32));
        assert!(one_1.compare_base(&0_i64));
        assert!(one_1.compare_base(&0_u8));
        assert!(one_1.compare_base(&0_u16));
        assert!(one_1.compare_base(&0_u32));
        assert!(one_1.compare_base(&0_u64));

        assert!(one_1.call_compare_base_error(&Z::ONE).is_none());
        assert!(one_1
            .call_compare_base_error(&PolyOverZ::from_str("1  3").unwrap())
            .is_none());
        assert!(one_1.call_compare_base_error(&0_i8).is_none());
        assert!(one_1.call_compare_base_error(&0_i16).is_none());
        assert!(one_1.call_compare_base_error(&0_i32).is_none());
        assert!(one_1.call_compare_base_error(&0_i64).is_none());
        assert!(one_1.call_compare_base_error(&0_u8).is_none());
        assert!(one_1.call_compare_base_error(&0_u16).is_none());
        assert!(one_1.call_compare_base_error(&0_u32).is_none());
        assert!(one_1.call_compare_base_error(&0_u64).is_none());
    }

    /// Ensures that the [`CompareBase`] is available for all types it would be checked against
    /// where comparison is needed
    #[test]
    fn availability_with_comparisons() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let modulus_other = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 18").unwrap();
        let one_1 = PolynomialRingZq::from(&modulus);

        assert!(one_1.compare_base(&one_1));
        assert!(one_1.compare_base(&Zq::from((3, 17))));
        assert!(!one_1.compare_base(&Zq::from((3, 18))));
        assert!(one_1.compare_base(&PolyOverZq::from_str("1  3 mod 17").unwrap()));
        assert!(!one_1.compare_base(&PolyOverZq::from_str("1  3 mod 18").unwrap()));
        assert!(one_1.compare_base(&PolynomialRingZq::from(&modulus)));
        assert!(!one_1.compare_base(&PolynomialRingZq::from(&modulus_other)));

        assert!(one_1.call_compare_base_error(&Zq::from((3, 18))).is_some());
        assert!(one_1
            .call_compare_base_error(&PolyOverZq::from_str("1  3 mod 18").unwrap())
            .is_some());
        assert!(one_1
            .call_compare_base_error(&PolynomialRingZq::from(&modulus_other))
            .is_some());
    }
}
