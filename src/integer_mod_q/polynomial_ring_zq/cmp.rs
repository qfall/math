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
        compare_base_default, compare_base_get_mod, compare_base_get_mod_get_q,
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
    use crate::{integer_mod_q::PolynomialRingZq, traits::CompareBase};
    use std::str::FromStr;

    /// Ensures that the [`CompareBase`] trait uses an actual implementation.
    #[test]
    fn different_base() {
        let p1 = PolynomialRingZq::from_str("0 / 3  1 1 2 mod 7").unwrap();
        let p2 = PolynomialRingZq::from_str("2  7 14 / 2  1 1  mod 7").unwrap();

        assert!(!p1.compare_base(&p2));
        assert!(p1.call_compare_base_error(&p2).is_some())
    }

    /// Ensures that the same base return `true`.
    #[test]
    fn same_base() {
        let p1 = PolynomialRingZq::from_str("0 / 2  1 1 mod 7").unwrap();
        let p2 = PolynomialRingZq::from_str("2  7 14 / 2  1 1  mod 7").unwrap();

        assert!(p1.compare_base(&p2));
    }
}
