// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations for comparison of [`MatPolynomialRingZq`].

use super::MatPolynomialRingZq;
use crate::{
    error::MathError,
    integer::{MatPolyOverZ, MatZ, PolyOverZ, Z},
    integer_mod_q::{MatZq, PolyOverZq, PolynomialRingZq, Zq},
    macros::compare_base::{
        compare_base_default, compare_base_get_mod, compare_base_get_mod_get_q, compare_base_impl,
    },
    traits::CompareBase,
};

compare_base_get_mod!(MatPolynomialRingZq for MatPolynomialRingZq PolynomialRingZq);
compare_base_get_mod_get_q!(MatPolynomialRingZq for Zq MatZq PolyOverZq);

compare_base_default!(MatPolynomialRingZq for MatZ PolyOverZ MatPolyOverZ);
impl<Integer: Into<Z>> CompareBase<Integer> for MatPolynomialRingZq {}

/// Test that the [`CompareBase`] trait uses an actual implementation.
#[cfg(test)]
mod test_compare_base {
    use crate::{
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
        traits::CompareBase,
    };
    use std::str::FromStr;

    /// Ensures that the [`CompareBase`] trait uses an actual implementation.
    #[test]
    fn different_base() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let one_1 = MatPolynomialRingZq::identity(10, 7, &modulus);
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 23").unwrap();
        let one_2 = MatPolynomialRingZq::identity(10, 7, &modulus);

        assert!(!one_1.compare_base(&one_2));
        assert!(one_1.call_compare_base_error(&one_2).is_some())
    }

    /// Ensures that the same base return `true`.
    #[test]
    fn same_base() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let one_1 = MatPolynomialRingZq::identity(10, 7, &modulus);
        let one_2 = MatPolynomialRingZq::identity(29, 3, &modulus);

        assert!(one_1.compare_base(&one_2));
    }
}
