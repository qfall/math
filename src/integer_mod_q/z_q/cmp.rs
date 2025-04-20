// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations for comparison of [`Zq`].

use super::Zq;
use crate::{
    error::MathError, integer::Z, macros::compare_base::compare_base_get_mod,
    macros::compare_base::compare_base_impl, traits::CompareBase,
};

compare_base_get_mod!(Zq for Zq);
impl<Integer: Into<Z>> CompareBase<Integer> for Zq {}

/// Test that the [`CompareBase`] trait uses an actual implementation.
#[cfg(test)]
mod test_compare_base {
    use crate::{integer_mod_q::Zq, traits::CompareBase};
    use std::str::FromStr;

    /// Ensures that the [`CompareBase`] trait uses an actual implementation.
    #[test]
    fn different_base() {
        let v1 = Zq::from_str("2 mod 17").unwrap();
        let v2 = Zq::from_str("2 mod 19").unwrap();

        assert!(!v1.compare_base(&v2));
        assert!(v1.call_compare_base_error(&v2).is_some())
    }

    /// Ensures that the same base return `true`.
    #[test]
    fn same_base() {
        let v1 = Zq::from_str("2 mod 17").unwrap();
        let v2 = Zq::from_str("2 mod 17").unwrap();

        assert!(v1.compare_base(&v2));
    }
}
