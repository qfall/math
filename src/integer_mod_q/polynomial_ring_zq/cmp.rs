// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations for comparison of [`PolynomialRingZq`].

use super::PolynomialRingZq;
use crate::{error::MathError, traits::CompareBase};

impl CompareBase for PolynomialRingZq {
    /// Compares the moduli of the two elements.
    ///
    /// Parameters:
    /// - `other`: The other object whose base is compared to `self`
    ///
    /// Returns true if the moduli match and false otherwise.
    ///
    /// # Example
    /// ```
    /// use qfall_math::{integer_mod_q::PolynomialRingZq, traits::CompareBase};
    /// use std::str::FromStr;
    ///
    /// let p1 = PolynomialRingZq::from_str("0 / 3  1 1 2 mod 7").unwrap();
    /// let p2 = PolynomialRingZq::from_str("2  7 14 / 2  1 1  mod 7").unwrap();
    ///
    /// assert!(!p1.compare_base(&p2));
    /// ```
    fn compare_base(&self, other: &Self) -> bool {
        self.get_mod() == other.get_mod()
    }

    /// Returns an error that gives small explanation how the moduli differ.
    ///
    /// Parameters:
    /// - `other`: The other object whose base is compared to `self`
    ///
    /// Returns a MathError of type [MathError::MismatchingModulus].
    ///
    /// # Example
    /// ```
    /// use qfall_math::{integer_mod_q::PolynomialRingZq, traits::CompareBase};
    /// use std::str::FromStr;
    ///
    /// let p1 = PolynomialRingZq::from_str("0 / 3  1 1 2 mod 7").unwrap();
    /// let p2 = PolynomialRingZq::from_str("2  7 14 / 2  1 1  mod 7").unwrap();
    ///
    /// assert!(p1.call_compare_base_error(&p2).is_some())
    /// ```
    fn call_compare_base_error(&self, other: &Self) -> Option<MathError> {
        Some(MathError::MismatchingModulus(format!(
            "The moduli of the polynomial ring elements mismatch. One of them is {} and the other is {}.
            The desired operation is not defined and an error is returned.",
            self.get_mod(),
            other.get_mod()
        )))
    }
}

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
