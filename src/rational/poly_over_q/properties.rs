// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`PolyOverQ`] instances.

use flint_sys::fmpq_poly::{fmpq_poly_degree, fmpq_poly_is_one};

use super::PolyOverQ;

impl PolyOverQ {
    /// Checks if a [`PolyOverQ`] is the constant polynomial with coefficient `1`.
    ///
    /// Returns true if the first coefficient is `1` and is the only coefficient
    ///
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let value = PolyOverQ::from_str("1  1").unwrap();
    /// assert!(value.is_one())
    /// ```
    pub fn is_one(&self) -> bool {
        1 == unsafe { fmpq_poly_is_one(&self.poly) }
    }

    /// Checks if every entry of a [`PolyOverQ`] is `0`.
    ///
    /// Returns true if [`PolyOverQ`] has no coefficients
    ///
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let value = PolyOverQ::from_str("0").unwrap();
    /// assert!(value.is_zero())
    /// ```
    pub fn is_zero(&self) -> bool {
        -1 == unsafe { fmpq_poly_degree(&self.poly) }
    }
}

#[cfg(test)]
mod test_is_one {
    use super::PolyOverQ;
    use std::str::FromStr;

    /// ensure that is_one returns `true` for the one polynomial
    #[test]
    fn one_detection() {
        let one = PolyOverQ::from_str("1  1").unwrap();

        assert!(one.is_one());
    }

    /// ensure that is_one returns `false` for other polynomials
    #[test]
    fn one_rejection() {
        let small = PolyOverQ::from_str("4  1 0 0 1/123").unwrap();
        let large = PolyOverQ::from_str(&format!("1  {}", (u128::MAX - 1) / 2 + 2)).unwrap();

        assert!(!(small.is_one()));
        assert!(!(large.is_one()));
    }
}

#[cfg(test)]
mod test_is_zero {
    use super::PolyOverQ;
    use std::str::FromStr;

    /// ensure that is_zero returns `true` for the zero polynomial
    #[test]
    fn zero_detection() {
        let zero = PolyOverQ::from_str("0").unwrap();

        assert!(zero.is_zero());
    }

    /// ensure that is_zero returns `false` for non-zero polynomials
    #[test]
    fn zero_rejection() {
        let small = PolyOverQ::from_str("4  0 0 0 1/8").unwrap();
        let large = PolyOverQ::from_str(&format!("1  {}", (u128::MAX - 1) / 2 + 1)).unwrap();

        assert!(!(small.is_zero()));
        assert!(!(large.is_zero()));
    }
}
