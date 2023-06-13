// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`PolyOverZ`] instances.

use super::PolyOverZ;
use flint_sys::fmpz_poly::{fmpz_poly_degree, fmpz_poly_is_one};

impl PolyOverZ {
    /// Checks if a [`PolyOverZ`] is the constant polynomial with coefficient `1`.
    ///
    /// Returns true if there is only one coefficient, which is `1`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let value = PolyOverZ::from_str("1  1").unwrap();
    /// assert!(value.is_one())
    /// ```
    pub fn is_one(&self) -> bool {
        1 == unsafe { fmpz_poly_is_one(&self.poly) }
    }

    /// Checks if every entry of a [`PolyOverZ`] is `0`.
    ///
    /// Returns true if [`PolyOverZ`] has no coefficients.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let value = PolyOverZ::from_str("0").unwrap();
    /// assert!(value.is_zero())
    /// ```
    pub fn is_zero(&self) -> bool {
        -1 == unsafe { fmpz_poly_degree(&self.poly) }
    }
}

#[cfg(test)]
mod test_is_one {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that is_one returns `true` for the one polynomial.
    #[test]
    fn one_detection() {
        let constant1 = PolyOverZ::from_str("1  1").unwrap();
        let constant2 = PolyOverZ::from_str("3  1 0 0").unwrap();

        assert!(constant1.is_one());
        assert!(constant2.is_one());
    }

    /// Ensure that is_one returns `false` for other polynomials.
    #[test]
    fn one_rejection() {
        let small = PolyOverZ::from_str("4  1 0 0 1").unwrap();
        let large = PolyOverZ::from_str(&format!("1  {}", (u128::MAX - 1) / 2 + 2)).unwrap();

        assert!(!small.is_one());
        assert!(!large.is_one());
    }
}

#[cfg(test)]
mod test_is_zero {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that is_zero returns `true` for the zero polynomial.
    #[test]
    fn zero_detection() {
        let zero1 = PolyOverZ::from_str("0").unwrap();
        let zero2 = PolyOverZ::from_str("3  0 0 0").unwrap();

        assert!(zero1.is_zero());
        assert!(zero2.is_zero());
    }

    /// Ensure that is_zero returns `false` for non-zero polynomials.
    #[test]
    fn zero_rejection() {
        let small = PolyOverZ::from_str("4  0 0 0 1").unwrap();
        let large = PolyOverZ::from_str(&format!("1  {}", (u128::MAX - 1) / 2 + 1)).unwrap();

        assert!(!small.is_zero());
        assert!(!large.is_zero());
    }
}
