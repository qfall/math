// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to check certain properties of [`PolynomialRingZq`].
//! This includes checks such as reducibility.

use super::PolynomialRingZq;
use crate::integer_mod_q::PolyOverZq;

impl PolynomialRingZq {
    /// Checks if a [`PolynomialRingZq`] is irreducible.
    ///
    /// Returns `true` if the polynomial is irreducible and `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly_irr = PolynomialRingZq::from_str("2  1 1 / 3  1 2 3 mod 17").unwrap();
    /// // returns true, since X + 1 is irreducible
    /// assert!(poly_irr.is_irreducible());
    /// ```
    pub fn is_irreducible(&self) -> bool {
        let poly_over_zq = PolyOverZq::from((&self.poly, self.modulus.get_q()));

        // Since after reduction with the polynomial modulus, the check of
        // irreducibility is the same as without the polynomial modulus
        poly_over_zq.is_irreducible()
    }

    /// Checks if a [`PolynomialRingZq`] is the constant polynomial with coefficient `1`.
    ///
    /// Returns `true` if there is only one coefficient, which is `1`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let value = PolynomialRingZq::from_str("1  1 / 3  1 0 1 mod 4").unwrap();
    /// assert!(value.is_one());
    /// ```
    pub fn is_one(&self) -> bool {
        self.poly.is_one()
    }

    /// Checks if every entry of a [`PolynomialRingZq`] is `0`.
    ///
    /// Returns `true` if [`PolynomialRingZq`] has no coefficients.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let value = PolynomialRingZq::from_str("0 / 2  1 1 mod 7").unwrap();
    /// assert!(value.is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        self.poly.is_zero()
    }
}

#[cfg(test)]
mod test_is_irreducible {
    use crate::integer_mod_q::PolynomialRingZq;
    use std::str::FromStr;

    /// Ensure that a irreducible [`PolynomialRingZq`] returns `true`.
    #[test]
    fn poly_is_irreducible() {
        // 9X^2 + 12X + 10 is irreducible over 17
        let poly_irr = PolynomialRingZq::from_str("3  10 12 9 / 4  1 10 12 9 mod 17").unwrap();
        print!("{}", poly_irr);
        assert!(poly_irr.is_irreducible());
    }

    /// Ensure that a reducible [`PolynomialRingZq`] returns `false`.
    #[test]
    fn poly_is_reducible() {
        let poly_irr = PolynomialRingZq::from_str("3  1 2 1 / 4  1 10 12 9 mod 17").unwrap();
        assert!(!poly_irr.is_irreducible());
    }
}

#[cfg(test)]
mod test_is_one {
    use super::PolynomialRingZq;
    use std::str::FromStr;

    /// Ensure that is_one returns `true` for the one polynomial.
    #[test]
    fn one_detection() {
        let one = PolynomialRingZq::from_str("1  1 / 4  1 10 12 9 mod 7").unwrap();
        let one_2 = PolynomialRingZq::from_str("2  1 14 / 4  1 10 12 9 mod 7").unwrap();

        assert!(one.is_one());
        assert!(one_2.is_one());
    }

    /// Ensure that is_one returns `false` for other polynomials.
    #[test]
    fn one_rejection() {
        let small = PolynomialRingZq::from_str("4  1 0 0 1 / 4  1 10 12 9 mod 7").unwrap();
        let large = PolynomialRingZq::from_str(&format!(
            "1  {} / 4  1 10 12 9 mod {}",
            (u128::MAX - 1) / 2 + 2,
            u128::MAX
        )) //2^127 + 1 the last memory entry is `1`
        .unwrap();

        assert!(!small.is_one());
        assert!(!large.is_one());
    }
}

#[cfg(test)]
mod test_is_zero {
    use super::PolynomialRingZq;
    use std::str::FromStr;

    /// Ensure that is_zero returns `true` for the zero polynomial.
    #[test]
    fn zero_detection() {
        let zero = PolynomialRingZq::from_str("0 / 2  1 1 mod 7").unwrap();
        let zero_2 = PolynomialRingZq::from_str("2  7 14 / 2  1 1  mod 7").unwrap();

        assert!(zero.is_zero());
        assert!(zero_2.is_zero());
    }

    /// Ensure that is_zero returns `false` for non-zero polynomials.
    #[test]
    fn zero_rejection() {
        let small = PolynomialRingZq::from_str("4  0 0 0 1 / 2  1 1 mod 7").unwrap();
        let large = PolynomialRingZq::from_str(&format!(
            "1  {} / 2  1 1 mod {}",
            (u128::MAX - 1) / 2 + 1,
            u128::MAX
        )) //last 126 bits are 0
        .unwrap();

        assert!(!small.is_zero());
        assert!(!large.is_zero());
    }
}
