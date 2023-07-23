// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`PolyOverZ`].

use super::PolyOverZ;
use crate::{error::MathError, integer::Z, traits::GetCoefficient, utils::index::evaluate_index};
use flint_sys::fmpz_poly::{fmpz_poly_degree, fmpz_poly_get_coeff_fmpz};
use std::fmt::Display;

impl GetCoefficient<Z> for PolyOverZ {
    /// Returns the coefficient of a polynomial [`PolyOverZ`] as a [`Z`].
    ///
    /// If an index is provided which exceeds the highest set coefficient, `0` is returned.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to get (has to be positive)
    ///
    /// Returns the coefficient as a [`Z`] or a [`MathError`] if the provided index
    /// is negative and therefore invalid or it does not fit into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    /// use qfall_math::traits::*;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    ///
    /// let coeff_0 = poly.get_coeff(0).unwrap();
    /// let coeff_1 = poly.get_coeff(1).unwrap();
    /// let coeff_4 = poly.get_coeff(4).unwrap(); // This would only return 0
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the index is negative or it does not fit into an [`i64`].
    fn get_coeff(&self, index: impl TryInto<i64> + Display) -> Result<Z, MathError> {
        let mut out = Z::default();
        let index = evaluate_index(index)?;
        unsafe { fmpz_poly_get_coeff_fmpz(&mut out.value, &self.poly, index) }
        Ok(out)
    }
}

impl PolyOverZ {
    /// Returns the degree of a polynomial [`PolyOverZ`] as a [`i64`].
    /// The zero polynomial has degree '-1'.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    ///
    /// let degree = poly.get_degree();
    /// assert_eq!(3, degree);
    /// ```
    pub fn get_degree(&self) -> i64 {
        unsafe { fmpz_poly_degree(&self.poly) }
    }
}

#[cfg(test)]
mod test_get_coeff {
    use crate::{
        integer::{PolyOverZ, Z},
        traits::GetCoefficient,
    };
    use std::str::FromStr;

    /// Ensure that 0 is returned if the provided index is not yet set
    #[test]
    fn index_out_of_range() {
        let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();

        let zero_coeff = poly.get_coeff(4).unwrap();

        assert_eq!(Z::ZERO, zero_coeff)
    }

    /// Tests if negative coefficients are returned correctly
    #[test]
    fn negative_coeff() {
        let poly = PolyOverZ::from_str("4  0 1 2 -3").unwrap();

        let coeff = poly.get_coeff(3).unwrap();

        assert_eq!(Z::from(-3), coeff)
    }

    /// Tests if positive coefficients are returned correctly
    #[test]
    fn positive_coeff() {
        let poly = PolyOverZ::from_str("4  0 1 2 -3").unwrap();

        let coeff = poly.get_coeff(2).unwrap();

        assert_eq!(Z::from(2), coeff)
    }

    /// Tests if large coefficients are returned correctly
    #[test]
    fn large_coeff() {
        let large_string = format!("2  {} {}", u64::MAX, i64::MIN);
        let poly = PolyOverZ::from_str(&large_string).unwrap();

        assert_eq!(Z::from(u64::MAX), poly.get_coeff(0).unwrap());
        assert_eq!(Z::from(i64::MIN), poly.get_coeff(1).unwrap());
    }

    /// Tests if large negative coefficients are returned correctly
    #[test]
    fn large_coeff_neg() {
        let large_string = format!("2  -{} {}", u64::MAX, i64::MIN);
        let poly = PolyOverZ::from_str(&large_string).unwrap();

        assert_eq!(
            Z::from_str(&format!("-{}", u64::MAX)).unwrap(),
            poly.get_coeff(0).unwrap()
        );
        assert_eq!(Z::from(i64::MIN), poly.get_coeff(1).unwrap());
    }
}

#[cfg(test)]
mod test_get_degree {
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that degree is working
    #[test]
    fn degree() {
        let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();

        let deg = poly.get_degree();

        assert_eq!(3, deg);
    }

    /// Ensure that degree is working for constant polynomials
    #[test]
    fn degree_constant() {
        let poly1 = PolyOverZ::from_str("1  1").unwrap();
        let poly2 = PolyOverZ::default();

        let deg1 = poly1.get_degree();
        let deg2 = poly2.get_degree();

        assert_eq!(0, deg1);
        assert_eq!(-1, deg2);
    }

    /// Ensure that degree is working for polynomials with leading 0 coefficients
    #[test]
    fn degree_leading_zeros() {
        let poly = PolyOverZ::from_str("4  1 0 0 0").unwrap();

        let deg = poly.get_degree();

        assert_eq!(0, deg);
    }
}
