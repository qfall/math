// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute the dot product of two polynomials.

use crate::integer_mod_q::{PolynomialRingZq, Zq};
use crate::traits::GetCoefficient;
use crate::{error::MathError, integer::Z};

impl PolynomialRingZq {
    /// Returns the dot product of two polynomials of type [`PolynomialRingZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the other polynomial the dot product is calculated over
    ///
    /// Returns the resulting `dot_product` as a [`PolynomialRingZq`] or an error
    /// if the moduli mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolynomialRingZq::from_str("4  1 0 2 1 / 5  1 2 3 4 5 mod 11").unwrap();
    /// let poly_2 = PolynomialRingZq::from_str("1  9 / 5  1 2 3 4 5 mod 11").unwrap();
    ///
    /// let dot_prod = poly_1.dot_product(&poly_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`MathError::MismatchingModulus`] if the moduli mismatch.
    pub fn dot_product(&self, other: &Self) -> Result<Zq, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Modulus of self: '{}'. Modulus of other: '{}'.
                If the modulus should be ignored please convert into a PolyOverZ beforehand.",
                self.modulus, other.modulus
            )));
        }

        let self_degree = self.get_degree();
        let other_degree = other.get_degree();

        let mut smaller_degree = self_degree;
        if smaller_degree > other_degree {
            smaller_degree = other_degree;
        }

        // calculate dot product of polynomials
        let mut result = Zq::from((Z::default(), self.modulus.get_q()));
        for i in 0..=smaller_degree {
            let coefficient_1: Z = self.get_coeff(i).unwrap();
            let coefficient_2: Z = other.get_coeff(i).unwrap();

            result = result + coefficient_1 * coefficient_2;
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test_dot_product {
    use crate::integer_mod_q::{PolynomialRingZq, Zq};
    use std::str::FromStr;

    /// Check whether the dot product is calculated correctly
    #[test]
    fn dot_product_correct() {
        let poly_1 = PolynomialRingZq::from_str("2  1 1 / 5  1 2 3 4 5 mod 8").unwrap();
        let poly_2 = PolynomialRingZq::from_str("2  3 4 / 5  1 2 3 4 5 mod 8").unwrap();

        let cmp = Zq::from((7, 8));
        let dot_prod = poly_1.dot_product(&poly_2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product is calculated correctly with large numbers.
    #[test]
    fn large_numbers() {
        let poly_1 =
            PolynomialRingZq::from_str(&format!("3  6 2 4 / 5  1 2 3 4 5 mod {}", i64::MAX))
                .unwrap();
        let poly_2 = PolynomialRingZq::from_str(&format!(
            "3  1 2 {} / 5  1 2 3 4 5 mod {}",
            i64::MAX / 8,
            i64::MAX
        ))
        .unwrap();

        let cmp = Zq::from(((10 + 4 * (i64::MAX / 8)), i64::MAX));
        let dot_prod = poly_1.dot_product(&poly_2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product calculation on
    /// polynomials of different lengths works.
    #[test]
    fn different_lengths_work() {
        let poly_1 = PolynomialRingZq::from_str("3  1 2 3 / 5  1 2 3 4 5 mod 11").unwrap();
        let poly_2 = PolynomialRingZq::from_str("2  3 4 / 5  1 2 3 4 5 mod 11").unwrap();

        let cmp = Zq::from((0, 11));
        let dot_prod = poly_1.dot_product(&poly_2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product calculation on
    /// polynomials with length 0 works.
    #[test]
    fn zero_length_works() {
        let poly_1 = PolynomialRingZq::from_str("3  1 2 3 / 5  1 2 3 4 5 mod 15").unwrap();
        let poly_2 = PolynomialRingZq::from_str("0 / 5  1 2 3 4 5 mod 15").unwrap();

        let cmp = Zq::from((0, 15));
        let dot_prod = poly_1.dot_product(&poly_2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product calculation on
    /// polynomials with different moduli yields an error.
    #[test]
    fn modulus_error() {
        let poly_1 = PolynomialRingZq::from_str("3  1 2 3 / 5  1 2 3 4 5 mod 15").unwrap();
        let poly_2 = PolynomialRingZq::from_str("2  1 4 / 5  1 2 3 4 5 mod 14").unwrap();

        let dot_prod = poly_1.dot_product(&poly_2);

        assert!(dot_prod.is_err());
    }
}
