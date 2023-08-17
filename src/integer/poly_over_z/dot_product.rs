// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute the dot product of two polynomials.

use crate::integer::PolyOverZ;
use crate::{error::MathError, integer::Z};
use flint_sys::fmpz::{fmpz_add, fmpz_mul};
use flint_sys::fmpz_poly::fmpz_poly_get_coeff_fmpz;

impl PolyOverZ {
    /// Returns the dot product of two polynomials of type [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the other polynomial the dot product is calculated over
    ///
    /// Returns the resulting `dot_product` as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let poly2 = PolyOverZ::from(42);
    ///
    /// let dot_prod = poly1.dot_product(&poly2).unwrap();
    /// ```
    pub fn dot_product(&self, other: &Self) -> Result<Z, MathError> {
        let self_degree = self.get_degree();
        let other_degree = other.get_degree();

        let mut smaller_degree = self_degree;
        if smaller_degree > other_degree {
            smaller_degree = other_degree;
        }

        // calculate dot product of polynomials
        let mut result = Z::default();
        let mut temp = Z::default();
        for i in 0..=smaller_degree {
            // sets result = result + coefficient1 * coefficient2
            unsafe {
                let mut coefficient1 = Z::default();
                let mut coefficient2 = Z::default();
                fmpz_poly_get_coeff_fmpz(&mut coefficient1.value, &self.poly, i);
                fmpz_poly_get_coeff_fmpz(&mut coefficient2.value, &other.poly, i);

                fmpz_mul(&mut temp.value, &coefficient1.value, &coefficient2.value);

                fmpz_add(&mut result.value, &result.value, &temp.value)
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test_dot_product {
    use crate::integer::{PolyOverZ, Z};
    use std::str::FromStr;

    /// Check whether the dot product is calculated correctly
    #[test]
    fn dot_product_correct() {
        let poly1 = PolyOverZ::from_str("2  1 1").unwrap();
        let poly2 = PolyOverZ::from_str("2  3 4").unwrap();

        let cmp = Z::from(7);
        let dot_prod = poly1.dot_product(&poly2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product is calculated correctly with large numbers.
    #[test]
    fn large_numbers() {
        let poly1 = PolyOverZ::from_str("3  6 2 4").unwrap();
        let poly2 = PolyOverZ::from_str(&format!("3  1 2 {}", i64::MAX / 8)).unwrap();

        let cmp = Z::from(10 + 4 * (i64::MAX / 8));
        let dot_prod = poly1.dot_product(&poly2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product calculation on
    /// polynomials of different lengths works.
    #[test]
    fn different_lengths_work() {
        let poly1 = PolyOverZ::from_str("3  1 2 3").unwrap();
        let poly2 = PolyOverZ::from_str("2  3 4").unwrap();

        let cmp = Z::from(11);
        let dot_prod = poly1.dot_product(&poly2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product calculation on
    /// polynomials with length 0 works.
    #[test]
    fn zero_length_works() {
        let poly1 = PolyOverZ::from_str("3  1 2 3").unwrap();
        let poly2 = PolyOverZ::from(0);

        let cmp = Z::from(0);
        let dot_prod = poly1.dot_product(&poly2).unwrap();

        assert_eq!(dot_prod, cmp);
    }
}
