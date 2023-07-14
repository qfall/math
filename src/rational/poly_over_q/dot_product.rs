// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute the dot product of two polynomials.

use crate::error::MathError;
use crate::rational::{PolyOverQ, Q};
use flint_sys::fmpq::{fmpq_add, fmpq_mul};
use flint_sys::fmpq_poly::fmpq_poly_get_coeff_fmpq;

impl PolyOverQ {
    /// Returns the dot product of two polynomials of type [`PolyOverQ`].
    ///
    /// Parameters:
    /// - `other`: specifies the other polynomial the dot product is calculated over
    ///
    /// Returns the resulting `dot_product` as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let poly1 = PolyOverQ::from_str("4  -1/2 0 7/8 1").unwrap();
    /// let poly2 = PolyOverQ::from_str("1  5/42").unwrap();
    ///
    /// let dot_prod = poly1.dot_product(&poly2).unwrap();
    /// ```
    pub fn dot_product(&self, other: &Self) -> Result<Q, MathError> {
        let self_degree = self.get_degree();
        let other_degree = other.get_degree();

        let mut smaller_degree = self_degree;
        if smaller_degree > other_degree {
            smaller_degree = other_degree;
        }

        // calculate dot product of polynomials
        let mut result = Q::default();
        let mut temp = Q::default();
        for i in 0..smaller_degree + 1 {
            // sets result = result + coefficient1 * coefficient2
            unsafe {
                let mut coefficient1 = Q::default();
                let mut coefficient2 = Q::default();
                fmpq_poly_get_coeff_fmpq(&mut coefficient1.value, &self.poly, i);
                fmpq_poly_get_coeff_fmpq(&mut coefficient2.value, &other.poly, i);

                fmpq_mul(&mut temp.value, &coefficient1.value, &coefficient2.value);

                fmpq_add(&mut result.value, &result.value, &temp.value)
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test_dot_product {
    use crate::rational::{PolyOverQ, Q};
    use std::str::FromStr;

    /// Check whether the dot product is calculated correctly
    #[test]
    fn dot_product_correct() {
        let poly1 = PolyOverQ::from_str("2  1/2 1").unwrap();
        let poly2 = PolyOverQ::from_str("2  3 4/2").unwrap();

        let cmp = Q::from((7, 2));
        let dot_prod = poly1.dot_product(&poly2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product is calculated correctly with large numbers.
    #[test]
    fn large_numbers() {
        let poly1 = PolyOverQ::from_str("3  6 2 2").unwrap();
        let poly2 = PolyOverQ::from_str(&format!("3  1 2 {}", i64::MAX / 3)).unwrap();

        let cmp = Q::from(10 + 2 * (i64::MAX / 3));
        let dot_prod = poly1.dot_product(&poly2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product calculation on
    /// polynomials of different lengths works.
    #[test]
    fn different_lengths_work() {
        let poly1 = PolyOverQ::from_str("3  1 2 3/7").unwrap();
        let poly2 = PolyOverQ::from_str("2  3 4").unwrap();

        let cmp = Q::from(11);
        let dot_prod = poly1.dot_product(&poly2).unwrap();

        assert_eq!(dot_prod, cmp);
    }

    /// Check whether the dot product calculation on
    /// polynomials with length 0 works.
    #[test]
    fn zero_length_works() {
        let poly1 = PolyOverQ::from_str("3  1 2/11 3").unwrap();
        let poly2 = PolyOverQ::from_str("0").unwrap();

        let cmp = Q::ZERO;
        let dot_prod = poly1.dot_product(&poly2).unwrap();

        assert_eq!(dot_prod, cmp);
    }
}
