// Copyright 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute several norms
//! defined on polynomials.

use crate::{
    rational::{PolyOverQ, Q},
    traits::{GetCoefficient, Pow},
};
use std::cmp::max;

impl PolyOverQ {
    /// Returns the squared Euclidean norm or squared 2-norm of the given polynomial.
    /// The squared Euclidean norm for a polynomial is obtained by treating the coefficients
    /// of the polynomial as a vector and then applying the standard squared Euclidean norm.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{PolyOverQ, Q};
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverQ::from_str("3  1/7 2/7 3/7").unwrap();
    ///
    /// let sqrd_2_norm = poly.norm_eucl_sqrd();
    ///
    /// // (1*1 + 2*2 + 3*3)/49 = 14/49 = 2/7
    /// assert_eq!(Q::from((2, 7)), sqrd_2_norm);
    /// ```
    pub fn norm_eucl_sqrd(&self) -> Q {
        let mut res = Q::ZERO;

        for i in 0..=self.get_degree() {
            let coeff = unsafe { self.get_coeff_unchecked(i) };
            res += coeff.pow(2).unwrap();
        }
        res
    }
}

impl PolyOverQ {
    /// Returns the infinity norm or the maximal absolute value of a
    /// coefficient of the given polynomial.
    /// The infinity norm for a polynomial is obtained by treating the coefficients
    /// of the polynomial as a vector and then applying the standard infinity norm.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::{PolyOverQ, Q};
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverQ::from_str("3  1/7 2/7 3/7").unwrap();
    ///
    /// let infty_norm = poly.norm_infty();
    ///
    /// // max coefficient is 3/7
    /// assert_eq!(Q::from((3, 7)), infty_norm);
    /// ```
    pub fn norm_infty(&self) -> Q {
        let mut res = Q::ZERO;
        for i in 0..=self.get_degree() {
            res = max(res, unsafe { self.get_coeff_unchecked(i).abs() });
        }
        res
    }

    /// Outputs the hamming weight of `self`, i.e. it returns the number of
    /// non-zero coefficients in the polynomial.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverQ::from_str("5  1 2/3 3/2 0 4").unwrap();
    ///
    /// let hamming_weight = poly.hamming_weight();
    ///
    /// assert_eq!(4, hamming_weight);
    /// ```
    pub fn hamming_weight(&self) -> i64 {
        let mut hamming_weight = 0;
        for i in 0..=self.get_degree() {
            let coeff = unsafe { self.get_coeff_unchecked(i) };
            if !coeff.is_zero() {
                hamming_weight += 1;
            }
        }
        hamming_weight
    }
}

#[cfg(test)]
mod test_norm_eucl_sqrd {
    use super::{PolyOverQ, Q};
    use std::str::FromStr;

    /// Check whether the squared euclidean norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_small_coefficient() {
        let poly_1 = PolyOverQ::default();
        let poly_2 = PolyOverQ::from_str("3  1/7 2/7 3/7").unwrap();
        let poly_3 = PolyOverQ::from_str("3  1/8 2010/19 90/29").unwrap();

        assert_eq!(poly_1.norm_eucl_sqrd(), Q::ZERO);
        assert_eq!(poly_2.norm_eucl_sqrd(), Q::from((2, 7)));
        assert_eq!(
            poly_3.norm_eucl_sqrd(),
            Q::from((1, 64)) + Q::from((2010, 19)) * Q::from((2010, 19)) + Q::from((8100, 841))
        );
    }

    /// Check whether the squared euclidean norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_large_coefficient() {
        let poly_1 = PolyOverQ::from_str(&format!("1  {}", u64::MAX)).unwrap();
        let poly_2 =
            PolyOverQ::from_str(&format!("3  {} {} 1/{}", u64::MAX, i64::MIN, i64::MAX)).unwrap();

        assert_eq!(
            poly_1.norm_eucl_sqrd(),
            Q::from(u64::MAX) * Q::from(u64::MAX)
        );
        assert_eq!(
            poly_2.norm_eucl_sqrd(),
            Q::from(u64::MAX) * Q::from(u64::MAX)
                + Q::from(i64::MIN) * Q::from(i64::MIN)
                + Q::from((1, i64::MAX)) * Q::from((1, i64::MAX))
        );
    }
}

#[cfg(test)]
mod test_norm_infty {
    use super::{PolyOverQ, Q};
    use std::str::FromStr;

    /// Check whether the infinity norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_small_coefficient() {
        let poly_1 = PolyOverQ::default();
        let poly_2 = PolyOverQ::from_str("3  1/7 2/7 3/7").unwrap();
        let poly_3 = PolyOverQ::from_str("3  1/8 2010/19 90/29").unwrap();

        assert_eq!(poly_1.norm_infty(), Q::ZERO);
        assert_eq!(poly_2.norm_infty(), Q::from((3, 7)));
        assert_eq!(poly_3.norm_infty(), Q::from((2010, 19)));
    }

    /// Check whether the infinity norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_large_coefficient() {
        let poly_1 = PolyOverQ::from_str(&format!("1  {}", u64::MAX)).unwrap();
        let poly_2 =
            PolyOverQ::from_str(&format!("3  1/{} {}/7 {}", u64::MAX, i64::MIN, i64::MAX)).unwrap();

        assert_eq!(poly_1.norm_infty(), Q::from(u64::MAX));
        assert_eq!(poly_2.norm_infty(), Q::from(i64::MAX));
    }
}

#[cfg(test)]
mod test_hamming_weight {
    use super::PolyOverQ;
    use std::str::FromStr;

    /// Ensures that the hamming weight is computed correctly.
    #[test]
    fn hamming_weight() {
        let poly0 = PolyOverQ::default();
        let poly1 = PolyOverQ::from_str("6  0 0 2/2 3/2 4 5/7").unwrap();

        let hw0 = poly0.hamming_weight();
        let hw1 = poly1.hamming_weight();

        assert_eq!(0, hw0);
        assert_eq!(4, hw1);
    }
}
