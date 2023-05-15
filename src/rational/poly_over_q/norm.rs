// Copyright © 2023 Phil Milewski
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

impl PolyOverQ {
    /// Returns the squared Euclidean norm or 2-norm of the given polynomial.
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
    /// assert_eq!(Q::from_str("2/7").unwrap(), sqrd_2_norm);
    /// ```
    pub fn norm_eucl_sqrd(&self) -> Q {
        let mut res = Q::ZERO;

        for i in 0..=self.get_degree() {
            let coeff = self.get_coeff(i).unwrap();
            res = res + coeff.pow(2).unwrap();
        }
        res
    }
}

impl PolyOverQ {
    /// Returns the infinity norm or the maximal absolute value of a
    /// coefficient of the given polynomial.
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
    /// assert_eq!(Q::from_str("3/7").unwrap(), infty_norm);
    /// ```
    pub fn norm_infty(&self) -> Q {
        let mut res = Q::ZERO;
        for i in 0..=self.get_degree() {
            // todo: once ord is on dev use:
            // res = max(res, self.get_coeff(i).unwrap().abs());
            // AND todo: use std::cmp::max;
            if res < self.get_coeff(i).unwrap().abs() {
                res = self.get_coeff(i).unwrap().abs();
            }
        }
        res
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
        let poly1 = PolyOverQ::from_str("0").unwrap();
        let poly2 = PolyOverQ::from_str("3  1/7 2/7 3/7").unwrap();
        let poly3 = PolyOverQ::from_str("3  1/8 2010/19 90/29").unwrap();

        assert_eq!(poly1.norm_eucl_sqrd(), Q::ZERO);
        assert_eq!(poly2.norm_eucl_sqrd(), Q::from_str("2/7").unwrap());
        assert_eq!(
            poly3.norm_eucl_sqrd(),
            Q::from_str("1/64").unwrap()
                + Q::from_str("2010/19").unwrap() * Q::from_str("2010/19").unwrap()
                + Q::from_str("8100/841").unwrap()
        );
    }

    /// Check whether the squared euclidean norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_large_coefficient() {
        let poly1 = PolyOverQ::from_str(&format!("1  {}", u64::MAX)).unwrap();
        let poly2 =
            PolyOverQ::from_str(&format!("3  {} {} 1/{}", u64::MAX, i64::MIN, i64::MAX)).unwrap();

        assert_eq!(
            poly1.norm_eucl_sqrd(),
            Q::from(u64::MAX) * Q::from(u64::MAX)
        );
        assert_eq!(
            poly2.norm_eucl_sqrd(),
            Q::from(u64::MAX) * Q::from(u64::MAX)
                + Q::from(i64::MIN) * Q::from(i64::MIN)
                + Q::from_str(&format!("1/{}", i64::MAX)).unwrap()
                    * Q::from_str(&format!("1/{}", i64::MAX)).unwrap()
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
        let poly1 = PolyOverQ::from_str("0").unwrap();
        let poly2 = PolyOverQ::from_str("3  1/7 2/7 3/7").unwrap();
        let poly3 = PolyOverQ::from_str("3  1/8 2010/19 90/29").unwrap();

        assert_eq!(poly1.norm_infty(), Q::ZERO);
        assert_eq!(poly2.norm_infty(), Q::from_str("3/7").unwrap());
        assert_eq!(poly3.norm_infty(), Q::from_str("2010/19").unwrap());
    }

    /// Check whether the infinity norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_large_coefficient() {
        let poly1 = PolyOverQ::from_str(&format!("1  {}", u64::MAX)).unwrap();
        let poly2 =
            PolyOverQ::from_str(&format!("3  1/{} {}/7 {}", u64::MAX, i64::MIN, i64::MAX)).unwrap();

        assert_eq!(poly1.norm_infty(), Q::from(u64::MAX));
        assert_eq!(poly2.norm_infty(), Q::from(i64::MAX));
    }
}