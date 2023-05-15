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
    integer::{PolyOverZ, Z},
    traits::{GetCoefficient, Pow},
};

impl PolyOverZ {
    /// Returns the squared Euclidean norm or 2-norm of the given polynomial.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{PolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("3  1 2 3").unwrap();
    ///
    /// let sqrd_2_norm = poly.norm_eucl_sqrd();
    ///
    /// // 1*1 + 2*2 + 3*3 = 14
    /// assert_eq!(Z::from(14), sqrd_2_norm);
    /// ```
    pub fn norm_eucl_sqrd(&self) -> Z {
        let mut res = Z::ZERO;

        for i in 0..=self.get_degree() {
            let coeff = self.get_coeff(i).unwrap();
            res = res + coeff.pow(2).unwrap();
        }
        res
    }
}

impl PolyOverZ {
    /// Returns the infinity norm or the maximal absolute value of a
    /// coefficient of the given polynomial.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{PolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("3  1 2 3").unwrap();
    ///
    /// let infty_norm = poly.norm_infty();
    ///
    /// // max coefficient is 3
    /// assert_eq!(Z::from(3), infty_norm);
    /// ```
    pub fn norm_infty(&self) -> Z {
        let mut res = Z::ZERO;
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
    use super::{PolyOverZ, Z};
    use std::str::FromStr;

    /// Check whether the squared euclidean norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_small_coefficient() {
        let poly1 = PolyOverZ::from_str("0").unwrap();
        let poly2 = PolyOverZ::from_str("3  1 2 3").unwrap();
        let poly3 = PolyOverZ::from_str("3  1 20 90").unwrap();

        assert_eq!(poly1.norm_eucl_sqrd(), Z::ZERO);
        assert_eq!(poly2.norm_eucl_sqrd(), Z::from(14));
        assert_eq!(poly3.norm_eucl_sqrd(), Z::from(8501));
    }

    /// Check whether the squared euclidean norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_large_coefficient() {
        let poly1 = PolyOverZ::from_str(&format!("1  {}", u64::MAX)).unwrap();
        let poly2 =
            PolyOverZ::from_str(&format!("3  {} {} {}", u64::MAX, i64::MIN, i64::MAX)).unwrap();

        assert_eq!(
            poly1.norm_eucl_sqrd(),
            Z::from(u64::MAX) * Z::from(u64::MAX)
        );
        assert_eq!(
            poly2.norm_eucl_sqrd(),
            Z::from(u64::MAX) * Z::from(u64::MAX)
                + Z::from(i64::MAX) * Z::from(i64::MAX)
                + Z::from(i64::MIN) * Z::from(i64::MIN)
        );
    }
}

#[cfg(test)]
mod test_norm_infty {
    use super::{PolyOverZ, Z};
    use std::str::FromStr;

    /// Check whether the infinity norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_small_coefficient() {
        let poly1 = PolyOverZ::from_str("0").unwrap();
        let poly2 = PolyOverZ::from_str("3  1 2 3").unwrap();
        let poly3 = PolyOverZ::from_str("3  1 2010 90").unwrap();

        assert_eq!(poly1.norm_infty(), Z::ZERO);
        assert_eq!(poly2.norm_infty(), Z::from(3));
        assert_eq!(poly3.norm_infty(), Z::from(2010));
    }

    /// Check whether the infinity norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_large_coefficient() {
        let poly1 = PolyOverZ::from_str(&format!("1  {}", u64::MAX)).unwrap();
        let poly2 =
            PolyOverZ::from_str(&format!("3  {} {} {}", u64::MAX, i64::MIN, i64::MAX)).unwrap();

        assert_eq!(poly1.norm_infty(), Z::from(u64::MAX));
        assert_eq!(poly2.norm_infty(), Z::from(u64::MAX));
    }
}
