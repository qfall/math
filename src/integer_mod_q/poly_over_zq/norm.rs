// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute several norms
//! defined on polynomials.

use crate::{integer::Z, integer_mod_q::PolyOverZq, traits::GetCoefficient};

impl PolyOverZq {
    /// Returns the squared Euclidean norm or 2-norm of the given polynomial.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::Z, integer_mod_q::PolyOverZq};
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("3  1 2 3 mod 11").unwrap();
    ///
    /// let sqrd_2_norm = poly.norm_eucl_sqrd();
    ///
    /// // 1*1 + 2*2 + 3*3 = 14
    /// assert_eq!(Z::from(14), sqrd_2_norm);
    /// ```
    pub fn norm_eucl_sqrd(&self) -> Z {
        let mut res = Z::ZERO;
        for i in 0..=self.get_degree() {
            let mut coeff: Z = self.get_coeff(i).unwrap();
            let minus_coeff = Z::from(&self.modulus) - &coeff;
            if minus_coeff < coeff {
                //todo: use min once on dev
                coeff = minus_coeff;
            }
            res = res + &coeff * &coeff;
        }
        res
    }
}

impl PolyOverZq {
    /// Returns the infinity norm or the maximal absolute value of a
    /// coefficient of the given polynomial.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::Z, integer_mod_q::PolyOverZq};
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("3  1 2 4 mod 7").unwrap();
    ///
    /// let infty_norm = poly.norm_infty();
    ///
    /// // max coefficient is 4 = -3
    /// assert_eq!(Z::from(3), infty_norm);
    /// ```
    pub fn norm_infty(&self) -> Z {
        let mut res = Z::ZERO;
        for i in 0..=self.get_degree() {
            let mut coeff: Z = self.get_coeff(i).unwrap();
            let minus_coeff = Z::from(&self.modulus) - &coeff;
            if minus_coeff < coeff {
                //todo: use min once on dev
                coeff = minus_coeff;
            }

            // todo: once ord is on dev use:
            // res = max(res, coeff);
            // AND todo: use std::cmp::max;
            if res < coeff {
                res = coeff;
            }
        }
        res
    }
}

#[cfg(test)]
mod test_norm_eucl_sqrd {
    use super::{PolyOverZq, Z};
    use std::str::FromStr;

    /// Check whether the squared euclidean norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_small_coefficient() {
        let poly1 = PolyOverZq::from_str("0 mod 11").unwrap();
        let poly2 = PolyOverZq::from_str("3  1 2 3 mod 11").unwrap();
        let poly3 = PolyOverZq::from_str("3  1 20 194 mod 195").unwrap();

        assert_eq!(poly1.norm_eucl_sqrd(), Z::ZERO);
        assert_eq!(poly2.norm_eucl_sqrd(), Z::from(14));
        assert_eq!(poly3.norm_eucl_sqrd(), Z::from(402));
    }

    /// Check whether the squared euclidean norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_large_coefficient() {
        let poly1 = PolyOverZq::from_str(&format!("1  {} mod {}", u64::MAX, u128::MAX)).unwrap();
        let poly2 = PolyOverZq::from_str(&format!(
            "3  {} {} {} mod {}",
            u64::MAX,
            i64::MIN,
            i64::MAX,
            u64::MAX - 58
        ))
        .unwrap();

        assert_eq!(
            poly1.norm_eucl_sqrd(),
            Z::from(u64::MAX) * Z::from(u64::MAX)
        );
        assert_eq!(
            poly2.norm_eucl_sqrd(),
            Z::from(58) * Z::from(58)
                + Z::from((u64::MAX - 1) / 2 - 57) * Z::from((u64::MAX - 1) / 2 - 57)
                + Z::from((u64::MAX - 1) / 2 - 58) * Z::from((u64::MAX - 1) / 2 - 58)
        );
    }
}

#[cfg(test)]
mod test_norm_infty {
    use super::{PolyOverZq, Z};
    use std::str::FromStr;

    /// Check whether the infinity norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_small_coefficient() {
        let poly1 = PolyOverZq::from_str("0 mod 3").unwrap();
        let poly2 = PolyOverZq::from_str("3  1 2 3 mod 5").unwrap();
        let poly3 = PolyOverZq::from_str("3  1 2010 90 mod 100").unwrap();

        assert_eq!(poly1.norm_infty(), Z::ZERO);
        assert_eq!(poly2.norm_infty(), Z::from(2));
        assert_eq!(poly3.norm_infty(), Z::from(10));
    }

    /// Check whether the infinity norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_large_coefficient() {
        let poly1 = PolyOverZq::from_str(&format!("1  {} mod {}", u64::MAX, u128::MAX)).unwrap();
        let poly2 = PolyOverZq::from_str(&format!(
            "3  {} {} {} mod {}",
            u64::MAX,
            i64::MIN,
            i64::MAX,
            u64::MAX - 58
        ))
        .unwrap();

        assert_eq!(poly1.norm_infty(), Z::from(u64::MAX));
        assert_eq!(poly2.norm_infty(), Z::from((u64::MAX - 1) / 2 - 57));
    }
}
