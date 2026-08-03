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
    integer::Z,
    integer_mod_q::{PolyOverZq, Zq, fmpz_mod_helpers::length},
    rational::Q,
    traits::{GetCoefficient, Pow},
};
use std::cmp::max;

impl PolyOverZq {
    /// Returns the squared Euclidean norm or squared 2-norm of the given polynomial.
    /// The squared Euclidean norm for a polynomial is obtained by treating the coefficients
    /// of the polynomial as a vector and then applying the standard squared Euclidean norm.
    ///
    /// Each length of an entry in this vector is defined as the shortest distance
    /// to the next zero representative modulo q.
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
            let coeff: Z = unsafe { self.get_coeff_unchecked(i) };
            res += length(&coeff.value, &self.modulus.get_fmpz_mod_ctx_struct().n[0])
                .pow(2)
                .unwrap();
        }
        res
    }

    /// Returns the Euclidean norm or 2-norm of the given polynomial.
    /// The Euclidean norm for a polynomial is obtained by treating the coefficients
    /// of the polynomial as a vector and then applying the standard Euclidean norm.
    ///
    /// Each length of an entry in this vector is defined as the shortest distance
    /// to the next zero representative modulo q.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{rational::Q, integer_mod_q::PolyOverZq};
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("1  3 mod 11").unwrap();
    ///
    /// let norm = poly.norm_eucl();
    ///
    /// // sqrt(3^2) = 3
    /// assert_eq!(Q::from(3), norm);
    /// ```
    pub fn norm_eucl(&self) -> Q {
        self.norm_eucl_sqrd().sqrt()
    }

    /// Returns the infinity norm or the maximal absolute value of a
    /// coefficient of the given polynomial.
    /// The infinity norm for a polynomial is obtained by treating the coefficients
    /// of the polynomial as a vector and then applying the standard infinity norm.
    ///
    /// Each length of an entry in this vector is defined as the shortest distance
    /// to the next zero representative modulo q.
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
            let coeff: Z = unsafe { self.get_coeff_unchecked(i) };
            let len = length(&coeff.value, &self.modulus.get_fmpz_mod_ctx_struct().n[0]);
            res = max(res, len);
        }
        res
    }

    /// Outputs the hamming weight of `self`, i.e. it returns the number of
    /// non-zero coefficients in the polynomial.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("5  1 2 3 0 5 mod 5").unwrap();
    ///
    /// let hamming_weight = poly.hamming_weight();
    ///
    /// assert_eq!(3, hamming_weight);
    /// ```
    pub fn hamming_weight(&self) -> i64 {
        let mut hamming_weight = 0;
        for i in 0..=self.get_degree() {
            let coeff: Zq = unsafe { self.get_coeff_unchecked(i) };
            if !coeff.is_zero() {
                hamming_weight += 1;
            }
        }
        hamming_weight
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
        let poly_1 = PolyOverZq::from_str("0 mod 11").unwrap();
        let poly_2 = PolyOverZq::from_str("3  1 2 3 mod 11").unwrap();
        let poly_3 = PolyOverZq::from_str("3  1 20 194 mod 195").unwrap();

        assert_eq!(poly_1.norm_eucl_sqrd(), Z::ZERO);
        assert_eq!(poly_2.norm_eucl_sqrd(), Z::from(14));
        assert_eq!(poly_3.norm_eucl_sqrd(), Z::from(402));
    }

    /// Check whether the squared euclidean norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_large_coefficient() {
        let poly_1 = PolyOverZq::from_str(&format!("1  {} mod {}", u64::MAX, u128::MAX)).unwrap();
        let poly_2 = PolyOverZq::from_str(&format!(
            "3  {} {} {} mod {}",
            u64::MAX,
            i64::MIN,
            i64::MAX,
            u64::MAX - 58
        ))
        .unwrap();

        assert_eq!(
            poly_1.norm_eucl_sqrd(),
            Z::from(u64::MAX) * Z::from(u64::MAX)
        );
        assert_eq!(
            poly_2.norm_eucl_sqrd(),
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
        let poly_1 = PolyOverZq::from_str("0 mod 3").unwrap();
        let poly_2 = PolyOverZq::from_str("3  1 2 3 mod 5").unwrap();
        let poly_3 = PolyOverZq::from_str("3  1 2010 90 mod 100").unwrap();

        assert_eq!(poly_1.norm_infty(), Z::ZERO);
        assert_eq!(poly_2.norm_infty(), Z::from(2));
        assert_eq!(poly_3.norm_infty(), Z::from(10));
    }

    /// Check whether the infinity norm for polynomials
    /// with small coefficients is calculated correctly
    #[test]
    fn poly_large_coefficient() {
        let poly_1 = PolyOverZq::from_str(&format!("1  {} mod {}", u64::MAX, u128::MAX)).unwrap();
        let poly_2 = PolyOverZq::from_str(&format!(
            "3  {} {} {} mod {}",
            u64::MAX,
            i64::MIN,
            i64::MAX,
            u64::MAX - 58
        ))
        .unwrap();

        assert_eq!(poly_1.norm_infty(), Z::from(u64::MAX));
        assert_eq!(poly_2.norm_infty(), Z::from((u64::MAX - 1) / 2 - 57));
    }
}

#[cfg(test)]
mod test_hamming_weight {
    use super::PolyOverZq;
    use std::str::FromStr;

    /// Ensures that the hamming weight is computed correctly.
    #[test]
    fn hamming_weight() {
        let poly0 = PolyOverZq::from((0, 3));
        let poly1 = PolyOverZq::from_str("6  0 0 2 3 4 5 mod 3").unwrap();

        let hw0 = poly0.hamming_weight();
        let hw1 = poly1.hamming_weight();

        assert_eq!(0, hw0);
        assert_eq!(3, hw1);
    }
}
