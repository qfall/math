// Copyright © 2024 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality to compute several norms
//! defined on polynomials.

use super::ModulusPolynomialRingZq;
use crate::{integer::Z, integer_mod_q::PolyOverZq};

impl ModulusPolynomialRingZq {
    /// Returns the squared Euclidean norm or 2-norm of the given polynomial.
    /// The squared Euclidean norm for a polynomial is obtained by treating the coefficients
    /// of the polynomial as a vector and then applying the standard squared Euclidean norm.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::Z, integer_mod_q::ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 11").unwrap();
    ///
    /// let sqrd_2_norm = poly.norm_eucl_sqrd();
    ///
    /// // 1*1 + 2*2 + 3*3 = 14
    /// assert_eq!(Z::from(14), sqrd_2_norm);
    /// ```
    pub fn norm_eucl_sqrd(&self) -> Z {
        PolyOverZq::from(self).norm_eucl_sqrd()
    }

    /// Returns the infinity norm or the maximal absolute value of a
    /// coefficient of the given polynomial.
    /// The infinity norm for a polynomial is obtained by treating the coefficients
    /// of the polynomial as a vector and then applying the standard infinity norm.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::Z, integer_mod_q::ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("3  1 2 4 mod 7").unwrap();
    ///
    /// let infty_norm = poly.norm_infty();
    ///
    /// // max coefficient is 4 = -3
    /// assert_eq!(Z::from(3), infty_norm);
    /// ```
    pub fn norm_infty(&self) -> Z {
        PolyOverZq::from(self).norm_infty()
    }
}

#[cfg(test)]
mod test_norms {
    use super::Z;
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// Check whether the norms can be computed for [`ModulusPolynomialRingZq`].
    /// Correctness is already checked for [`PolyOverZq`](crate::integer_mod_q::PolyOverZq).
    #[test]
    fn availability() {
        let poly = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 11").unwrap();

        let norm_es = poly.norm_eucl_sqrd();
        let norm_i = poly.norm_infty();

        assert_eq!(Z::from(14), norm_es);
        assert_eq!(Z::from(3), norm_i);
    }
}
