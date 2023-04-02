// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to approximate the exponential function using a [`PolyOverQ`] polynomial.

use super::PolyOverQ;
use flint_sys::fmpq_poly::fmpq_poly_exp_series;
use std::str::FromStr;

impl PolyOverQ {
    /// Creates the Taylor approximation as a polynomial with the provided length.
    ///
    /// Parameters:
    /// - `length`: the length of the taylor series approximation of the exponential function
    ///
    /// Returns the Taylor approximation of the exponential function.
    ///
    /// # Example
    /// ```compile_fail
    /// use math::rational::PolyOverQ;
    ///
    /// // sum_{k=0}^{length-1} x^k/k!
    /// let taylor_approximation_exponential_function = PolyOverQ::exp_function_taylor(1000);
    /// ```
    pub(crate) fn exp_function_taylor(length: u32) -> Self {
        let mut out = Self::default();
        let x_poly = PolyOverQ::from_str("2  0 1").unwrap();

        unsafe { fmpq_poly_exp_series(&mut out.poly, &x_poly.poly, length.into()) };
        out
    }
}

#[cfg(test)]
mod test_exp_series {
    use crate::{
        rational::{PolyOverQ, Q},
        traits::{Evaluate, GetCoefficient},
    };
    use flint_sys::fmpq::fmpq_get_d;
    use std::str::FromStr;

    #[test]
    fn coefficient_set_correctly() {
        let length = 1000;
        let poly = PolyOverQ::exp_function_taylor(length);
        let mut fac_value = Q::from_str("1").unwrap();
        assert_eq!(fac_value, poly.get_coeff(0).unwrap());
        for i in 1..length {
            fac_value = fac_value * Q::from_str(&format!("1/{}", i)).unwrap();
            assert_eq!(fac_value, poly.get_coeff(i).unwrap())
        }
    }

    #[test]
    fn correct_len() {
        let length = 170;
        let poly = PolyOverQ::exp_function_taylor(length);
        assert_eq!(length as i64, poly.poly.length);

        println!("{}", PolyOverQ::exp_function_taylor(1000).evaluate(1));

        println!("{}", unsafe {
            fmpq_get_d(&PolyOverQ::exp_function_taylor(1000).evaluate(1_i32).value)
        })
    }
}
