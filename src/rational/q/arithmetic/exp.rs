// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to call the exponential function on a [`Q`].

use crate::{
    rational::{PolyOverQ, Q},
    traits::Evaluate,
};

// Initialize the taylor expansion just once and not every time we call exp.
lazy_static::lazy_static! {
    /// The taylor expansion of the exponential function used when [`f64.exp`]
    /// can no longer be used.
    pub static ref EXP_TAYLOR_POLY: PolyOverQ = PolyOverQ::exp_function_taylor(100u32);
}

impl Q {
    /// Computes `e^self`. This is done by first converting the value to a [`f64`],
    /// evaluating the exponential function and converting the float back to [`Q`].
    /// As a result, the precision is limited to the precision of [`f64`].
    /// More concrete, values smaller than `e^-745` are rounded to `0`.
    /// For exponents above 709, a taylor series with 100 coefficients is used.
    ///
    /// Returns e^self.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let evaluation = Q::from((17, 3)).exp();
    /// let e = Q::ONE.exp();
    /// ```
    pub fn exp(&self) -> Self {
        if self < &Q::from(709) {
            Q::from(f64::from(self).exp())
        } else {
            EXP_TAYLOR_POLY.evaluate(self)
        }
    }

    /// Computes e^self using taylor series approximation of the exponential function.
    ///
    /// Parameters:
    /// - `length_taylor_polynomial`: the length of the taylor series
    /// approximation of the exponential function
    ///
    /// Returns e^self.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// // sum_{k=0}^999 (17/3)^k/k!
    /// let evaluation = Q::from((17, 3)).exp_taylor(1000_u32);
    /// ```
    pub fn exp_taylor(&self, length_taylor_polynomial: impl Into<u32>) -> Self {
        let exp_taylor_series = PolyOverQ::exp_function_taylor(length_taylor_polynomial);
        exp_taylor_series.evaluate(self)
    }
}

#[cfg(test)]
mod test_exp {
    use super::*;

    /// Ensure that `e^0 = 1`.
    #[test]
    fn zero() {
        assert_eq!(Q::ONE, Q::ZERO.exp())
    }

    /// Ensure that `e^1 = e`.
    #[test]
    fn one() {
        let e = Q::ONE.exp();

        assert_eq!(e, Q::from(1.0f64.exp()))
    }

    /// Show the exp behavior for large negative inputs zero e^-745, but values smaller than e^-745 do.
    #[test]
    fn large_negative_exponent() {
        let small = Q::from(-745).exp();
        let small_2 = Q::from((-7451, 10)).exp();
        let zero = Q::from((-7452, 10)).exp();

        println!("{}", &small);

        assert_ne!(small, Q::ZERO);
        assert_eq!(small, small_2);
        assert_eq!(zero, Q::ZERO);
    }

    /// Test a large input very close to where exp stops using f64 for calculation.
    /// It should not saturate f64 into infinity.
    #[test]
    fn large_float_calc() {
        let result = (Q::from(709) - Q::from((1, u64::MAX))).exp();

        assert_ne!(f64::from(&result), f64::INFINITY);
    }

    /// Ensure that the exponential function for large values outputs different results.
    #[test]
    fn large_exponent() {
        let large_1 = Q::from(u64::MAX).exp();
        let large_2 = Q::from(u64::MAX - 1).exp();

        assert!(large_1 > large_2);
    }
}

#[cfg(test)]
mod test_exp_taylor {
    use crate::rational::Q;

    /// Ensure that `0` is returned if the length `0` is provided
    #[test]
    fn zero_length() {
        let q = Q::from((17, 3));

        assert_eq!(Q::default(), q.exp_taylor(0_u32));
    }

    /// Test correct evaluation for some explicit values
    #[test]
    fn ten_length_value() {
        assert_eq!(Q::from((98641, 36288)), Q::ONE.exp_taylor(10_u32));
        assert_eq!(
            Q::from((2492063827u64, 1785641760)),
            Q::from((1, 3)).exp_taylor(10_u32)
        );
        assert_eq!(
            Q::from((5729869, 11160261)),
            Q::from((-2, 3)).exp_taylor(10_u32)
        );
    }
}
