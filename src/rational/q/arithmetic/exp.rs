// Copyright © 2023 Marvin Beckmann and Sven Moog
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
use flint_sys::fmpq::fmpq_mul_2exp;

impl Q {
    /// Computes `e^self`.
    ///
    /// For exponents below 709, the value is converted to [`f64`] for the calculation.
    /// As a result, the precision is limited to the precision of [`f64`].
    /// This means that values smaller than `e^-745` are rounded to `0`.
    /// The [`f64`] calculation is relatively fast.
    /// For exponents above 709, a different algorithm is used.
    /// Its error bound is not calculated at this point, but probably below 10%.
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
    ///
    /// # Panics ...
    /// - if the exponent is too large (exponent*log_2(e)) >= 2^36.
    ///   This would use up more than 64 GB of RAM.
    pub fn exp(&self) -> Self {
        // f64::exp starts mapping to f64::INFINITY between 709.7 and 709.8.
        if self <= &Q::from(709) {
            Q::from(f64::from(self).exp())
        } else {
            // e^x = 2^(log_2(e^x)) = 2^(x*log_2(e))
            let log_2_of_e = Q::from(f64::log2(1f64.exp()));

            let base_2_exponent = self * log_2_of_e;
            let base_2_int_exponent: i64 = (&base_2_exponent.floor()).try_into().unwrap();
            let base_2_remainder_exponent = base_2_exponent - base_2_int_exponent;

            // Divide x*log_2(e) into an integer part i and the remainder r.
            // 2^(i+r) = 2^i * 2^r
            // 2^r ~= r+1 for r in [0,1]
            let mut out: Q = base_2_remainder_exponent + 1;
            unsafe { fmpq_mul_2exp(&mut out.value, &out.value, base_2_int_exponent as u64) }
            out
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
    use flint_sys::fmpz::fmpz_get_d_2exp;

    /// Ensure that `e^0 = 1`.
    #[test]
    fn zero() {
        assert_eq!(Q::ONE, Q::ZERO.exp())
    }

    /// Ensure that `e^1 = e`.
    #[test]
    fn one() {
        let e = Q::ONE.exp();

        assert_eq!(e, Q::from(1f64.exp()))
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
    /// Additionally, the the greater relationship should be correct when transitioning
    /// to the other algorithm.
    #[test]
    fn algorithm_transition_correct() {
        let result_less_than_709 = (Q::from(709) - Q::from((1, u64::MAX))).exp();

        let result_709 = Q::from(709).exp();

        assert_ne!(f64::from(&result_less_than_709), f64::INFINITY);
        assert!(result_less_than_709 < result_709);
    }

    /// Ensure that e^300 is the same when calculated with [`Q`] or [`f64`].
    #[test]
    fn medium_exponent() {
        let a = Q::from(300).exp();

        assert_eq!(a, Q::from(300f64.exp()))
    }

    /// Ensure that the exponential function for large values outputs different results.
    #[test]
    fn large_exponent() {
        let large_1 = Q::from(u32::MAX).exp();
        let large_2 = Q::from(u32::MAX - 1).exp();

        assert!(large_1 > large_2);
    }

    /// Ensure that the exponential function for [`u32::MAX`] has an
    /// error of at most 6%.
    #[test]
    fn large_exponent_error_bound() {
        let large = Q::from(u32::MAX).exp();

        // large = e^u32::MAX ~= 1.490856880... × 10^1865280596
        // <https://www.wolframalpha.com/input?i=1%2Be%5E4294967295>

        // Calculations with these large numbers takes a lot of computing time.
        // Therefore, we norm them with 2^-6196328016 for further calculations.
        // 1.490856880 × 10^1865280596 * 2^-6196328016 = 2.42298514666...
        // 10^1865280596 = 2^6196328016.7006445
        // value_prime = large * 2^-6196328016
        let mut exponent = 0;
        let mut value_prime = unsafe { fmpz_get_d_2exp(&mut exponent, &large.value.num) };
        value_prime = value_prime * 2f64.powi((exponent - 6196328016) as i32);

        println!("{}, {}", value_prime, exponent);

        // Allow 6% Error (Error Bound chosen based on calculation result)
        let upper_bound = 1.06 * 2.42298514666;
        let lower_bound = 0.94 * 2.42298514666;
        // let upper_bound =
        assert!(lower_bound < value_prime);
        assert!(upper_bound > value_prime);
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
