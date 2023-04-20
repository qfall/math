// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to call the exponential function on a [`Q`].

use super::Q;
use crate::{rational::PolyOverQ, traits::Evaluate};

impl Q {
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
    /// let evaluation = Q::from_str("17/3").unwrap().exp_taylor(1000_u32);
    /// ```
    pub fn exp_taylor(&self, length_taylor_polynomial: impl Into<u32>) -> Self {
        let exp_taylor_series = PolyOverQ::exp_function_taylor(length_taylor_polynomial);
        exp_taylor_series.evaluate(self)
    }
}

#[cfg(test)]
mod test_exp {
    use crate::rational::Q;
    use std::str::FromStr;

    /// ensure that `0` is returned if the length `0` is provided
    #[test]
    fn zero_length() {
        let q = Q::from_str("17/3").unwrap();

        assert_eq!(Q::default(), q.exp_taylor(0_u32));
    }

    /// test correct evaluation for some explicit values
    #[test]
    fn ten_length_value() {
        assert_eq!(
            Q::from_str("98641/36288").unwrap(),
            Q::from_str("1").unwrap().exp_taylor(10_u32)
        );
        assert_eq!(
            Q::from_str("2492063827/1785641760").unwrap(),
            Q::from_str("1/3").unwrap().exp_taylor(10_u32)
        );
        assert_eq!(
            Q::from_str("5729869/11160261").unwrap(),
            Q::from_str("-2/3").unwrap().exp_taylor(10_u32)
        );
    }
}
