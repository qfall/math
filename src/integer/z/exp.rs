// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to call the exponential function on a [`Z`] integer.

use super::Z;
use crate::{
    rational::{PolyOverQ, Q},
    traits::Evaluate,
};

impl Z {
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
    /// use qfall_math::integer::Z;
    ///
    /// // sum_{k=0}^999 17^k/k!
    /// let evaluation = Z::from(17).exp_taylor(1000_u32);
    /// ```
    pub fn exp_taylor(&self, length_taylor_polynomial: impl Into<u32>) -> Q {
        let exp_taylor_series = PolyOverQ::exp_function_taylor(length_taylor_polynomial);
        exp_taylor_series.evaluate(self)
    }
}

#[cfg(test)]
mod test_exp {
    use crate::{integer::Z, rational::Q};
    use std::str::FromStr;

    /// ensure that `0` is returned if the length `0` is provided
    #[test]
    fn zero_length() {
        let z = Z::from(17);

        assert_eq!(Q::default(), z.exp_taylor(0_u32));
    }

    /// test correct evaluation for some explicit values
    #[test]
    fn ten_length_value() {
        assert_eq!(
            Q::from_str("98641/36288").unwrap(),
            Z::ONE.exp_taylor(10_u32)
        );
        assert_eq!(
            Q::from_str("22471/1120").unwrap(),
            Z::from(3).exp_taylor(10_u32)
        );
        assert_eq!(
            Q::from_str("83/2240").unwrap(),
            Z::from(-3).exp_taylor(10_u32)
        );
    }
}
