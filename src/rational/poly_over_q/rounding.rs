// Copyright © 2024 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality for rounding instances of [`PolyOverQ`] coefficient-wise.

use super::PolyOverQ;
use crate::{
    error::MathError,
    integer::{PolyOverZ, Z},
    rational::Q,
    traits::{GetCoefficient, SetCoefficient},
};

impl PolyOverQ {
    /// Rounds all coefficients of the given rational polynomial [`PolyOverQ`] down to the next integer
    /// as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let value = PolyOverQ::from_str("2  5/2 1").unwrap();
    /// assert_eq!(PolyOverZ::from_str("2  2 1").unwrap(), value.floor());
    ///
    /// let value = PolyOverQ::from_str("2  -5/2 1").unwrap();
    /// assert_eq!(PolyOverZ::from_str("2  -3 1").unwrap(), value.floor());
    /// ```
    pub fn floor(&self) -> PolyOverZ {
        let mut out = PolyOverZ::from(unsafe { self.get_coeff_unchecked(0).floor() });
        for i in 1..self.get_degree() + 1 {
            let coeff = unsafe { self.get_coeff_unchecked(i).floor() };
            unsafe { out.set_coeff_unchecked(i, coeff) };
        }

        out
    }

    /// Rounds all coefficients of the given rational polynomial [`PolyOverQ`] up to the next integer
    /// as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let value = PolyOverQ::from_str("2  5/2 1").unwrap();
    /// assert_eq!(PolyOverZ::from_str("2  3 1").unwrap(), value.ceil());
    ///
    /// let value = PolyOverQ::from_str("2  -5/2 1").unwrap();
    /// assert_eq!(PolyOverZ::from_str("2  -2 1").unwrap(), value.ceil());
    /// ```
    pub fn ceil(&self) -> PolyOverZ {
        let mut out = PolyOverZ::from(unsafe { self.get_coeff_unchecked(0).ceil() });
        for i in 1..self.get_degree() + 1 {
            let coeff = unsafe { self.get_coeff_unchecked(i).ceil() };
            unsafe { out.set_coeff_unchecked(i, coeff) };
        }

        out
    }

    /// Rounds all coefficients of the given rational polynomial [`PolyOverQ`] to the closest integer
    /// as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let value = PolyOverQ::from_str("2  5/2 1").unwrap();
    /// println!("{}", value.round());
    /// assert_eq!(PolyOverZ::from_str("2  3 1").unwrap(), value.round());
    ///
    /// let value = PolyOverQ::from_str("2  -5/2 1").unwrap();
    /// assert_eq!(PolyOverZ::from_str("2  -2 1").unwrap(), value.round());
    /// ```
    pub fn round(&self) -> PolyOverZ {
        let mut out = PolyOverZ::from(unsafe { self.get_coeff_unchecked(0).round() });

        for i in 1..self.get_degree() + 1 {
            let coeff = unsafe { self.get_coeff_unchecked(i).round() };
            unsafe { out.set_coeff_unchecked(i, coeff) };
        }

        out
    }

    /// Performs the randomized rounding algorithm coefficient-wise
    /// by sampling from a discrete Gaussian over the integers shifted
    /// by `self` with gaussian parameter `r`.
    ///
    /// Parameters:
    /// - `n`: the security parameter; also specifies the range from which is sampled
    /// - `r`: specifies the Gaussian parameter, which is proportional
    ///   to the standard deviation `sigma * sqrt(2 * pi) = r`
    ///
    /// Returns the rounded polynomial as a [`PolyOverZ`] or an error if `n <= 1` or `r <= 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let value = PolyOverQ::from_str("2  5/2 1").unwrap();
    /// let rounded = value.randomized_rounding(3,5).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///   if `n <= 1` or `r <= 0`.
    ///
    /// This function implements randomized rounding according to:
    /// - \[1\] Peikert, C. (2010, August).
    ///   An efficient and parallel Gaussian sampler for lattices.
    ///   In: Annual Cryptology Conference (pp. 80-97).
    ///   <https://link.springer.com/chapter/10.1007/978-3-642-14623-7_5>
    pub fn randomized_rounding(
        &self,
        r: impl Into<Q>,
        n: impl Into<Z>,
    ) -> Result<PolyOverZ, MathError> {
        let r = r.into();
        let n = n.into();
        let mut out =
            PolyOverZ::from(unsafe { self.get_coeff_unchecked(0).randomized_rounding(&r, &n)? });
        for i in 1..self.get_degree() + 1 {
            let coeff = unsafe { self.get_coeff_unchecked(i).randomized_rounding(&r, &n)? };
            unsafe { out.set_coeff_unchecked(i, coeff) };
        }

        Ok(out)
    }
}

#[cfg(test)]
mod test_floor {
    use crate::{integer::PolyOverZ, rational::PolyOverQ};
    use std::str::FromStr;

    // Ensure that positive rationals are rounded correctly
    #[test]
    fn positive() {
        let value = PolyOverQ::from_str(&format!("2  1/{} {}/2", u64::MAX, i64::MAX)).unwrap();
        let cmp = PolyOverZ::from_str(&format!("2  0 {}", (i64::MAX - 1) / 2)).unwrap();

        assert_eq!(cmp, value.floor());
    }

    // Ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let value = PolyOverQ::from_str(&format!("2  -1/{} -{}/2", u64::MAX, i64::MAX)).unwrap();
        let cmp = PolyOverZ::from_str(&format!("2  -1 {}", (-i64::MAX - 1) / 2)).unwrap();

        assert_eq!(cmp, value.floor());
    }
}

#[cfg(test)]
mod test_ceil {
    use crate::{integer::PolyOverZ, rational::PolyOverQ};
    use std::str::FromStr;

    // Ensure that positive rationals are rounded correctly
    #[test]
    fn positive() {
        let value = PolyOverQ::from_str(&format!("2  1/{} {}/2", u64::MAX, i64::MAX)).unwrap();
        let cmp = PolyOverZ::from_str(&format!("2  1 {}", (i64::MAX - 1) / 2 + 1)).unwrap();

        assert_eq!(cmp, value.ceil());
    }

    // Ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let value = PolyOverQ::from_str(&format!("2  -1/{} -{}/2", u64::MAX, i64::MAX)).unwrap();
        let cmp = PolyOverZ::from_str(&format!("2  0 {}", (-i64::MAX - 1) / 2 + 1)).unwrap();

        assert_eq!(cmp, value.ceil());
    }
}

#[cfg(test)]
mod test_round {
    use crate::{integer::PolyOverZ, rational::PolyOverQ};
    use std::str::FromStr;

    // Ensure that positive rationals are rounded correctly
    #[test]
    fn positive() {
        let value = PolyOverQ::from_str(&format!("2  1/{} {}/2", u64::MAX, i64::MAX)).unwrap();
        let cmp = PolyOverZ::from_str(&format!("2  0 {}", (i64::MAX - 1) / 2 + 1)).unwrap();

        assert_eq!(cmp, value.round());
    }

    // Ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let value = PolyOverQ::from_str(&format!("2  -1/{} -{}/2", u64::MAX, i64::MAX)).unwrap();
        let cmp = PolyOverZ::from_str(&format!("2  0 {}", (-i64::MAX - 1) / 2 + 1)).unwrap();

        assert_eq!(cmp, value.round());
    }
}

#[cfg(test)]
mod test_randomized_rounding {
    use crate::rational::PolyOverQ;
    use std::str::FromStr;

    /// Ensure that a `n <= 1` throws an error
    #[test]
    fn small_n() {
        let value = PolyOverQ::from_str("2  5/2 1").unwrap();
        assert!(value.randomized_rounding(3, 1).is_err());
        assert!(value.randomized_rounding(3, -3).is_err());
    }

    /// Ensure that a `r <= 0` throws an error
    #[test]
    fn negative_r() {
        let value = PolyOverQ::from_str("2  5/2 1").unwrap();
        assert!(value.randomized_rounding(0, 5).is_err());
        assert!(value.randomized_rounding(-1, 5).is_err());
    }
}
