// Copyright © 2024 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality for rounding instances of [`MatQ`] entrywise.

use super::MatQ;
use crate::{
    error::MathError,
    integer::{MatZ, Z},
    rational::Q,
    traits::{GetEntry, GetNumColumns, GetNumRows, SetEntry},
};

impl MatQ {
    /// Rounds all entries of the given rational matrix [`MatQ`] down to the next integer
    /// as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let value = MatQ::from_str("[[5/2, 1]]").unwrap();
    /// assert_eq!(MatZ::from_str("[[2, 1]]").unwrap(), value.floor());
    ///
    /// let value = MatQ::from_str("[[-5/2, 1]]").unwrap();
    /// assert_eq!(MatZ::from_str("[[-3, 1]]").unwrap(), value.floor());
    /// ```
    pub fn floor(&self) -> MatZ {
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        for i in 0..out.get_num_rows() {
            for j in 0..out.get_num_columns() {
                let entry = self.get_entry(i, j).unwrap().floor();
                out.set_entry(i, j, entry).unwrap();
            }
        }
        out
    }

    /// Rounds all entries of the given rational matrix [`MatQ`] up to the next integer
    /// as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let value = MatQ::from_str("[[5/2, 1]]").unwrap();
    /// assert_eq!(MatZ::from_str("[[3, 1]]").unwrap(), value.ceil());
    ///
    /// let value = MatQ::from_str("[[-5/2, 1]]").unwrap();
    /// assert_eq!(MatZ::from_str("[[-2, 1]]").unwrap(), value.ceil());
    /// ```
    pub fn ceil(&self) -> MatZ {
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        for i in 0..out.get_num_rows() {
            for j in 0..out.get_num_columns() {
                let entry = self.get_entry(i, j).unwrap().ceil();
                out.set_entry(i, j, entry).unwrap();
            }
        }
        out
    }

    /// Rounds all entries of the given rational matrix [`MatQ`] to the closest integer
    /// as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let value = MatQ::from_str("[[5/2, 1]]").unwrap();
    /// assert_eq!(MatZ::from_str("[[3, 1]]").unwrap(), value.round());
    ///
    /// let value = MatQ::from_str("[[-5/2, 1]]").unwrap();
    /// assert_eq!(MatZ::from_str("[[-2, 1]]").unwrap(), value.round());
    /// ```
    pub fn round(&self) -> MatZ {
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        for i in 0..out.get_num_rows() {
            for j in 0..out.get_num_columns() {
                let entry = self.get_entry(i, j).unwrap().round();
                out.set_entry(i, j, entry).unwrap();
            }
        }
        out
    }

    /// Performs the randomized rounding algorithm entrywise
    /// by sampling from a discrete Gaussian over the integers shifted
    /// by `self` with gaussian parameter `r`.
    ///
    /// Parameters:
    /// - `n`: the security parameter; also specifies the range from which is sampled
    /// - `r`: specifies the Gaussian parameter, which is proportional
    ///     to the standard deviation `sigma * sqrt(2 * pi) = r`
    ///
    /// Returns the rounded matrix as a [`MatZ`] or an error if `n <= 1` or `r <= 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let value = MatQ::from_str("[[5/2, 1]]").unwrap();
    /// let rounded = value.randomized_rounding(3,5).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///     if `n <= 1` or `r <= 0`.
    ///
    /// This function implements randomized rounding according to:
    /// - \[1\] Peikert, C. (2010, August).
    ///     An efficient and parallel Gaussian sampler for lattices.
    ///     In: Annual Cryptology Conference (pp. 80-97).
    ///     <https://link.springer.com/chapter/10.1007/978-3-642-14623-7_5>
    pub fn randomized_rounding(&self, r: impl Into<Q>, n: impl Into<Z>) -> Result<MatZ, MathError> {
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        let r = r.into();
        let n = n.into();
        for i in 0..out.get_num_rows() {
            for j in 0..out.get_num_columns() {
                let entry = self.get_entry(i, j).unwrap().randomized_rounding(&r, &n)?;
                out.set_entry(i, j, entry).unwrap();
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_floor {
    use crate::{integer::MatZ, rational::MatQ};
    use std::str::FromStr;

    // Ensure that positive rationals are rounded correctly
    #[test]
    fn positive() {
        let value = MatQ::from_str(&format!("[[1/{}, {}/2]]", u64::MAX, i64::MAX)).unwrap();
        let cmp = MatZ::from_str(&format!("[[0, {}]]", (i64::MAX - 1) / 2)).unwrap();

        assert_eq!(cmp, value.floor());
    }

    // Ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let value = MatQ::from_str(&format!("[[-1/{}, -{}/2]]", u64::MAX, i64::MAX)).unwrap();
        let cmp = MatZ::from_str(&format!("[[-1, {}]]", (-i64::MAX - 1) / 2)).unwrap();

        assert_eq!(cmp, value.floor());
    }
}

#[cfg(test)]
mod test_ceil {
    use crate::{integer::MatZ, rational::MatQ};
    use std::str::FromStr;

    // Ensure that positive rationals are rounded correctly
    #[test]
    fn positive() {
        let value = MatQ::from_str(&format!("[[1/{}, {}/2]]", u64::MAX, i64::MAX)).unwrap();
        let cmp = MatZ::from_str(&format!("[[1, {}]]", (i64::MAX - 1) / 2 + 1)).unwrap();

        assert_eq!(cmp, value.ceil());
    }

    // Ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let value = MatQ::from_str(&format!("[[-1/{}, -{}/2]]", u64::MAX, i64::MAX)).unwrap();
        let cmp = MatZ::from_str(&format!("[[0, {}]]", (-i64::MAX - 1) / 2 + 1)).unwrap();

        assert_eq!(cmp, value.ceil());
    }
}

#[cfg(test)]
mod test_round {
    use crate::{integer::MatZ, rational::MatQ};
    use std::str::FromStr;

    // Ensure that positive rationals are rounded correctly
    #[test]
    fn positive() {
        let value = MatQ::from_str(&format!("[[1/{}, {}/2]]", u64::MAX, i64::MAX)).unwrap();
        let cmp = MatZ::from_str(&format!("[[0, {}]]", (i64::MAX - 1) / 2 + 1)).unwrap();

        assert_eq!(cmp, value.round());
    }

    // Ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let value = MatQ::from_str(&format!("[[-1/{}, -{}/2]]", u64::MAX, i64::MAX)).unwrap();
        let cmp = MatZ::from_str(&format!("[[0, {}]]", (-i64::MAX - 1) / 2 + 1)).unwrap();

        assert_eq!(cmp, value.round());
    }
}

#[cfg(test)]
mod test_randomized_rounding {
    use crate::rational::MatQ;
    use std::str::FromStr;

    /// Ensure that a `n <= 1` throws an error
    #[test]
    fn small_n() {
        let value = MatQ::from_str("[[5/2, 1]]").unwrap();
        assert!(value.randomized_rounding(3, 1).is_err());
        assert!(value.randomized_rounding(3, -3).is_err());
    }

    /// Ensure that a `r <= 0` throws an error
    #[test]
    fn negative_r() {
        let value = MatQ::from_str("[[5/2, 1]]").unwrap();
        assert!(value.randomized_rounding(0, 5).is_err());
        assert!(value.randomized_rounding(-1, 5).is_err());
    }
}
