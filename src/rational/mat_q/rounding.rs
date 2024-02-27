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
    integer::MatZ,
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
