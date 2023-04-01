// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains helpful functions on [`fmpz`] that return a [`Z`] value.

use super::Z;
use flint_sys::fmpz::{fmpz, fmpz_abs, fmpz_cmpabs};

impl Z {
    /// Efficiently finds maximum absolute value and returns
    /// a cloned [`Z`] instance out of a vector of [`fmpz`] instances.
    ///
    /// Parameters:
    /// - `fmpz_vector`: contains a number of [`fmpz`] instances
    ///
    /// Returns the maximum absolute value out of the given [`fmpz`] vector
    /// as a cloned [`Z`] instance.
    ///
    /// # Example
    /// ```compile_fail
    /// use math::integer::Z;
    ///
    /// let a = Z::from(-4);
    /// let b = Z::from(-2);
    ///
    /// let fmpz_vector = vec![a.value, b.value];
    /// let abs_max = Z::find_max_abs_fmpz(&fmpz_vector);
    /// assert_eq!(abs_max, Z::from(4));
    /// ```
    pub(crate) fn find_max_abs_fmpz(fmpz_vector: &Vec<fmpz>) -> Self {
        // find maximum of absolute fmpz entries
        let mut max = &fmpz(0);
        for entry in fmpz_vector {
            if unsafe { fmpz_cmpabs(max, entry) } < 0 {
                max = entry;
            }
        }

        // clone and ensure that the output absolute maximum value is absolute
        let mut result = Z::ZERO;
        unsafe { fmpz_abs(&mut result.value, max) }
        result
    }
}

#[cfg(test)]
mod test_find_max_abs_fmpz {
    use super::Z;
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Checks whether `find_max_abs_fmpz` works correctly for small positive
    /// [`fmpz`] instances
    #[test]
    fn positive_small() {
        let mat = MatZ::from_str("[[1, 10, 100]]").unwrap();
        let fmpz_vector = mat.collect_entries();

        let abs_max = Z::find_max_abs_fmpz(&fmpz_vector);

        assert_eq!(abs_max, Z::from(100));
    }

    /// Checks whether `find_max_abs_fmpz` works correctly for large positive
    /// [`fmpz`] instances
    #[test]
    fn positive_large() {
        let mat = MatZ::from_str(&format!("[[1, {}, {}, 10]]", i64::MAX, u64::MAX)).unwrap();
        let fmpz_vector = mat.collect_entries();

        let abs_max = Z::find_max_abs_fmpz(&fmpz_vector);

        assert_eq!(abs_max, Z::from(u64::MAX));
    }

    /// Checks whether `find_max_abs_fmpz` works correctly for small negative
    /// [`fmpz`] instances
    #[test]
    fn negative_small() {
        let mat = MatZ::from_str("[[1, -10, -100]]").unwrap();
        let fmpz_vector = mat.collect_entries();

        let abs_max = Z::find_max_abs_fmpz(&fmpz_vector);

        assert_eq!(abs_max, Z::from(100));
    }

    /// Checks whether `find_max_abs_fmpz` works correctly for large negative
    /// [`fmpz`] instances
    #[test]
    fn negative_large() {
        let mat = MatZ::from_str(&format!("[[1, {}, -{}, 10]]", i64::MAX, u64::MAX)).unwrap();
        let fmpz_vector = mat.collect_entries();

        let abs_max = Z::find_max_abs_fmpz(&fmpz_vector);

        assert_eq!(abs_max, Z::from(u64::MAX));
    }
}
