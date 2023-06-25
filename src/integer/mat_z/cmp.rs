// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations for comparison of [`MatZ`].

use super::MatZ;
use flint_sys::fmpz_mat::fmpz_mat_equal;

impl PartialEq for MatZ {
    /// Checks if two [`MatZ`] instances are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is compare against `self`
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::from_str("[[1,2],[3,4]]").unwrap();
    /// let b = MatZ::from_str("[[1,2],[2,4]]").unwrap();
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (MatZ::eq(&a, &b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { fmpz_mat_equal(&self.matrix, &other.matrix) != 0 }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for MatZ {}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {
    use super::MatZ;
    use crate::traits::SetEntry;
    use std::str::FromStr;

    /// Ensures that different instantiations do not break the equality between matrices
    #[test]
    fn equality_between_instantiations() {
        let a = MatZ::from_str("[[0,1],[0,0]]").unwrap();
        let mut b = MatZ::new(2, 2);
        b.set_entry(0, 1, 1).unwrap();

        assert_eq!(a, b);
    }

    /// Checks that large and small entries (and different points in storage) do not break equality
    #[test]
    fn equality_for_large_and_small_entries() {
        let a = MatZ::from_str(&format!(
            "[[{},{}, 1],[-10, 10, 0],[0, 1, -10]]",
            i64::MIN,
            i64::MAX
        ))
        .unwrap();
        let b = MatZ::from_str(&format!(
            "[[{},{}, 1],[-10, 10, 0],[0, 1, -10]]",
            i64::MIN,
            i64::MAX
        ))
        .unwrap();

        assert_eq!(&a, &b);
    }

    /// Checks that different unequal matrices are unequal
    #[test]
    fn not_equal() {
        let a = MatZ::from_str(&format!("[[{},{}],[-10, 10]]", i64::MIN, i64::MAX)).unwrap();
        let b = MatZ::from_str(&format!("[[0,{}],[-10, 10]]", i64::MAX)).unwrap();
        let c = MatZ::from_str(&format!("[[{},{}],[-10, 10],[0,0]]", i64::MIN, i64::MAX)).unwrap();
        let d = MatZ::from_str(&format!("[[{},{}]]", i64::MIN, i64::MAX)).unwrap();
        let e = MatZ::from_str("[[0]]").unwrap();

        assert_ne!(&a, &b);
        assert_ne!(&a, &c);
        assert_ne!(&a, &d);
        assert_ne!(&a, &e);
        assert_ne!(&b, &c);
        assert_ne!(&b, &d);
        assert_ne!(&b, &e);
        assert_ne!(&c, &d);
        assert_ne!(&c, &e);
        assert_ne!(&d, &e);
    }
}
