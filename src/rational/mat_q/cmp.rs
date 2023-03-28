// Copyright © 2023 Sven Moog, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations for comparison of [`MatQ`].

use super::MatQ;
use flint_sys::fmpq_mat::fmpq_mat_equal;

impl PartialEq for MatQ {
    /// Checks if two [`MatQ`] instances are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is compare against `self`
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Example
    /// ```
    /// use math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a1 = MatQ::from_str("[[1/2,2],[3/2,4]]").unwrap();
    /// let a2 = MatQ::from_str("[[2/4,2],[3/2,4]]").unwrap();
    /// assert!(a1==a2);
    ///
    /// let b = MatQ::from_str("[[1,2],[2,4]]").unwrap();
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a1 == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a1 == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a1.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (MatQ::eq(&a1,&b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { fmpq_mat_equal(&self.matrix, &other.matrix) != 0 }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for MatQ {}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {

    use super::MatQ;
    use crate::rational::Q;
    use std::str::FromStr;

    /// Ensures that different instantiations do not break the equality between matrices
    #[test]
    fn equality_between_instantiations() {
        let a = MatQ::from_str("[[0,1],[0,0]]").unwrap();
        let mut b = MatQ::new(2, 2).unwrap();
        b.set_entry(0, 1, Q::from_str("1/1").unwrap()).unwrap();

        assert_eq!(a, b);
    }

    /// Checks that large and small entries (and different points in storage) do not break equality
    #[test]
    fn equality_for_large_and_small_entries() {
        let a = MatQ::from_str(&format!(
            "[[{},{}, 1],[-10, 10, 0],[0, 1, -10]]",
            i64::MIN,
            i64::MAX
        ))
        .unwrap();
        let b = MatQ::from_str(&format!(
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
        let a = MatQ::from_str(&format!("[[{},{}],[-10, 10]]", i64::MIN, i64::MAX)).unwrap();
        let b = MatQ::from_str(&format!("[[0,{}],[-10, 10]]", i64::MAX)).unwrap();
        let c = MatQ::from_str(&format!("[[{},{}],[-10, 10],[0,0]]", i64::MIN, i64::MAX)).unwrap();
        let d = MatQ::from_str(&format!("[[{},{}]]", i64::MIN, i64::MAX)).unwrap();
        let e = MatQ::from_str("[[0]]").unwrap();

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
