// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations for comparison of [`MatZq`].

use super::MatZq;
use flint_sys::{fmpz::fmpz_equal, fmpz_mat::fmpz_mat_equal};

impl PartialEq for MatZq {
    /// Checks if two [`MatZq`] instances are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is compare against `self`
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Example
    /// ```
    /// use math::integer::MatZq;
    /// use std::str::FromStr;
    ///
    /// let a = MatZq::from_str("[[1,2],[3,4]] mod 4").unwrap();
    /// let b = MatZq::from_str("[[1,2],[2,4]] mod 4").unwrap();
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (MatZq::eq(&a,&b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            fmpz_equal(&self.matrix.mod_[0], &other.matrix.mod_[0]) != 0
                && fmpz_mat_equal(&self.matrix.mat[0], &other.matrix.mat[0]) != 0
        }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for MatZq {}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {

    use crate::traits::SetEntry;

    use super::MatZq;
    use std::str::FromStr;

    /// Ensures that different instantiations do not break the equality between matrices
    #[test]
    fn equality_between_instantiations() {
        let a = MatZq::from_str("[[0,1],[0,0]] mod 4").unwrap();
        let mut b = MatZq::new(2, 2, 4).unwrap();
        b.set_entry(0, 1, 1).unwrap();

        assert_eq!(a, b);
    }

    /// Checks that large and small entries (and different points in storage) do not break equality
    #[test]
    fn equality_for_large_and_small_entries() {
        let mat_str_1 = format!(
            "[[{},{}, 1],[-10, 10, 0],[0, 1, -10]] mod {}",
            i64::MAX - 1,
            i64::MAX,
            u64::MAX
        );
        let mat_str_2 = format!(
            "[[{},{}, 1],[-10, 10, 0],[{}, 1, -10]] mod {}",
            i64::MAX - 1,
            i64::MAX,
            u64::MAX,
            u64::MAX
        );
        let a = MatZq::from_str(&mat_str_1).unwrap();
        let b = MatZq::from_str(&mat_str_1).unwrap();
        let c = MatZq::from_str(&mat_str_2).unwrap();

        assert_eq!(&a, &b);
        assert_eq!(&a, &c);
    }

    /// Checks that different unequal matrices with same modulus are unequal
    #[test]
    fn not_equal_same_modulus() {
        let a =
            MatZq::from_str(&format!("[[{},{}],[-10, 10]] mod 42", i64::MIN, i64::MAX)).unwrap();
        let b = MatZq::from_str(&format!("[[0,{}],[-10, 10]] mod 42", i64::MAX)).unwrap();
        let c = MatZq::from_str(&format!(
            "[[{},{}],[-10, 10],[0,0]] mod 42",
            i64::MIN,
            i64::MAX
        ))
        .unwrap();
        let d = MatZq::from_str(&format!("[[{},{}]] mod 42", i64::MIN, i64::MAX)).unwrap();
        let e = MatZq::from_str("[[0]] mod 42").unwrap();

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

    /// Checks that the same matrix with different modulus are unequal
    #[test]
    fn not_equal_different_modulus() {
        let a = MatZq::from_str("[[0,1],[0,0]] mod 4").unwrap();
        let b = MatZq::from_str("[[0,1],[0,0]] mod 8").unwrap();

        let c = MatZq::from_str(&format!("[[0]] mod {}", u64::MAX)).unwrap();
        let d = MatZq::from_str(&format!("[[0]] mod {}", u64::MAX - 1)).unwrap();
        let e = MatZq::from_str(&format!("[[0]] mod {}", c.matrix.mod_[0].0 as u64)).unwrap();

        assert_ne!(a, b);

        assert_ne!(c, d);
        assert_ne!(c, e);
    }
}
