// Copyright © 2023 Sven Moog, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations for comparison of [`MatQ`].

use super::MatQ;
use crate::{
    integer::MatZ,
    macros::for_others::implement_trait_reverse,
    traits::{CompareBase, MatrixDimensions, MatrixGetEntry},
};
use flint_sys::{
    fmpq_mat::{fmpq_mat_equal, fmpq_mat_set_fmpz_mat_div_fmpz},
    fmpz::fmpz,
};

impl PartialEq for MatQ {
    /// Checks if two [`MatQ`] instances are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is compare against `self`
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a_1 = MatQ::from_str("[[1/2, 2],[3/2, 4]]").unwrap();
    /// let a_2 = MatQ::from_str("[[2/4, 2],[3/2, 4]]").unwrap();
    /// assert!(a_1 == a_2);
    ///
    /// let b = MatQ::from_str("[[1, 2],[2, 4]]").unwrap();
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a_1 == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a_1 == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a_1.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (MatQ::eq(&a_1, &b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { fmpq_mat_equal(&self.matrix, &other.matrix) != 0 }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for MatQ {}

impl PartialEq<MatZ> for MatQ {
    /// Checks if an integer matrix and a rational matrix are equal. Used by the `==` and `!=` operators.
    /// [`PartialEq`] is also implemented for [`MatZ`] using [`MatQ`].
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    /// let a: MatQ = MatQ::from_str("[[42, 2],[3, 4]]").unwrap();
    /// let b: MatZ = MatZ::from_str("[[42, 2],[3, 4]]").unwrap();
    ///
    /// // These are all equivalent and return true.
    /// let compared: bool = (a == b);
    /// # assert!(compared);
    /// let compared: bool = (b == a);
    /// # assert!(compared);
    /// let compared: bool = (&a == &b);
    /// # assert!(compared);
    /// let compared: bool = (&b == &a);
    /// # assert!(compared);
    /// let compared: bool = (a.eq(&b));
    /// # assert!(compared);
    /// let compared: bool = (b.eq(&a));
    /// # assert!(compared);
    /// let compared: bool = (MatQ::eq(&a, &b));
    /// # assert!(compared);
    /// let compared: bool = (MatZ::eq(&b, &a));
    /// # assert!(compared);
    /// ```
    fn eq(&self, other: &MatZ) -> bool {
        let num_rows = self.get_num_rows();
        let num_cols = self.get_num_columns();

        if num_rows != other.get_num_rows() || num_cols != other.get_num_columns() {
            return false;
        }

        for i in 0..num_rows {
            for j in 0..num_cols {
                if unsafe { self.get_entry_unchecked(i, j) != other.get_entry_unchecked(i, j) } {
                    return false;
                }
            }
        }

        true
    }
}

impl MatQ {
    pub fn equal(self, other: MatZ) -> bool {
        let mut other_matq = MatQ::new(other.get_num_rows(), other.get_num_columns());
        unsafe { fmpq_mat_set_fmpz_mat_div_fmpz(&mut other_matq.matrix, &other.matrix, &fmpz(1)) };
        1 != unsafe { fmpq_mat_equal(&other_matq.matrix, &self.matrix) }
    }
}

implement_trait_reverse!(PartialEq, eq, MatZ, MatQ, bool);

impl CompareBase for MatQ {}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {
    use super::MatQ;
    use crate::{rational::Q, traits::MatrixSetEntry};
    use std::str::FromStr;

    /// Ensures that different instantiations do not break the equality between matrices
    #[test]
    fn equality_between_instantiations() {
        let a = MatQ::from_str("[[0, 1/2],[0/2, 0]]").unwrap();
        let mut b = MatQ::new(2, 2);
        b.set_entry(0, 1, Q::from((2, 4))).unwrap();

        assert_eq!(a, b);
    }

    /// Checks that large and small entries (and different points in storage) do not break equality
    #[test]
    fn equality_for_large_and_small_entries() {
        let mat_str_1 = &format!(
            "[[{}/{}, {}/{}, 1],[-10, 10, 0],[0, 1, -10]]",
            i64::MIN,
            i64::MIN + 1,
            i64::MAX,
            i64::MAX - 1
        );

        // like mat_str_1 but also 2nd row is expanded by 2
        let mat_str_2 = &format!(
            "[[{}/{}, {}/{}, 1],[-20/2, 20/2, 0/2],[0, 1, -10]]",
            i64::MIN,
            i64::MIN + 1,
            i64::MAX,
            i64::MAX - 1
        );

        let a = MatQ::from_str(mat_str_1).unwrap();
        let b = MatQ::from_str(mat_str_1).unwrap();
        let c = MatQ::from_str(mat_str_2).unwrap();

        assert_eq!(&a, &b);
        assert_eq!(&a, &c);
    }

    /// Checks that different unequal matrices are unequal
    #[test]
    fn not_equal() {
        let a = MatQ::from_str(&format!("[[{}, {}],[-10, 10]]", i64::MIN, i64::MAX)).unwrap();
        let b = MatQ::from_str(&format!("[[0, {}],[-10, 10]]", i64::MAX)).unwrap();
        let c =
            MatQ::from_str(&format!("[[{}, {}],[-10, 10],[0, 0]]", i64::MIN, i64::MAX)).unwrap();
        let d = MatQ::from_str(&format!("[[{}, {}]]", i64::MIN, i64::MAX)).unwrap();
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

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq_q_other {
    use super::MatQ;
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensure that the function can be called with several types.
    #[test]
    #[allow(clippy::op_ref)]
    fn availability() {
        let q = MatQ::from_str("[[1, 2],[3, 4]]").unwrap();
        let z = MatZ::from_str("[[1, 2],[3, 4]]").unwrap();

        assert!(q == z);
        assert!(z == q);
        assert!(&q == &z);
        assert!(&z == &q);
    }

    /// Ensure that large values are compared correctly.
    #[test]
    fn equal_large() {
        let q = MatQ::from_str(&format!("[[1,2],[3,{}]]", u64::MAX)).unwrap();
        let z = MatZ::from_str(&format!("[[1,2],[3,{}]]", u64::MAX)).unwrap();

        assert!(q == z);
    }
}
