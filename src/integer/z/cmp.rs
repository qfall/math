// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to compare [`Z`] with other values.
//! This uses the traits from [`std::cmp`].

use super::Z;
use flint_sys::fmpz::{fmpz_cmp, fmpz_equal};
use std::cmp::Ordering;

impl PartialEq for Z {
    /// Checks if two integers are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let a: Z = Z::from(42);
    /// let b: Z = Z::from(24);
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (Z::eq(&a,&b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { 1 == fmpz_equal(&self.value, &other.value) }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for Z {}

impl PartialOrd for Z {
    /// Compares two [`Z`] values. Used by the `<`, `<=`, `>`, and `>=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns the [`Ordering`] of the elements.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a: Z = Z::from(10);
    /// let b: Z = Z::from(42);
    ///
    /// assert!(a < b);
    /// assert!(a <= b);
    /// assert!(b > a);
    /// assert!(b >= a);
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Z {
    //! Enables the usage of `max`, `min`, and `clamp`.
    //!
    //! # Examples
    //! ```
    //! use qfall_math::integer::Z;
    //! use std::cmp::{max, min};
    //!
    //! let a: Z = Z::from(10);
    //! let b: Z = Z::from(42);
    //!
    //! assert_eq!(b, max(a.clone(), b.clone()));
    //! assert_eq!(a, min(a.clone(), b.clone()));
    //! assert_eq!(a, Z::ZERO.clamp(a.clone(), b.clone()));
    //! ```

    /// Compares two [`Z`] values. Used by the `<`, `<=`, `>`, and `>=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns the [`Ordering`] of the elements.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a: Z = Z::from(10);
    /// let b: Z = Z::from(42);
    ///
    /// assert!(a < b);
    /// assert!(a <= b);
    /// assert!(b > a);
    /// assert!(b >= a);
    /// ```
    fn cmp(&self, other: &Self) -> Ordering {
        unsafe { fmpz_cmp(&self.value, &other.value).cmp(&0) }
    }
}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {
    // Test case structure:
    // 1. Different ways to use equal and not equal.
    // 2. Test different combinations of equal and not equal with different
    //    parameter length combinations.
    //    Not equal test are inverted equal tests.

    use super::Z;

    /// Demonstrate the different ways to use equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn equal_call_methods() {
        let one_1 = Z::from(1);
        let one_2 = Z::from(1);

        assert!(one_1 == one_2);
        assert!(&one_1 == &one_2);
        assert!(one_1.eq(&one_2));
        assert!(Z::eq(&one_1, &one_2));
        assert_eq!(one_1, one_2);
    }

    /// Demonstrate the different ways to use not equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn not_equal_call_methods() {
        let one = Z::from(1);
        let two = Z::from(2);

        assert!(one != two);
        assert!(&one != &two);
        assert!(one.ne(&two));
        assert!(Z::ne(&one, &two));
        assert_ne!(one, two);
    }

    /// Test equal with small positive and negative numbers.
    #[test]
    fn equal_small() {
        let small_1 = Z::from(10);
        let small_2 = Z::from(10);

        assert!(small_1 == small_2);
        assert!(small_2 == small_1);
        assert!(small_1 == small_1);
    }

    /// Test not equal with small positive and negative numbers.
    #[test]
    fn not_equal_small() {
        let small_1 = Z::from(10);
        let negative = Z::from(-1);

        assert!(small_1 != negative);
        assert!(negative != small_1);
    }

    /// Test equal with a large [`Z`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn equal_large() {
        let max_1 = Z::from(u64::MAX);
        let max_2 = Z::from(u64::MAX);
        let min = Z::from(i64::MIN);

        assert!(max_1 == max_2);
        assert!(max_2 == max_1);
        assert!(max_1 == max_1);
        assert!(min == min);
    }

    /// Test not equal with a large [`Z`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn not_equal_large() {
        let max_1 = Z::from(u64::MAX);
        let min = Z::from(i64::MIN);

        assert!(max_1 != min);
        assert!(min != max_1);
    }

    /// Test not equal with a large [`Z`] (uses FLINT's pointer representation)
    /// and small [`Z`] (no pointer representation).
    #[test]
    fn not_equal_large_small() {
        let max = Z::from(u64::MAX);
        let small_positive = Z::from(1);
        let small_negative = Z::from(-1);
        let min = Z::from(i64::MIN);

        assert!(max != small_negative);
        assert!(small_negative != max);
        assert!(max != small_positive);
        assert!(small_positive != max);

        assert!(min != small_negative);
        assert!(small_negative != min);
        assert!(min != small_positive);
        assert!(small_positive != min);
    }
}

/// Test the [`PartialOrd`] trait implementation for [`Z`]
#[allow(clippy::neg_cmp_op_on_partial_ord)]
#[cfg(test)]
mod test_partial_ord {
    use super::Z;

    /// Test less (<) comparison between small positive and negative [`Z`]
    /// (FLINT is not using pointers)
    #[test]
    fn less_small() {
        let small_positive_1 = Z::from(1);
        let small_negative = Z::from(-1);

        assert!(small_negative < small_positive_1);
    }

    /// Test less (<) comparison between large [`Z`] (FLINT uses pointers)
    /// and small [`Z`] (not using pointers).
    #[test]
    fn less_large_small() {
        let max = Z::from(u64::MAX);
        let small_positive = Z::from(1);
        let small_negative = Z::from(-1);
        let max_negative = Z::from(i64::MIN);

        // Comparisons with max
        assert!(small_positive < max);
        assert!(small_negative < max);

        // Comparisons with max_negative
        assert!(max_negative < small_positive);
        assert!(max_negative < small_negative);
    }

    /// Test less (<) comparison between large positive and negative [`Z`]
    /// (FLINT uses pointers)
    #[test]
    fn less_large() {
        let max_1 = Z::from(u64::MAX);
        let max_negative = Z::from(i64::MIN);

        assert!(max_negative < max_1);
    }

    /// Test less or equal (<=) comparison between small positive and negative [`Z`]
    /// (FLINT is not using pointers)
    #[test]
    fn less_equal_small() {
        let small_positive_1 = Z::from(1);
        let small_positive_2 = Z::from(1);
        let small_negative = Z::from(-1);

        assert!(small_positive_1 <= small_positive_2);
        assert!(small_positive_2 <= small_positive_1);
        assert!(small_positive_1 <= small_positive_1);

        assert!(small_negative <= small_positive_1);
        assert!(small_negative <= small_negative);
    }

    /// Test less or equal (<=) comparison between large [`Z`] (FLINT uses pointers)
    /// and small [`Z`] (not using pointers).
    #[test]
    fn less_equal_large_small() {
        let max = Z::from(u64::MAX);
        let small_positive = Z::from(1);
        let small_negative = Z::from(-1);
        let max_negative = Z::from(i64::MIN);

        // Comparisons with max
        assert!(small_positive <= max);
        assert!(small_negative <= max);

        // Comparisons with max_negative
        assert!(max_negative <= small_positive);
        assert!(max_negative <= small_negative);
    }

    /// Test less or equal (<=) comparison between large positive and negative [`Z`]
    /// (FLINT uses pointers)
    #[test]
    fn less_equal_large() {
        let max_1 = Z::from(u64::MAX);
        let max_2 = Z::from(u64::MAX);
        let max_negative = Z::from(i64::MIN);

        assert!(max_1 <= max_2);
        assert!(max_2 <= max_1);
        assert!(max_1 <= max_1);

        assert!(max_negative <= max_1);
        assert!(max_negative <= max_negative);
    }

    /// Test greater (>) comparison between small positive and negative [`Z`]
    /// (FLINT is not using pointers)
    #[test]
    fn greater_small() {
        let small_positive_1 = Z::from(1);
        let small_negative = Z::from(-1);

        assert!(small_positive_1 > small_negative);
    }

    /// Test greater (>) comparison between large [`Z`] (FLINT uses pointers)
    /// and small [`Z`] (not using pointers).
    #[test]
    fn greater_large_small() {
        let max = Z::from(u64::MAX);
        let small_positive = Z::from(1);
        let small_negative = Z::from(-1);
        let max_negative = Z::from(i64::MIN);

        // Comparisons with max
        assert!(max > small_positive);
        assert!(max > small_negative);

        // Comparisons with max_negative
        assert!(small_positive > max_negative);
        assert!(small_negative > max_negative);
    }

    /// Test greater (>) comparison between large positive and negative [`Z`]
    /// (FLINT uses pointers)
    #[test]
    fn greater_large() {
        let max_1 = Z::from(u64::MAX);
        let max_negative = Z::from(i64::MIN);

        assert!(max_1 > max_negative);
    }

    /// Test greater or equal (>=) comparison between small positive and negative [`Z`]
    /// (FLINT is not using pointers)
    #[test]
    fn greater_equal_small() {
        let small_positive_1 = Z::from(1);
        let small_positive_2 = Z::from(1);
        let small_negative = Z::from(-1);

        assert!(small_positive_1 >= small_positive_2);
        assert!(small_positive_2 >= small_positive_1);
        assert!(small_positive_1 >= small_positive_1);

        assert!(small_positive_1 >= small_negative);
        assert!(small_negative >= small_negative);
    }

    /// Test greater or equal (>=) comparison between large [`Z`] (FLINT uses pointers)
    /// and small [`Z`] (not using pointers).
    #[test]
    fn greater_equal_large_small() {
        let max = Z::from(u64::MAX);
        let small_positive = Z::from(1);
        let small_negative = Z::from(-1);
        let max_negative = Z::from(i64::MIN);

        // Comparisons with max
        assert!(max >= small_positive);
        assert!(max >= small_negative);

        // Comparisons with max_negative
        assert!(small_positive >= max_negative);
        assert!(small_negative >= max_negative);
    }

    /// Test greater or equal (>=) comparison between large positive and negative [`Z`]
    /// (FLINT uses pointers)
    #[test]
    fn greater_equal_large() {
        let max_1 = Z::from(u64::MAX);
        let max_2 = Z::from(u64::MAX);
        let max_negative = Z::from(i64::MIN);

        assert!(max_1 >= max_2);
        assert!(max_2 >= max_1);
        assert!(max_1 >= max_1);

        assert!(max_1 >= max_negative);
        assert!(max_negative >= max_negative);
    }
}

#[cfg(test)]
mod test_ord {
    use super::Z;
    use std::cmp::{max, min};

    // `cmp` is extensively tested in module `test_partial_eq`, hence omitted here

    /// Check whether default implementations `max`, `min`, `clamp`
    /// work properly for small numbers
    #[test]
    fn default_implementations_small() {
        let a: Z = Z::from(10);
        let b: Z = Z::from(42);

        assert_eq!(b, max(a.clone(), b.clone()));
        assert_eq!(a, min(a.clone(), b.clone()));

        assert_eq!(a, Z::ZERO.clamp(a.clone(), b.clone()));
        assert_eq!(a, a.clone().clamp(Z::ZERO, b.clone()));
        assert_eq!(a, b.clamp(Z::ZERO, a.clone()));
    }

    /// Check whether default implementations `max`, `min`, `clamp`
    /// work properly for large numbers
    #[test]
    fn default_implementations_large() {
        let a: Z = Z::from(i64::MAX);
        let b: Z = Z::from(u64::MAX);

        assert_eq!(b, max(a.clone(), b.clone()));
        assert_eq!(a, min(a.clone(), b.clone()));

        assert_eq!(a, Z::ZERO.clamp(a.clone(), b.clone()));
        assert_eq!(a, a.clone().clamp(Z::ZERO, b.clone()));
        assert_eq!(a, b.clamp(Z::ZERO, a.clone()));
    }
}
