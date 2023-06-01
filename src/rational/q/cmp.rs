// Copyright © 2023 Sven Moog, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to compare [`Q`] with other values.
//! This uses the traits from [`std::cmp`].

use super::Q;
use flint_sys::fmpq::{fmpq_cmp, fmpq_equal};
use std::cmp::Ordering;

impl PartialEq for Q {
    /// Checks if two rationals are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    /// let a: Q = Q::from_str("42/24").unwrap();
    /// let b: Q = Q::from_str("24/42").unwrap();
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (Q::eq(&a,&b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { 1 == fmpq_equal(&self.value, &other.value) }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
// We do not allow division by zero, therefore, this is the case.
impl Eq for Q {}

impl PartialOrd for Q {
    /// Compares two [`Q`] values. Used by the `<`, `<=`, `>`, and `>=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns the [`Ordering`] of the elements.
    ///
    /// # Examples
    /// ```
    /// # use qfall_math::error::MathError;
    /// use qfall_math::rational::Q;
    ///
    /// let a: Q = Q::from((1,10));
    /// let b: Q = Q::from((2,10));
    ///
    /// assert!(a < b);
    /// assert!(a <= b);
    /// assert!(b > a);
    /// assert!(b >= a);
    ///
    /// assert!(&a < &b);
    /// # Ok::<(), MathError>(())
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Q {
    //! Enables the usage of `max`, `min`, and `clamp`.
    //!
    //! # Examples
    //! ```
    //! use qfall_math::rational::Q;
    //! use std::cmp::{max, min};
    //!
    //! let a: Q = Q::from(10);
    //! let b: Q = Q::from(42);
    //!
    //! assert_eq!(b, max(a.clone(), b.clone()));
    //! assert_eq!(a, min(a.clone(), b.clone()));
    //! assert_eq!(a, Q::ZERO.clamp(a.clone(), b.clone()));
    //! ```

    /// Compares two [`Q`] values. Used by the `<`, `<=`, `>`, and `>=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns the [`Ordering`] of the elements.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let a: Q = Q::from(10);
    /// let b: Q = Q::from(42);
    ///
    /// assert!(a < b);
    /// assert!(a <= b);
    /// assert!(b > a);
    /// assert!(b >= a);
    /// ```
    fn cmp(&self, other: &Self) -> Ordering {
        unsafe { fmpq_cmp(&self.value, &other.value).cmp(&0) }
    }
}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {
    /// Test case structure:
    /// 1. Different ways to use equal and not equal.
    /// 2. Test different combinations of equal and not equal with different
    ///    parameter length combinations.
    ///    Not equal test are inverted equal tests.
    use super::Q;
    use std::str::FromStr;

    /// Demonstrate the different ways to use equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn equal_call_methods() {
        let one_1 = Q::from_str("1").unwrap();
        let one_2 = Q::from_str("1").unwrap();

        assert!(one_1 == one_2);
        assert!(&one_1 == &one_2);
        assert!(one_1.eq(&one_2));
        assert!(Q::eq(&one_1, &one_2));
        assert_eq!(one_1, one_2);
    }

    /// Demonstrate the different ways to use not equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn not_equal_call_methods() {
        let one = Q::from_str("1").unwrap();
        let two = Q::from_str("2").unwrap();

        assert!(one != two);
        assert!(&one != &two);
        assert!(one.ne(&two));
        assert!(Q::ne(&one, &two));
        assert_ne!(one, two);
    }

    /// Test equal with small positive and negative numbers.
    #[test]
    fn equal_small() {
        let small_1 = Q::from_str("10").unwrap();
        let small_2 = Q::from_str("10").unwrap();
        let negative = Q::from_str("-1").unwrap();

        assert!(small_1 == small_2);
        assert!(small_2 == small_1);
        assert!(small_1 == small_1);
        assert!(!(small_1 == negative));
        assert!(!(negative == small_1));
    }

    /// Test not equal with small positive and negative numbers.
    #[test]
    fn not_equal_small() {
        let small_1 = Q::from_str("10").unwrap();
        let small_2 = Q::from_str("10").unwrap();
        let negative = Q::from_str("-1").unwrap();

        assert!(!(small_1 != small_2));
        assert!(!(small_2 != small_1));
        assert!(!(small_1 != small_1));
        assert!(small_1 != negative);
        assert!(negative != small_1);
    }

    /// Test equal with a large [`Q`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn equal_large() {
        let max_1 = Q::from_str(&"1".repeat(65)).unwrap();
        let max_2 = Q::from_str(&"1".repeat(65)).unwrap();
        let large_negative_str = format!("-{:1<65}", "1");
        let min = Q::from_str(&large_negative_str).unwrap();

        assert!(max_1 == max_2);
        assert!(max_2 == max_1);
        assert!(max_1 == max_1);
        assert!(min == min);
        assert!(!(max_1 == min));
        assert!(!(min == max_1));
    }

    /// Test not equal with a large [`Q`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn not_equal_large() {
        let max_1 = Q::from_str(&"1".repeat(65)).unwrap();
        let max_2 = Q::from_str(&"1".repeat(65)).unwrap();
        let large_negative_str = format!("-{:1<65}", "1");
        let min = Q::from_str(&large_negative_str).unwrap();

        assert!(!(max_1 != max_2));
        assert!(!(max_2 != max_1));
        assert!(!(max_1 != max_1));
        assert!(!(min != min));
        assert!(max_1 != min);
        assert!(min != max_1);
    }

    /// Test equal with a large [`Q`] (uses FLINT's pointer representation)
    /// and small [`Q`] (no pointer representation).
    #[test]
    fn equal_large_small() {
        let max = Q::from_str(&"1".repeat(65)).unwrap();
        let small_positive = Q::from_str("1").unwrap();
        let small_negative = Q::from_str("-1").unwrap();
        let large_negative_str = format!("-{:1<65}", "1");
        let min = Q::from_str(&large_negative_str).unwrap();

        assert!(!(max == small_negative));
        assert!(!(small_negative == max));
        assert!(!(max == small_positive));
        assert!(!(small_positive == max));

        assert!(!(min == small_negative));
        assert!(!(small_negative == min));
        assert!(!(min == small_positive));
        assert!(!(small_positive == min));
    }

    /// Test not equal with a large [`Q`] (uses FLINT's pointer representation)
    /// and small [`Q`] (no pointer representation).
    #[test]
    fn not_equal_large_small() {
        let max = Q::from_str(&"1".repeat(65)).unwrap();
        let small_positive = Q::from_str("1").unwrap();
        let small_negative = Q::from_str("-1").unwrap();
        let large_negative_str = format!("-{:1<65}", "1");
        let min = Q::from_str(&large_negative_str).unwrap();

        assert!(max != small_negative);
        assert!(small_negative != max);
        assert!(max != small_positive);
        assert!(small_positive != max);

        assert!(min != small_negative);
        assert!(small_negative != min);
        assert!(min != small_positive);
        assert!(small_positive != min);
    }

    /// Test equal with small [`Q`] that have a large denominator
    /// (uses FLINT's pointer representation)
    #[test]
    fn equal_large_denominator() {
        let large_denominator_str = format!("1/{:1<200}", "1");
        let large_denominator_less_str = format!("1/{:1<201}", "1");

        let small_1 = Q::from_str(&large_denominator_str).unwrap();
        let small_2 = Q::from_str(&large_denominator_str).unwrap();
        let less = Q::from_str(&large_denominator_less_str).unwrap();

        assert!(small_1 == small_2);
        assert!(small_2 == small_1);
        assert!(small_1 == small_1);

        assert!(less == less);
        assert!(!(small_1 == less));
        assert!(!(less == small_1));
    }

    /// Test equal for [`Q`] with large numerator and denominator
    /// (uses FLINT's pointer representation)
    #[test]
    fn equal_large_numerator_denominator() {
        // The greatest common divisor of numerator and denominator is 1
        // => also large after canonicalization
        let large_denominator_str = format!("{:5<200}/{:4<200}", "1", "1");
        let large_denominator_less_str = format!("{:5<201}/{:4<201}", "1", "1");

        let small_1 = Q::from_str(&large_denominator_str).unwrap();
        let small_2 = Q::from_str(&large_denominator_str).unwrap();
        let less = Q::from_str(&large_denominator_less_str).unwrap();

        assert!(small_1 == small_2);
        assert!(small_2 == small_1);
        assert!(small_1 == small_1);

        assert!(less == less);
        assert!(!(small_1 == less));
        assert!(!(less == small_1));
    }

    /// Ensure that two elements are equal
    #[test]
    fn equal_rational() {
        let a = Q::from_str("1/2").unwrap();
        let b = Q::from_str("2/4").unwrap();

        assert_eq!(a, b);
    }

    /// assert not equal when denominator is different
    #[test]
    fn not_equal_different_denominator() {
        let a = Q::from_str("1/2").unwrap();
        let b = Q::from_str("1/4").unwrap();

        assert_ne!(a, b);
    }

    /// assert equal for `0` when denominator is different
    #[test]
    fn zero_equal_different_denominator() {
        let a = Q::from_str("0/2").unwrap();
        let b = Q::from_str("0/4").unwrap();

        assert_eq!(a, b);
    }
}

/// Test the [`PartialOrd`] trait implementation for [`Q`]
#[allow(clippy::neg_cmp_op_on_partial_ord)]
#[cfg(test)]
mod test_partial_ord {

    use super::Q;

    /// Different ways to compare [`Q`] elements with each other
    #[test]
    fn call_methods() {
        let one = Q::ONE;
        let zero = Q::ZERO;

        assert!(one > zero);
        assert!(one >= zero);
        assert!(!(one < zero));
        assert!(!(one <= zero));

        assert!(&one > &zero);
        assert!(&one >= &zero);
        assert!(!(&one < &zero));
        assert!(!(&one <= &zero));
    }

    /// Test less (<) comparison between small positive and negative [`Q`]
    /// (FLINT is not using pointers)
    #[test]
    fn less_small() {
        let one_1 = Q::ONE;
        let one_2 = Q::ONE;
        let small_negative = Q::from(-1);
        let one_half = Q::try_from((&1, &2)).unwrap();

        assert!(!(one_1 < one_2));
        assert!(!(one_2 < one_1));
        assert!(!(one_1 < one_1));

        assert!(small_negative < one_1);
        assert!(!(one_1 < small_negative));
        assert!(!(small_negative < small_negative));

        assert!(!(one_1 < one_half));
        assert!(one_half < one_1);
        assert!(small_negative < one_half);
        assert!(!(one_half < small_negative));
    }

    /// Test less (<) comparison between large [`Q`] (FLINT uses pointers)
    /// and small [`Q`] (not using pointers).
    #[test]
    fn less_large_small() {
        let large = Q::try_from((&u64::MAX, &2)).unwrap();
        let small_positive = Q::ONE;
        let small_negative = Q::try_from((&(i64::MIN + 1), &i64::MAX)).unwrap();
        let large_negative = Q::from(i64::MIN);

        // Comparisons with max
        assert!(small_positive < large);
        assert!(small_negative < large);
        assert!(!(large < small_positive));
        assert!(!(large < small_negative));

        // Comparisons with max_negative
        assert!(large_negative < small_positive);
        assert!(large_negative < small_negative);
        assert!(!(small_positive < large_negative));
        assert!(!(small_negative < large_negative));
    }

    /// Test less (<) comparison between large positive and negative [`Q`]
    /// (FLINT uses pointers)
    #[test]
    fn less_large() {
        let max_1 = Q::from(u64::MAX);
        let max_2 = Q::from(u64::MAX);
        let max_negative = Q::from(i64::MIN);

        assert!(!(max_1 < max_2));
        assert!(!(max_2 < max_1));
        assert!(!(max_1 < max_1));

        assert!(max_negative < max_1);
        assert!(!(max_1 < max_negative));
        assert!(!(max_negative < max_negative));
    }

    /// Test less or equal (<=) comparison between small positive and negative [`Q`]
    /// (FLINT is not using pointers)
    #[test]
    fn less_equal_small() {
        let small_positive_1 = Q::ONE;
        let small_positive_2 = Q::ONE;
        let small_negative = Q::from(-1);

        assert!(small_positive_1 <= small_positive_2);
        assert!(small_positive_2 <= small_positive_1);
        assert!(small_positive_1 <= small_positive_1);

        assert!(small_negative <= small_positive_1);
        assert!(!(small_positive_1 <= small_negative));
        assert!(small_negative <= small_negative);
    }

    /// Test less or equal (<=) comparison between large [`Q`] (FLINT uses pointers)
    /// and small [`Q`] (not using pointers).
    #[test]
    fn less_equal_large_small() {
        let max = Q::from(u64::MAX);
        let small_positive = Q::ONE;
        let small_negative = Q::from(-1);
        let max_negative = Q::from(i64::MIN);

        // Comparisons with max
        assert!(small_positive <= max);
        assert!(small_negative <= max);
        assert!(!(max <= small_positive));
        assert!(!(max <= small_negative));

        // Comparisons with max_negative
        assert!(max_negative <= small_positive);
        assert!(max_negative <= small_negative);
        assert!(!(small_positive <= max_negative));
        assert!(!(small_negative <= max_negative));
    }

    /// Test less or equal (<=) comparison between large positive and negative [`Q`]
    /// (FLINT uses pointers)
    #[test]
    fn less_equal_large() {
        let max_1 = Q::from(u64::MAX);
        let max_2 = Q::from(u64::MAX);
        let max_negative = Q::from(i64::MIN);

        assert!(max_1 <= max_2);
        assert!(max_2 <= max_1);
        assert!(max_1 <= max_1);

        assert!(max_negative <= max_1);
        assert!(!(max_1 <= max_negative));
        assert!(max_negative <= max_negative);
    }

    /// Test greater (>) comparison between small positive and negative [`Q`]
    /// (FLINT is not using pointers)
    #[test]
    fn greater_small() {
        let small_positive_1 = Q::ONE;
        let small_positive_2 = Q::ONE;
        let small_negative = Q::from(-1);

        assert!(!(small_positive_1 > small_positive_2));
        assert!(!(small_positive_2 > small_positive_1));
        assert!(!(small_positive_1 > small_positive_1));

        assert!(!(small_negative > small_positive_1));
        assert!(small_positive_1 > small_negative);
        assert!(!(small_negative > small_negative));
    }

    /// Test greater (>) comparison between large [`Q`] (FLINT uses pointers)
    /// and small [`Q`] (not using pointers).
    #[test]
    fn greater_large_small() {
        let max = Q::from(u64::MAX);
        let small_positive = Q::ONE;
        let small_negative = Q::from(-1);
        let max_negative = Q::from(i64::MIN);

        // Comparisons with max
        assert!(!(small_positive > max));
        assert!(!(small_negative > max));
        assert!(max > small_positive);
        assert!(max > small_negative);

        // Comparisons with max_negative
        assert!(!(max_negative > small_positive));
        assert!(!(max_negative > small_negative));
        assert!(small_positive > max_negative);
        assert!(small_negative > max_negative);
    }

    /// Test greater (>) comparison between large positive and negative [`Q`]
    /// (FLINT uses pointers)
    #[test]
    fn greater_large() {
        let max_1 = Q::from(u64::MAX);
        let max_2 = Q::from(u64::MAX);
        let max_negative = Q::from(i64::MIN);

        assert!(!(max_1 > max_2));
        assert!(!(max_2 > max_1));
        assert!(!(max_1 > max_1));

        assert!(!(max_negative > max_1));
        assert!(max_1 > max_negative);
        assert!(!(max_negative > max_negative));
    }

    /// Test greater or equal (>=) comparison between small positive and negative [`Q`]
    /// (FLINT is not using pointers)
    #[test]
    fn greater_equal_small() {
        let small_positive_1 = Q::ONE;
        let small_positive_2 = Q::ONE;
        let small_negative = Q::from(-1);

        assert!(small_positive_1 >= small_positive_2);
        assert!(small_positive_2 >= small_positive_1);
        assert!(small_positive_1 >= small_positive_1);

        assert!(!(small_negative >= small_positive_1));
        assert!(small_positive_1 >= small_negative);
        assert!(small_negative >= small_negative);
    }

    /// Test greater or equal (>=) comparison between large [`Q`] (FLINT uses pointers)
    /// and small [`Q`] (not using pointers).
    #[test]
    fn greater_equal_large_small() {
        let max = Q::from(u64::MAX);
        let small_positive = Q::ONE;
        let small_negative = Q::from(-1);
        let max_negative = Q::from(i64::MIN);

        // Comparisons with max
        assert!(!(small_positive >= max));
        assert!(!(small_negative >= max));
        assert!(max >= small_positive);
        assert!(max >= small_negative);

        // Comparisons with max_negative
        assert!(!(max_negative >= small_positive));
        assert!(!(max_negative >= small_negative));
        assert!(small_positive >= max_negative);
        assert!(small_negative >= max_negative);
    }

    /// Test greater or equal (>=) comparison between large positive and negative [`Q`]
    /// (FLINT uses pointers)
    #[test]
    fn greater_equal_large() {
        let max_1 = Q::from(u64::MAX);
        let max_2 = Q::from(u64::MAX);
        let max_negative = Q::from(i64::MIN);

        assert!(max_1 >= max_2);
        assert!(max_2 >= max_1);
        assert!(max_1 >= max_1);

        assert!(!(max_negative >= max_1));
        assert!(max_1 >= max_negative);
        assert!(max_negative >= max_negative);
    }

    /// Compare a number close to zero with zero
    #[test]
    fn close_to_zero() {
        let small = Q::try_from((&1, &u64::MAX)).unwrap();
        let zero = Q::ZERO;

        assert!(small > zero);
        assert!(small >= zero);
        assert!(!(small < zero));
        assert!(!(small <= zero));
    }
}

#[cfg(test)]
mod test_ord {
    use super::Q;
    use std::cmp::{max, min};

    // `cmp` is extensively tested in module `test_partial_eq`, hence omitted here

    /// Check whether default implementations `max`, `min`, `clamp`
    /// work properly for small numbers
    #[test]
    fn default_implementations_small() {
        let a: Q = Q::from((10, 3));
        let b: Q = Q::from((42, 4));

        assert_eq!(b, max(a.clone(), b.clone()));
        assert_eq!(a, min(a.clone(), b.clone()));

        assert_eq!(a, Q::ZERO.clamp(a.clone(), b.clone()));
        assert_eq!(a, a.clone().clamp(Q::ZERO, b.clone()));
        assert_eq!(a, b.clone().clamp(Q::ZERO, a.clone()));
    }

    /// Check whether default implementations `max`, `min`, `clamp`
    /// work properly for large numbers
    #[test]
    fn default_implementations_large() {
        let a: Q = Q::from(i64::MAX);
        let b: Q = Q::from(u64::MAX);

        assert_eq!(b, max(a.clone(), b.clone()));
        assert_eq!(a, min(a.clone(), b.clone()));

        assert_eq!(a, Q::ZERO.clamp(a.clone(), b.clone()));
        assert_eq!(a, a.clone().clamp(Q::ZERO, b.clone()));
        assert_eq!(a, b.clone().clamp(Q::ZERO, a.clone()));
    }
}
