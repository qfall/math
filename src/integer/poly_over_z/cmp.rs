// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to compare [`PolyOverZ`] with other values.
//! This uses the traits from [`std::cmp`].

use flint_sys::fmpz_poly::fmpz_poly_equal;

use super::PolyOverZ;

impl PartialEq for PolyOverZ {
    /// Checks if two polynomials over [`Z`](crate::integer::Z) are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    /// let a: PolyOverZ = PolyOverZ::from_str("2  42 1").unwrap();
    /// let b: PolyOverZ = PolyOverZ::from_str("2  24 1").unwrap();
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (PolyOverZ::eq(&a,&b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { 1 == fmpz_poly_equal(&self.poly, &other.poly) }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for PolyOverZ {}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {
    // Test case structure:
    // 1. Different ways to use equal and not equal.
    // 2. Test different combinations of equal and not equal with different
    //    parameter length combinations.
    //    Not equal test are inverted equal tests.

    use super::PolyOverZ;
    use std::str::FromStr;

    /// Demonstrate the different ways to use equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn equal_call_methods() {
        let one_1 = PolyOverZ::from_str("2  24 1").unwrap();
        let one_2 = PolyOverZ::from_str("2  24 1").unwrap();

        assert!(one_1 == one_2);
        assert!(&one_1 == &one_2);
        assert!(one_1.eq(&one_2));
        assert!(PolyOverZ::eq(&one_1, &one_2));
        assert_eq!(one_1, one_2);
    }

    /// Demonstrate the different ways to use not equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn not_equal_call_methods() {
        let one = PolyOverZ::from_str("2  24 1").unwrap();
        let two = PolyOverZ::from_str("3  24 1 1").unwrap();

        assert!(one != two);
        assert!(&one != &two);
        assert!(one.ne(&two));
        assert!(PolyOverZ::ne(&one, &two));
        assert_ne!(one, two);
    }

    /// Test equal with small positive and negative constant polynomials.
    #[test]
    fn equal_small() {
        let small_1 = PolyOverZ::from_str("1  10").unwrap();
        let small_2 = PolyOverZ::from_str("1  10").unwrap();
        let negative = PolyOverZ::from_str("1  -1").unwrap();

        assert!(small_1 == small_2);
        assert!(small_2 == small_1);
        assert!(small_1 == small_1);
        assert!(!(small_1 == negative));
        assert!(!(negative == small_1));
    }

    /// Test not equal with small positive and negative constant polynomials.
    #[test]
    fn not_equal_small() {
        let small_1 = PolyOverZ::from_str("1  10").unwrap();
        let small_2 = PolyOverZ::from_str("1  10").unwrap();
        let negative = PolyOverZ::from_str("1  -1").unwrap();

        assert!(!(small_1 != small_2));
        assert!(!(small_2 != small_1));
        assert!(!(small_1 != small_1));
        assert!(small_1 != negative);
        assert!(negative != small_1);
    }

    /// Test equal with a large [`PolyOverZ`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn equal_large() {
        let max_str = format!("1  {}", u64::MAX);
        let min_str = format!("1  {}", i64::MIN);

        let max_1 = PolyOverZ::from_str(&max_str).unwrap();
        let max_2 = PolyOverZ::from_str(&max_str).unwrap();
        let min = PolyOverZ::from_str(&min_str).unwrap();

        assert!(max_1 == max_2);
        assert!(max_2 == max_1);
        assert!(max_1 == max_1);
        assert!(min == min);
        assert!(!(max_1 == min));
        assert!(!(min == max_1));
    }

    /// Test not equal with a large [`PolyOverZ`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn not_equal_large() {
        let max_str = format!("1  {}", u64::MAX);
        let min_str = format!("1  {}", i64::MIN);

        let max_1 = PolyOverZ::from_str(&max_str).unwrap();
        let max_2 = PolyOverZ::from_str(&max_str).unwrap();
        let min = PolyOverZ::from_str(&min_str).unwrap();

        assert!(!(max_1 != max_2));
        assert!(!(max_2 != max_1));
        assert!(!(max_1 != max_1));
        assert!(!(min != min));
        assert!(max_1 != min);
        assert!(min != max_1);
    }

    /// Test equal with a large [`PolyOverZ`] (uses FLINT's pointer representation)
    /// and small [`PolyOverZ`] (no pointer representation).
    #[test]
    fn equal_large_small() {
        let max_str = format!("1  {}", u64::MAX);
        let min_str = format!("1  {}", i64::MIN);

        let max = PolyOverZ::from_str(&max_str).unwrap();
        let min = PolyOverZ::from_str(&min_str).unwrap();

        let small_positive = PolyOverZ::from_str("1  1").unwrap();
        let small_negative = PolyOverZ::from_str("1  -1").unwrap();

        assert!(!(max == small_negative));
        assert!(!(small_negative == max));
        assert!(!(max == small_positive));
        assert!(!(small_positive == max));

        assert!(!(min == small_negative));
        assert!(!(small_negative == min));
        assert!(!(min == small_positive));
        assert!(!(small_positive == min));
    }

    /// Test not equal with a large [`PolyOverZ`] (uses FLINT's pointer representation)
    /// and small [`PolyOverZ`] (no pointer representation).
    #[test]
    fn not_equal_large_small() {
        let max_str = format!("1  {}", u64::MAX);
        let min_str = format!("1  {}", i64::MIN);

        let max = PolyOverZ::from_str(&max_str).unwrap();
        let min = PolyOverZ::from_str(&min_str).unwrap();

        let small_positive = PolyOverZ::from_str("1  1").unwrap();
        let small_negative = PolyOverZ::from_str("1  -1").unwrap();

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
