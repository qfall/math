// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to compare [`MatPolyOverZ`] with other values.
//! This uses the traits from [`std::cmp`].

use super::MatPolyOverZ;
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_equal;

impl PartialEq for MatPolyOverZ {
    /// Checks if two matrices over [`PolyOverZ`](crate::integer::PolyOverZ) are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    /// let mat_a = "[[0, 1  17, 2  24 42],[2  24 42, 2  24 42, 2  24 42]]";
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str(mat_a).unwrap();
    /// let mat_b = "[[1  17, 1  17, 2  24 42],[2  24 42, 2  24 42, 2  24 42]]";
    /// let b: MatPolyOverZ = MatPolyOverZ::from_str(mat_b).unwrap();
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (MatPolyOverZ::eq(&a, &b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { 1 == fmpz_poly_mat_equal(&self.matrix, &other.matrix) }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for MatPolyOverZ {}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {
    // Test case structure:
    // 1. Different ways to use equal and not equal.
    // 2. Test different combinations of equal and not equal with different
    //    parameter length combinations.
    //    Not equal test are inverted equal tests.

    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Demonstrate the different ways to use equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn equal_call_methods() {
        let mat_a = "[[2  24 42],[2  24 42]]";
        let mat_b = "[[2  24 42],[2  24 42]]";

        let one_1 = MatPolyOverZ::from_str(mat_a).unwrap();
        let one_2 = MatPolyOverZ::from_str(mat_b).unwrap();

        assert!(one_1 == one_2);
        assert!(&one_1 == &one_2);
        assert!(one_1.eq(&one_2));
        assert!(MatPolyOverZ::eq(&one_1, &one_2));
        assert_eq!(one_1, one_2);
    }

    /// Demonstrate the different ways to use not equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn not_equal_call_methods() {
        let mat_a = "[[2  24 42],[2  24 42]]";
        let mat_b = "[[2  24 42],[3  24 42 17]]";

        let one = MatPolyOverZ::from_str(mat_a).unwrap();
        let two = MatPolyOverZ::from_str(mat_b).unwrap();

        assert!(one != two);
        assert!(&one != &two);
        assert!(one.ne(&two));
        assert!(MatPolyOverZ::ne(&one, &two));
        assert_ne!(one, two);
    }

    /// Test equal with small positive and negative constant polynomials as an entry.
    #[test]
    fn equal_small() {
        let mat_small_1 = "[[1  10],[3  24 42 17]]";
        let mat_small_2 = "[[1  10],[3  24 42 17]]";
        let mat_negative = "[[1  -10],[3  24 42 17]]";

        let small_1 = MatPolyOverZ::from_str(mat_small_1).unwrap();
        let small_2 = MatPolyOverZ::from_str(mat_small_2).unwrap();
        let negative = MatPolyOverZ::from_str(mat_negative).unwrap();

        assert!(small_1 == small_2);
        assert!(small_2 == small_1);
        assert!(small_1 == small_1);
        assert!(!(small_1 == negative));
        assert!(!(negative == small_1));
    }

    /// Test not equal with small positive and negative constant polynomials.
    #[test]
    fn not_equal_small() {
        let mat_small_1 = "[[1  10],[3  24 42 17]]";
        let mat_small_2 = "[[1  10],[3  24 42 17]]";
        let mat_negative = "[[1  -10],[3  24 42 17]]";

        let small_1 = MatPolyOverZ::from_str(mat_small_1).unwrap();
        let small_2 = MatPolyOverZ::from_str(mat_small_2).unwrap();
        let negative = MatPolyOverZ::from_str(mat_negative).unwrap();

        assert!(!(small_1 != small_2));
        assert!(!(small_2 != small_1));
        assert!(!(small_1 != small_1));
        assert!(small_1 != negative);
        assert!(negative != small_1);
    }

    /// Test equal with a large coefficient of [`PolyOverZ`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn equal_large() {
        let max_str = format!("[[1  {}],[2  17 42]]", u64::MAX);
        let min_str = format!("[[1  {}],[2  17 42]]", i64::MIN);

        let max_1 = MatPolyOverZ::from_str(&max_str).unwrap();
        let max_2 = MatPolyOverZ::from_str(&max_str).unwrap();
        let min = MatPolyOverZ::from_str(&min_str).unwrap();

        assert!(max_1 == max_2);
        assert!(max_2 == max_1);
        assert!(max_1 == max_1);
        assert!(min == min);
        assert!(!(max_1 == min));
        assert!(!(min == max_1));
    }

    /// Test not equal with a large coefficient of [`PolyOverZ`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn not_equal_large() {
        let max_str = format!("[[1  {}],[2  17 42]]", u64::MAX);
        let min_str = format!("[[1  {}],[2  17 42]]", i64::MIN);

        let max_1 = MatPolyOverZ::from_str(&max_str).unwrap();
        let max_2 = MatPolyOverZ::from_str(&max_str).unwrap();
        let min = MatPolyOverZ::from_str(&min_str).unwrap();

        assert!(!(max_1 != max_2));
        assert!(!(max_2 != max_1));
        assert!(!(max_1 != max_1));
        assert!(!(min != min));
        assert!(max_1 != min);
        assert!(min != max_1);
    }

    /// Test equal with a large coefficient of [`PolyOverZ`] (uses FLINT's pointer representation)
    /// and small coefficient of [`PolyOverZ`] (no pointer representation).
    #[test]
    fn equal_large_small() {
        let max_str = format!("[[1  {}],[2  17 42]]", u64::MAX);
        let min_str = format!("[[1  {}],[2  17 42]]", i64::MIN);

        let max = MatPolyOverZ::from_str(&min_str).unwrap();
        let min = MatPolyOverZ::from_str(&max_str).unwrap();

        let small_positive = MatPolyOverZ::from_str("[[1  1],[2  17 42]]").unwrap();
        let small_negative = MatPolyOverZ::from_str("[[1  -1],[2  17 42]]").unwrap();

        assert!(!(max == small_negative));
        assert!(!(small_negative == max));
        assert!(!(max == small_positive));
        assert!(!(small_positive == max));

        assert!(!(min == small_negative));
        assert!(!(small_negative == min));
        assert!(!(min == small_positive));
        assert!(!(small_positive == min));
    }

    /// Test not equal with a large coefficient of [`PolyOverZ`] (uses FLINT's pointer representation)
    /// and small coefficient of [`PolyOverZ`] (no pointer representation).
    #[test]
    fn not_equal_large_small() {
        let max_str = format!("[[1  {}],[2  17 42]]", u64::MAX);
        let min_str = format!("[[1  {}],[2  17 42]]", i64::MIN);

        let max = MatPolyOverZ::from_str(&min_str).unwrap();
        let min = MatPolyOverZ::from_str(&max_str).unwrap();

        let small_positive = MatPolyOverZ::from_str("[[1  1],[2  17 42]]").unwrap();
        let small_negative = MatPolyOverZ::from_str("[[1  -1],[2  17 42]]").unwrap();

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
