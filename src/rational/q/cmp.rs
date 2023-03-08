use flint_sys::fmpq::fmpq_equal;

use super::Q;

impl PartialEq for Q {
    /// Checks if two integers are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - other: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Example
    /// ```rust
    /// use math::rational::Q;
    /// use std::str::FromStr;
    /// let a: Q = Q::from_str("42").unwrap();
    /// let b: Q = Q::from_str("24").unwrap();
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

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {
    /// Test case structure:
    /// 1. Different ways to use equal and not equal.
    /// 2. Test different combinations of equal and not equal with different
    ///    parameter length combinations.
    ///    Not equal test are inverted equal tests.
    use std::str::FromStr;

    use super::Q;

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

    /// Test equal with a large [`Z`]
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

    /// Test not equal with a large [`Z`]
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

    /// Test equal with a large [`Z`] (uses FLINT's pointer representation)
    /// and small [`Z`] (no pointer representation).
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

    /// Test not equal with a large [`Z`] (uses FLINT's pointer representation)
    /// and small [`Z`] (no pointer representation).
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
}
