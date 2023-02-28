//! Implementations to compare [`Z`] with other values.
//! This uses the traits from [`std::cmp`].

use super::Z;

use flint_sys::fmpz::fmpz_equal;

impl PartialEq for Z {
    /// Checks if two integers are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - other: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Example
    /// ```rust
    /// use math::integer::Z;
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

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {
    // Test case structure:
    // 1. Different ways to use equal and not equal.
    // 2. Test different combinations of equal and not equal with different
    //    parameter length combinations.
    //    Not equal test are inverted equal tests.

    use super::Z;

    // Demonstrate the different ways to use equal.
    // We assume that they behave the same in the other tests.
    #[test]
    fn equal_call_methods() {
        let one_1 = Z::from(1);
        let one_2 = Z::from(1);

        assert!(one_1 == one_2);
        assert!(&one_1 == &one_2);
        assert!(one_1.eq(&one_2));
        assert!(Z::eq(&one_1, &one_2));
        assert_eq!(one_1, one_2);
    }

    // Demonstrate the different ways to use not equal.
    // We assume that they behave the same in the other tests.
    #[test]
    fn not_equal_call_methods() {
        let one = Z::from(1);
        let two = Z::from(2);

        assert!(one != two);
        assert!(&one != &two);
        assert!(one.ne(&two));
        assert!(Z::ne(&one, &two));
        assert_ne!(one, two);
    }

    // Test equal with small positive and negative numbers.
    #[test]
    fn equal_small() {
        let small_1 = Z::from(10);
        let small_2 = Z::from(10);
        let negative = Z::from(-1);

        assert!(small_1 == small_2);
        assert!(small_2 == small_1);
        assert!(small_1 == small_1);
        assert!(!(small_1 == negative));
        assert!(!(negative == small_1));
    }

    // Test not equal with small positive and negative numbers.
    #[test]
    fn not_equal_small() {
        let small_1 = Z::from(10);
        let small_2 = Z::from(10);
        let negative = Z::from(-1);

        assert!(!(small_1 != small_2));
        assert!(!(small_2 != small_1));
        assert!(!(small_1 != small_1));
        assert!(small_1 != negative);
        assert!(negative != small_1);
    }

    // Test equal with a large [`Z`]
    // (uses FLINT's pointer representation)
    #[test]
    fn equal_large() {
        let max_1 = Z::from(u64::MAX);
        let max_2 = Z::from(u64::MAX);
        let min = Z::from(i64::MIN);

        assert!(max_1 == max_2);
        assert!(max_2 == max_1);
        assert!(max_1 == max_1);
        assert!(min == min);
        assert!(!(max_1 == min));
        assert!(!(min == max_1));
    }

    // Test not equal with a large [`Z`]
    // (uses FLINT's pointer representation)
    #[test]
    fn not_equal_large() {
        let max_1 = Z::from(u64::MAX);
        let max_2 = Z::from(u64::MAX);
        let min = Z::from(i64::MIN);

        assert!(!(max_1 != max_2));
        assert!(!(max_2 != max_1));
        assert!(!(max_1 != max_1));
        assert!(!(min != min));
        assert!(max_1 != min);
        assert!(min != max_1);
    }

    // Test equal with a large [`Z`] (uses FLINT's pointer representation)
    // and small [`Z`] (no pointer representation).
    #[test]
    fn equal_large_small() {
        let max = Z::from(u64::MAX);
        let small_positive = Z::from(1);
        let small_negative = Z::from(-1);
        let min = Z::from(i64::MIN);

        assert!(!(max == small_negative));
        assert!(!(small_negative == max));
        assert!(!(max == small_positive));
        assert!(!(small_positive == max));

        assert!(!(min == small_negative));
        assert!(!(small_negative == min));
        assert!(!(min == small_positive));
        assert!(!(small_positive == min));
    }

    // Test not equal with a large [`Z`] (uses FLINT's pointer representation)
    // and small [`Z`] (no pointer representation).
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
