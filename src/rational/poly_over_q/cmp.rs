//! Implementations to compare [`PolyOverQ`] with other values.
//! This uses the traits from [`std::cmp`].

use flint_sys::fmpq_poly::fmpq_poly_equal;

use super::PolyOverQ;

impl PartialEq for PolyOverQ {
    /// Checks if two polynomials over [`Q`](crate::rational::Q) are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Example
    /// ```
    /// use math::rational::PolyOverQ;
    /// use std::str::FromStr;
    /// let a: PolyOverQ = PolyOverQ::from_str("2  42/24 1").unwrap();
    /// let b: PolyOverQ = PolyOverQ::from_str("2  24/42 1").unwrap();
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (PolyOverQ::eq(&a,&b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { 1 == fmpq_poly_equal(&self.poly, &other.poly) }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for PolyOverQ {}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq {
    // Test case structure:
    // 1. Different ways to use equal and not equal.
    // 2. Test different combinations of equal and not equal with different
    //    parameter length combinations.
    //    Not equal test are inverted equal tests.

    use super::PolyOverQ;
    use std::str::FromStr;

    /// Demonstrate the different ways to use equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn equal_call_methods() {
        let one_1 = PolyOverQ::from_str("2  24/42 1").unwrap();
        let one_2 = PolyOverQ::from_str("2  24/42 1").unwrap();

        assert!(one_1 == one_2);
        assert!(&one_1 == &one_2);
        assert!(one_1.eq(&one_2));
        assert!(PolyOverQ::eq(&one_1, &one_2));
        assert_eq!(one_1, one_2);
    }

    /// Demonstrate the different ways to use not equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn not_equal_call_methods() {
        let one = PolyOverQ::from_str("2  24/42 1").unwrap();
        let two = PolyOverQ::from_str("3  24/42 1 1").unwrap();

        assert!(one != two);
        assert!(&one != &two);
        assert!(one.ne(&two));
        assert!(PolyOverQ::ne(&one, &two));
        assert_ne!(one, two);
    }

    /// Test equal with small positive and negative constant polynomials.
    #[test]
    fn equal_small() {
        let small_1 = PolyOverQ::from_str("1  10/3").unwrap();
        let small_2 = PolyOverQ::from_str("1  10/3").unwrap();
        let negative = PolyOverQ::from_str("1  -1/5").unwrap();

        assert!(small_1 == small_2);
        assert!(small_2 == small_1);
        assert!(small_1 == small_1);
        assert!(!(small_1 == negative));
        assert!(!(negative == small_1));
    }

    /// Test not equal with small positive and negative constant polynomials.
    #[test]
    fn not_equal_small() {
        let small_1 = PolyOverQ::from_str("1  10/3").unwrap();
        let small_2 = PolyOverQ::from_str("1  10/3").unwrap();
        let negative = PolyOverQ::from_str("1  -1/5").unwrap();

        assert!(!(small_1 != small_2));
        assert!(!(small_2 != small_1));
        assert!(!(small_1 != small_1));
        assert!(small_1 != negative);
        assert!(negative != small_1);
    }

    /// Test equal with a large [`PolyOverQ`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn equal_large() {
        let max_str = format!("1  {}/{}", u64::MAX, 3);
        let min_str = format!("1  {}/{}", i64::MIN, 4);

        let max_1 = PolyOverQ::from_str(&max_str).unwrap();
        let max_2 = PolyOverQ::from_str(&max_str).unwrap();
        let min = PolyOverQ::from_str(&min_str).unwrap();

        assert!(max_1 == max_2);
        assert!(max_2 == max_1);
        assert!(max_1 == max_1);
        assert!(min == min);
        assert!(!(max_1 == min));
        assert!(!(min == max_1));
    }

    /// Test not equal with a large [`PolyOverQ`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn not_equal_large() {
        let max_str = format!("1  {}/{}", u64::MAX, 3);
        let min_str = format!("1  {}/{}", i64::MIN, 4);

        let max_1 = PolyOverQ::from_str(&max_str).unwrap();
        let max_2 = PolyOverQ::from_str(&max_str).unwrap();
        let min = PolyOverQ::from_str(&min_str).unwrap();

        assert!(!(max_1 != max_2));
        assert!(!(max_2 != max_1));
        assert!(!(max_1 != max_1));
        assert!(!(min != min));
        assert!(max_1 != min);
        assert!(min != max_1);
    }

    /// Test equal with a large [`PolyOverQ`] (uses FLINT's pointer representation)
    /// and small [`PolyOverQ`] (no pointer representation).
    #[test]
    fn equal_large_small() {
        let max_str = format!("1  {}/{}", u64::MAX, 3);
        let min_str = format!("1  {}/{}", i64::MIN, 4);

        let max = PolyOverQ::from_str(&max_str).unwrap();
        let min = PolyOverQ::from_str(&min_str).unwrap();

        let small_positive = PolyOverQ::from_str("1  1/7").unwrap();
        let small_negative = PolyOverQ::from_str("1  -1/7").unwrap();

        assert!(!(max == small_negative));
        assert!(!(small_negative == max));
        assert!(!(max == small_positive));
        assert!(!(small_positive == max));

        assert!(!(min == small_negative));
        assert!(!(small_negative == min));
        assert!(!(min == small_positive));
        assert!(!(small_positive == min));
    }

    /// Test not equal with a large [`PolyOverQ`] (uses FLINT's pointer representation)
    /// and small [`PolyOverQ`] (no pointer representation).
    #[test]
    fn not_equal_large_small() {
        let max_str = format!("1  {}/{}", u64::MAX, 3);
        let min_str = format!("1  {}/{}", i64::MIN, 4);

        let max = PolyOverQ::from_str(&max_str).unwrap();
        let min = PolyOverQ::from_str(&min_str).unwrap();

        let small_positive = PolyOverQ::from_str("1  1").unwrap();
        let small_negative = PolyOverQ::from_str("1  -1").unwrap();

        assert!(max != small_negative);
        assert!(small_negative != max);
        assert!(max != small_positive);
        assert!(small_positive != max);

        assert!(min != small_negative);
        assert!(small_negative != min);
        assert!(min != small_positive);
        assert!(small_positive != min);
    }

    /// Test not equal with a large [`PolyOverQ`] (uses FLINT's pointer representation)
    /// i.e. a large denominator and a large nominator
    #[test]
    #[allow(clippy::op_ref)]
    fn large_nom_large_denom() {
        let max_str = format!("1  {}/3{}", u64::MAX, u64::MAX);
        let min_str = format!("1  {}/4{}", i64::MIN, u64::MAX);

        let one = PolyOverQ::from_str(&min_str).unwrap();
        let two = PolyOverQ::from_str(&max_str).unwrap();

        assert!(one != two);
        assert!(&one != &two);
        assert!(one.ne(&two));
        assert!(PolyOverQ::ne(&one, &two));
        assert_ne!(one, two);
    }
}
