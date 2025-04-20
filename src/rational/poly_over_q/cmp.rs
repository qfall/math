// Copyright © 2023 Marvin Beckmann, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to compare [`PolyOverQ`] with other values.
//! This uses the traits from [`std::cmp`].

use super::PolyOverQ;
use crate::{
    integer::PolyOverZ,
    macros::for_others::implement_trait_reverse,
    rational::Q,
    traits::{CompareBase, GetCoefficient},
};
use flint_sys::fmpq_poly::fmpq_poly_equal;

impl PartialEq for PolyOverQ {
    /// Checks if two polynomials over [`Q`](crate::rational::Q) are equal. Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
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
    /// let compared: bool = (PolyOverQ::eq(&a, &b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { 1 == fmpq_poly_equal(&self.poly, &other.poly) }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for PolyOverQ {}

impl PartialEq<PolyOverZ> for PolyOverQ {
    /// Checks if an integer matrix and a rational matrix are equal. Used by the `==` and `!=` operators.
    /// [`PartialEq`] is also implemented for [`PolyOverZ`] using [`PolyOverQ`].
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    /// let a: PolyOverQ = PolyOverQ::from_str("3  1 2 3").unwrap();
    /// let b: PolyOverZ = PolyOverZ::from_str("3  1 2 3").unwrap();
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
    /// let compared: bool = (PolyOverQ::eq(&a, &b));
    /// # assert!(compared);
    /// let compared: bool = (PolyOverZ::eq(&b, &a));
    /// # assert!(compared);
    /// ```
    fn eq(&self, other: &PolyOverZ) -> bool {
        let degree = self.get_degree();

        if degree != other.get_degree() {
            return false;
        }

        for i in 0..degree + 1 {
            if unsafe { self.get_coeff_unchecked(i) } != unsafe { other.get_coeff_unchecked(i) } {
                return false;
            }
        }

        true
    }
}

implement_trait_reverse!(PartialEq, eq, PolyOverZ, PolyOverQ, bool);

impl CompareBase<PolyOverQ> for PolyOverQ {}
impl CompareBase<PolyOverZ> for PolyOverQ {}
impl<Rational: Into<Q>> CompareBase<Rational> for PolyOverQ {}

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

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq_q_other {
    use super::PolyOverQ;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that the function can be called with several types.
    #[test]
    #[allow(clippy::op_ref)]
    fn availability() {
        let q = PolyOverQ::from_str("4  1 2 3 4").unwrap();
        let z = PolyOverZ::from_str("4  1 2 3 4").unwrap();

        assert!(q == z);
        assert!(z == q);
        assert!(&q == &z);
        assert!(&z == &q);
    }

    /// Ensure that equal values are compared correctly.
    #[test]
    fn equal() {
        let q = PolyOverQ::from_str(&format!("3  1 2 {}", u64::MAX)).unwrap();
        let z_1 = PolyOverZ::from_str(&format!("3  1 2 {}", u64::MAX)).unwrap();
        let z_2 = PolyOverZ::from_str(&format!("4  1 2 {} 0", u64::MAX)).unwrap();

        assert!(q == z_1);
        assert!(q == z_2);
    }

    /// Ensure that unequal polynomials are compared correctly.
    #[test]
    fn unequal() {
        let q = PolyOverQ::from_str(&format!("3  1 2 {}", u64::MAX)).unwrap();
        let z_1 = PolyOverZ::from_str(&format!("3  1 3 {}", u64::MAX)).unwrap();
        let z_2 = PolyOverZ::from_str(&format!("4  1 2 {} 1", u64::MAX)).unwrap();

        assert!(q != z_1);
        assert!(q != z_2);
    }
}

/// Test that the [`CompareBase`] trait uses the default implementation.
#[cfg(test)]
mod test_compare_base {
    use crate::{
        integer::{PolyOverZ, Z},
        rational::{PolyOverQ, Q},
        traits::CompareBase,
    };
    use std::str::FromStr;

    /// Ensures that the [`CompareBase`] trait uses the default implementation
    /// and is available for all types it would be checked against.
    #[test]
    fn availability() {
        let one_1 = PolyOverQ::from_str("3  1/3 1 -7").unwrap();

        assert!(one_1.compare_base(&Q::ONE));
        assert!(one_1.compare_base(&Z::ONE));
        assert!(one_1.compare_base(&PolyOverQ::from(1)));
        assert!(one_1.compare_base(&PolyOverZ::from(1)));
        assert!(one_1.compare_base(&0_i8));
        assert!(one_1.compare_base(&0_i16));
        assert!(one_1.compare_base(&0_i32));
        assert!(one_1.compare_base(&0_i64));
        assert!(one_1.compare_base(&0_u8));
        assert!(one_1.compare_base(&0_u16));
        assert!(one_1.compare_base(&0_u32));
        assert!(one_1.compare_base(&0_u64));
        assert!(one_1.compare_base(&0.5_f32));
        assert!(one_1.compare_base(&0.5_f64));

        assert!(one_1.call_compare_base_error(&PolyOverQ::from(1)).is_none());
        assert!(one_1.call_compare_base_error(&PolyOverZ::from(1)).is_none());
        assert!(one_1.call_compare_base_error(&Z::ONE).is_none());
        assert!(one_1.call_compare_base_error(&Q::ONE).is_none());
        assert!(one_1.call_compare_base_error(&0_i8).is_none());
        assert!(one_1.call_compare_base_error(&0_i16).is_none());
        assert!(one_1.call_compare_base_error(&0_i32).is_none());
        assert!(one_1.call_compare_base_error(&0_i64).is_none());
        assert!(one_1.call_compare_base_error(&0_u8).is_none());
        assert!(one_1.call_compare_base_error(&0_u16).is_none());
        assert!(one_1.call_compare_base_error(&0_u32).is_none());
        assert!(one_1.call_compare_base_error(&0_u64).is_none());
        assert!(one_1.call_compare_base_error(&0.5_f32).is_none());
        assert!(one_1.call_compare_base_error(&0.5_f64).is_none());
    }
}
