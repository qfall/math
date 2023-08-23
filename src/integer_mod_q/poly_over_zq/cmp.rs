// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to compare [`PolyOverZq`] with other values.
//! This uses the traits from [`std::cmp`].

use super::PolyOverZq;
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_equal;

impl PartialEq for PolyOverZq {
    /// Checks if two polynomials over [`Zq`](crate::integer_mod_q::Zq) are equal.
    /// Two [`PolyOverZq`] are considered equal if their modulus is equal and
    /// all coefficients are equal modulus `q`.
    /// Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    /// let a: PolyOverZq = PolyOverZq::from_str("2  42 1 mod 17").unwrap();
    /// let b: PolyOverZq = PolyOverZq::from_str("2  24 1 mod 19").unwrap();
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (PolyOverZq::eq(&a, &b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            self.modulus == other.modulus
                && 1 == fmpz_mod_poly_equal(
                    &self.poly,
                    &other.poly,
                    self.modulus.get_fmpz_mod_ctx_struct(),
                )
        }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for PolyOverZq {}

/// Test that the [`PartialEq`] trait is correctly implemented.
/// Consider that negative is turned positive due to the modulus being applied.
/// Hence negative refers to the instantiation.
#[cfg(test)]
mod test_partial_eq {
    // Test case structure:
    // 1. Different ways to use equal and not equal.
    // 2. Test different combinations of equal and not equal with different
    //    parameter length combinations.
    //    Not equal test are inverted equal tests.

    use super::PolyOverZq;
    use std::str::FromStr;

    /// Demonstrate the different ways to use equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn equal_call_methods() {
        let one_1 = PolyOverZq::from_str("2  24 1 mod 17").unwrap();
        let one_2 = PolyOverZq::from_str("2  24 1 mod 17").unwrap();

        assert!(one_1 == one_2);
        assert!(&one_1 == &one_2);
        assert!(one_1.eq(&one_2));
        assert!(PolyOverZq::eq(&one_1, &one_2));
        assert_eq!(one_1, one_2);
    }

    /// Demonstrate the different ways to use not equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn not_equal_call_methods_different_num_coeffs() {
        let one = PolyOverZq::from_str("2  24 1 mod 17").unwrap();
        let two = PolyOverZq::from_str("3  24 1 1 mod 17").unwrap();

        assert!(one != two);
        assert!(&one != &two);
        assert!(one.ne(&two));
        assert!(PolyOverZq::ne(&one, &two));
        assert_ne!(one, two);
    }

    /// Test equal with small positive and negative constant polynomials.
    #[test]
    fn equal_small() {
        let small_1 = PolyOverZq::from_str("1  10 mod 17").unwrap();
        let small_2 = PolyOverZq::from_str("1  10 mod 17").unwrap();
        let negative = PolyOverZq::from_str("1  -1 mod 17").unwrap();

        assert!(small_1 == small_2);
        assert!(small_2 == small_1);
        assert!(small_1 == small_1);
        assert!(!(small_1 == negative));
        assert!(!(negative == small_1));
    }

    /// Test not equal with small positive and negative constant polynomials.
    #[test]
    fn not_equal_small() {
        let small_1 = PolyOverZq::from_str("1  10 mod 17").unwrap();
        let small_2 = PolyOverZq::from_str("1  10 mod 17").unwrap();
        let negative = PolyOverZq::from_str("1  -1 mod 17").unwrap();

        assert!(!(small_1 != small_2));
        assert!(!(small_2 != small_1));
        assert!(!(small_1 != small_1));
        assert!(small_1 != negative);
        assert!(negative != small_1);
    }

    /// Test equal with a large [`PolyOverZq`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn equal_large() {
        let max_str = format!("1  {} mod 1{}", u64::MAX, u64::MAX);
        let min_str = format!("1  {} mod 1{}", i64::MIN, u64::MAX);

        let max_1 = PolyOverZq::from_str(&max_str).unwrap();
        let max_2 = PolyOverZq::from_str(&max_str).unwrap();
        let min = PolyOverZq::from_str(&min_str).unwrap();

        assert!(max_1 == max_2);
        assert!(max_2 == max_1);
        assert!(max_1 == max_1);
        assert!(min == min);
        assert!(!(max_1 == min));
        assert!(!(min == max_1));
    }

    /// Test not equal with a large [`PolyOverZq`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn not_equal_large() {
        let max_str = format!("1  {} mod 1{}", u64::MAX, u64::MAX);
        let min_str = format!("1  {} mod 1{}", i64::MIN, u64::MAX);

        let max_1 = PolyOverZq::from_str(&max_str).unwrap();
        let max_2 = PolyOverZq::from_str(&max_str).unwrap();
        let min = PolyOverZq::from_str(&min_str).unwrap();

        assert!(!(max_1 != max_2));
        assert!(!(max_2 != max_1));
        assert!(!(max_1 != max_1));
        assert!(!(min != min));
        assert!(max_1 != min);
        assert!(min != max_1);
    }

    /// Test equal with a large [`PolyOverZq`] (uses FLINT's pointer representation)
    /// and small [`PolyOverZq`] (no pointer representation).
    #[test]
    fn equal_large_small() {
        let max_str = format!("1  {} mod 1{}", u64::MAX, u64::MAX);
        let min_str = format!("1  {} mod 1{}", i64::MIN, u64::MAX);

        let max = PolyOverZq::from_str(&max_str).unwrap();
        let min = PolyOverZq::from_str(&min_str).unwrap();

        let small_positive = PolyOverZq::from_str(&format!("1  1 mod {}", u64::MAX)).unwrap();
        let small_negative = PolyOverZq::from_str(&format!("1  -1 mod {}", u64::MAX)).unwrap();

        assert!(!(max == small_negative));
        assert!(!(small_negative == max));
        assert!(!(max == small_positive));
        assert!(!(small_positive == max));

        assert!(!(min == small_negative));
        assert!(!(small_negative == min));
        assert!(!(min == small_positive));
        assert!(!(small_positive == min));
    }

    /// Test not equal with a large [`PolyOverZq`] (uses FLINT's pointer representation)
    /// and small [`PolyOverZq`] (no pointer representation).
    #[test]
    fn not_equal_large_small() {
        let max_str = format!("1  {} mod 1{}", u64::MAX, u64::MAX);
        let min_str = format!("1  {} mod 1{}", i64::MIN, u64::MAX);

        let max = PolyOverZq::from_str(&max_str).unwrap();
        let min = PolyOverZq::from_str(&min_str).unwrap();

        let small_positive = PolyOverZq::from_str(&format!("1  1 mod {}", u64::MAX)).unwrap();
        let small_negative = PolyOverZq::from_str(&format!("1  -1 mod {}", u64::MAX)).unwrap();

        assert!(max != small_negative);
        assert!(small_negative != max);
        assert!(max != small_positive);
        assert!(small_positive != max);

        assert!(min != small_negative);
        assert!(small_negative != min);
        assert!(min != small_positive);
        assert!(small_positive != min);
    }

    /// Ensure that polynomials with different [`Modulus`](crate::integer_mod_q::Modulus)
    #[test]
    #[allow(clippy::op_ref)]
    fn different_modulus_err() {
        let str_1 = format!("1  {} mod 1{}", u64::MAX, u64::MAX);
        let str_2 = format!("1  {} mod 1{}", u64::MAX, u64::MAX - 1);
        let poly_1 = PolyOverZq::from_str(&str_1).unwrap();
        let poly_2 = PolyOverZq::from_str(&str_2).unwrap();

        assert_ne!(poly_1, poly_2);
        assert!(poly_1 != poly_2);
        assert!(&poly_1 != &poly_2);
        assert!(poly_1.ne(&poly_2));
        assert!(PolyOverZq::ne(&poly_1, &poly_2));
    }

    /// Ensure equal for polynomials of a high degree
    #[test]
    fn equal_high_degree() {
        let str_1 = format!("7  {} 72 48 2028 23 392 1 mod 1{}", u64::MAX, u64::MAX);
        let str_2 = format!("7  {} 72 48 2028 23 392 1 mod 1{}", u64::MAX, u64::MAX);
        let poly_1 = PolyOverZq::from_str(&str_1).unwrap();
        let poly_2 = PolyOverZq::from_str(&str_2).unwrap();

        assert_eq!(poly_1, poly_2);
        assert!(poly_1 == poly_2);
    }
}
