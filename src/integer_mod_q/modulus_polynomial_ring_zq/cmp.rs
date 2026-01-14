// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to compare [`ModulusPolynomialRingZq`] with other values.
//! This uses the traits from [`std::cmp`].

use super::ModulusPolynomialRingZq;
use crate::{
    integer::Z,
    integer_mod_q::{PolyOverZq, modulus},
    macros::for_others::implement_trait_reverse,
    traits::GetCoefficient,
};
use flint_sys::{fmpz::fmpz_equal, fmpz_mod_poly::fmpz_mod_poly_equal};

impl PartialEq for ModulusPolynomialRingZq {
    /// Checks if two modulus objects of type over [`ModulusPolynomialRingZq`] are equal.
    /// They are considered equal, if their representation as a
    /// [`PolyOverZq`](crate::integer_mod_q::PolyOverZq) match: i.e. the modulus `q`
    /// and the coefficients of the polynomial under modulus `q`.
    /// Used by the `==` and `!=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    /// let a: ModulusPolynomialRingZq = ModulusPolynomialRingZq::from_str("2  24 1 mod 17").unwrap();
    /// let b: ModulusPolynomialRingZq = ModulusPolynomialRingZq::from_str("2  42 1 mod 17").unwrap();
    ///
    /// // These are all equivalent and return false.
    /// let compared: bool = (a == b);
    /// # assert!(!compared);
    /// let compared: bool = (&a == &b);
    /// # assert!(!compared);
    /// let compared: bool = (a.eq(&b));
    /// # assert!(!compared);
    /// let compared: bool = (ModulusPolynomialRingZq::eq(&a, &b));
    /// # assert!(!compared);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.modulus == other.modulus
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for ModulusPolynomialRingZq {}

impl PartialEq<PolyOverZq> for ModulusPolynomialRingZq {
    /// Checks if an integer matrix and a rational matrix are equal. Used by the `==` and `!=` operators.
    /// [`PartialEq`] is also implemented for [`PolyOverZq`] using [`ModulusPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolyOverZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let a: ModulusPolynomialRingZq = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 17").unwrap();
    /// let b: PolyOverZq = PolyOverZq::from_str("3  1 2 3 mod 17").unwrap();
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
    /// let compared: bool = (ModulusPolynomialRingZq::eq(&a, &b));
    /// # assert!(compared);
    /// let compared: bool = (PolyOverZq::eq(&b, &a));
    /// # assert!(compared);
    /// ```
    fn eq(&self, other: &PolyOverZq) -> bool {
        if self.get_q() != other.modulus {
            return false;
        }

        let degree = self.get_degree();
        if degree != other.get_degree() {
            return false;
        }

        for i in 0..degree + 1 {
            if unsafe { GetCoefficient::<Z>::get_coeff_unchecked(self, i) }
                != unsafe { GetCoefficient::<Z>::get_coeff_unchecked(other, i) }
            {
                return false;
            }
        }

        true
    }
}

implement_trait_reverse!(PartialEq, eq, PolyOverZq, ModulusPolynomialRingZq, bool);

/// Test that the [`PartialEq`] trait is correctly implemented.
/// Consider that negative is turned positive due to the modulus being applied.
/// Hence negative/small refers to the instantiation.
#[cfg(test)]
mod test_partial_eq {
    // Test case structure:
    // 1. Different ways to use equal and not equal.
    // 2. Test different combinations of equal and not equal with different
    //    parameter length combinations.
    //    Not equal test are inverted equal tests.

    use super::ModulusPolynomialRingZq;
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Demonstrate the different ways to use equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn equal_call_methods() {
        let one_1 = ModulusPolynomialRingZq::from_str("2  42 -1 mod 17").unwrap();
        let one_2 = ModulusPolynomialRingZq::from_str("2  42 -1 mod 17").unwrap();

        assert!(one_1 == one_2);
        assert!(&one_1 == &one_2);
        assert!(one_1.eq(&one_2));
        assert!(ModulusPolynomialRingZq::eq(&one_1, &one_2));
        assert_eq!(one_1, one_2);
    }

    /// Demonstrate the different ways to use not equal.
    /// We assume that they behave the same in the other tests.
    #[test]
    #[allow(clippy::op_ref)]
    fn not_equal_call_methods_different_num_coeffs() {
        let one = ModulusPolynomialRingZq::from_str("2  42 -1 mod 17").unwrap();
        let two = ModulusPolynomialRingZq::from_str("3  42 -1 1 mod 17").unwrap();

        assert!(one != two);
        assert!(&one != &two);
        assert!(one.ne(&two));
        assert!(ModulusPolynomialRingZq::ne(&one, &two));
        assert_ne!(one, two);
    }

    /// Test equal with small positive and negative constant polynomials.
    #[test]
    fn equal_small() {
        let small_1 = ModulusPolynomialRingZq::from_str("2  1 10 mod 17").unwrap();
        let small_2 = ModulusPolynomialRingZq::from_str("2  1 10 mod 17").unwrap();
        let negative = ModulusPolynomialRingZq::from_str("2  1 -2 mod 17").unwrap();

        assert!(small_1 == small_2);
        assert!(small_2 == small_1);
        assert!(small_1 == small_1);
        assert!(!(small_1 == negative));
        assert!(!(negative == small_1));
    }

    /// Test not equal with small positive and negative constant polynomials.
    #[test]
    fn not_equal_small() {
        let small_1 = ModulusPolynomialRingZq::from_str("2  1 10 mod 17").unwrap();
        let small_2 = ModulusPolynomialRingZq::from_str("2  1 10 mod 17").unwrap();
        let negative = ModulusPolynomialRingZq::from_str("2  1 -1 mod 17").unwrap();

        assert!(!(small_1 != small_2));
        assert!(!(small_2 != small_1));
        assert!(!(small_1 != small_1));
        assert!(small_1 != negative);
        assert!(negative != small_1);
    }

    /// Test equal with a large [`ModulusPolynomialRingZq`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn equal_large() {
        let max_str = format!("2  1 {} mod {LARGE_PRIME}", u64::MAX);
        let min_str = format!("2  1 {} mod {LARGE_PRIME}", i64::MIN);

        let max_1 = ModulusPolynomialRingZq::from_str(&max_str).unwrap();
        let max_2 = ModulusPolynomialRingZq::from_str(&max_str).unwrap();
        let min = ModulusPolynomialRingZq::from_str(&min_str).unwrap();

        assert!(max_1 == max_2);
        assert!(max_2 == max_1);
        assert!(max_1 == max_1);
        assert!(min == min);
        assert!(!(max_1 == min));
        assert!(!(min == max_1));
    }

    /// Test not equal with a large [`ModulusPolynomialRingZq`]
    /// (uses FLINT's pointer representation)
    #[test]
    fn not_equal_large() {
        let max_str = format!("2  1 {} mod {LARGE_PRIME}", u64::MAX);
        let min_str = format!("2  1 {} mod {LARGE_PRIME}", i64::MIN);

        let max_1 = ModulusPolynomialRingZq::from_str(&max_str).unwrap();
        let max_2 = ModulusPolynomialRingZq::from_str(&max_str).unwrap();
        let min = ModulusPolynomialRingZq::from_str(&min_str).unwrap();

        assert!(!(max_1 != max_2));
        assert!(!(max_2 != max_1));
        assert!(!(max_1 != max_1));
        assert!(!(min != min));
        assert!(max_1 != min);
        assert!(min != max_1);
    }

    /// Test equal with a large polynomial with a large [`ModulusPolynomialRingZq`] (uses FLINT's pointer representation)
    /// and small polynomial with a small [`ModulusPolynomialRingZq`] (no pointer representation).
    #[test]
    fn equal_large_small() {
        let max_str = format!("2  1 {} mod {LARGE_PRIME}", u64::MAX);
        let min_str = format!("2  1 {} mod {LARGE_PRIME}", i64::MIN);

        let max = ModulusPolynomialRingZq::from_str(&max_str).unwrap();
        let min = ModulusPolynomialRingZq::from_str(&min_str).unwrap();

        let small_positive = ModulusPolynomialRingZq::from_str("2  1 2 mod 17").unwrap();
        let small_negative = ModulusPolynomialRingZq::from_str("2  1 -2 mod 17").unwrap();

        assert!(!(max == small_negative));
        assert!(!(small_negative == max));
        assert!(!(max == small_positive));
        assert!(!(small_positive == max));

        assert!(!(min == small_negative));
        assert!(!(small_negative == min));
        assert!(!(min == small_positive));
        assert!(!(small_positive == min));
    }

    /// Test not equal with a large [`ModulusPolynomialRingZq`] (uses FLINT's pointer representation)
    /// and small [`ModulusPolynomialRingZq`] (no pointer representation).
    #[test]
    fn not_equal_large_small() {
        let max_str = format!("2  1 {} mod {LARGE_PRIME}", u64::MAX);
        let min_str = format!("2  1 {} mod {LARGE_PRIME}", i64::MIN);

        let max = ModulusPolynomialRingZq::from_str(&max_str).unwrap();
        let min = ModulusPolynomialRingZq::from_str(&min_str).unwrap();

        let small_positive = ModulusPolynomialRingZq::from_str("2  1 2 mod 17").unwrap();
        let small_negative = ModulusPolynomialRingZq::from_str("2  1 -2 mod 17").unwrap();

        assert!(max != small_negative);
        assert!(small_negative != max);
        assert!(max != small_positive);
        assert!(small_positive != max);

        assert!(min != small_negative);
        assert!(small_negative != min);
        assert!(min != small_positive);
        assert!(small_positive != min);
    }

    /// Test not equal for the same polynomial but with a different modulus
    #[test]
    fn different_modulus() {
        let first_str = "2  1 2 mod 17";
        let second_str = "2  1 2 mod 19";

        let first = ModulusPolynomialRingZq::from_str(first_str).unwrap();
        let second = ModulusPolynomialRingZq::from_str(second_str).unwrap();

        assert_ne!(first, second);
    }
}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq_q_other {
    use crate::integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq};
    use std::str::FromStr;

    /// Ensure that the function can be called with several types.
    #[test]
    #[allow(clippy::op_ref)]
    fn availability() {
        let q = ModulusPolynomialRingZq::from_str("4  1 2 3 4 mod 17").unwrap();
        let z = PolyOverZq::from_str("4  1 2 3 4 mod 17").unwrap();

        assert!(q == z);
        assert!(z == q);
        assert!(&q == &z);
        assert!(&z == &q);
    }

    /// Ensure that equal values are compared correctly.
    #[test]
    fn equal() {
        let q = ModulusPolynomialRingZq::from_str(&format!("3  1 2 {} mod {}", i64::MAX, u64::MAX))
            .unwrap();
        let z_1 = PolyOverZq::from_str(&format!("3  1 2 {} mod {}", i64::MAX, u64::MAX)).unwrap();
        let z_2 = PolyOverZq::from_str(&format!("4  1 2 {} 0 mod {}", i64::MAX, u64::MAX)).unwrap();

        assert!(q == z_1);
        assert!(q == z_2);
    }

    /// Ensure that unequal values are compared correctly.
    #[test]
    fn unequal() {
        let q = ModulusPolynomialRingZq::from_str(&format!("3  1 2 {} mod {}", i64::MAX, u64::MAX))
            .unwrap();
        let z_1 = PolyOverZq::from_str(&format!("3  1 3 {} mod {}", i64::MAX, u64::MAX)).unwrap();
        let z_2 = PolyOverZq::from_str(&format!("4  1 2 {} 1 mod {}", i64::MAX, u64::MAX)).unwrap();
        let z_3 =
            PolyOverZq::from_str(&format!("3  1 2 {} mod {}", i64::MAX, u64::MAX - 1)).unwrap();

        assert!(q != z_1);
        assert!(q != z_2);
        assert!(q != z_3);
    }
}
