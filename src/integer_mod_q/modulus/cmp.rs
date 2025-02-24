// Copyright © 2023 Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations of functions
//! important for comparison such as the [`PartialEq`] trait.
//!
//! The explicit functions contain the documentation.

use super::Modulus;
use crate::{
    integer::Z,
    macros::for_others::{implement_for_others, implement_trait_reverse},
};
use flint_sys::fmpz::{fmpz, fmpz_cmp, fmpz_equal};
use std::cmp::Ordering;

impl PartialEq for Modulus {
    /// Compares the two [`fmpz`](flint_sys::fmpz::fmpz) structs hiding behind the
    /// given [`Modulus`] instances to check whether the given [`Modulus`] instances
    /// have the same value.
    ///
    /// Parameters:
    /// - `other`: holds another [`Modulus`] object which `self` is compared to
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let a = Modulus::from(3);
    /// let b = Modulus::from(3);
    /// let c = Modulus::from(4);
    ///
    /// assert_eq!(a, b);
    /// assert_ne!(a, c);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            1 == flint_sys::fmpz::fmpz_equal(
                &self.get_fmpz_mod_ctx_struct().to_owned().n[0],
                &other.get_fmpz_mod_ctx_struct().to_owned().n[0],
            )
        }
    }
}

// With the [`Eq`] trait, `a == a` is always true.
// This is not guaranteed by the [`PartialEq`] trait.
impl Eq for Modulus {}

impl PartialEq<Z> for Modulus {
    /// Checks if an integer and a modulus are equal. Used by the `==` and `!=` operators.
    /// [`PartialEq`] is also implemented for [`Z`] using [`Modulus`].
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns `true` if the elements are equal, otherwise `false`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::Modulus;
    /// let a: Modulus = Modulus::from(42);
    /// let b: Z = Z::from(42);
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
    /// let compared: bool = (Z::eq(&b, &a));
    /// # assert!(compared);
    /// let compared: bool = (Modulus::eq(&a, &b));
    /// # assert!(compared);
    /// ```
    fn eq(&self, other: &Z) -> bool {
        unsafe { 1 == fmpz_equal(&other.value, &self.modulus.n[0]) }
    }
}

implement_trait_reverse!(PartialEq, eq, Z, Modulus, bool);

implement_for_others!(Z, Modulus, PartialEq for fmpz i8 i16 i32 i64 u8 u16 u32 u64);

impl PartialOrd for Modulus {
    /// Compares two [`Modulus`] values. Used by the `<`, `<=`, `>`, and `>=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns the [`Ordering`] of the elements.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Modulus;
    ///
    /// let a: Modulus = Modulus::from(10);
    /// let b: Modulus = Modulus::from(42);
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

impl Ord for Modulus {
    //! Enables the usage of `max`, `min`, and `clamp`.
    //!
    //! # Examples
    //! ```
    //! use qfall_math::integer_mod_q::Modulus;
    //! use std::cmp::{max, min};
    //!
    //! let a: Modulus = Modulus::from(10);
    //! let b: Modulus = Modulus::from(42);
    //!
    //! assert_eq!(b, max(a.clone(), b.clone()));
    //! assert_eq!(a, min(a.clone(), b.clone()));
    //! assert_eq!(a, Modulus::from(2).clamp(a.clone(), b.clone()));
    //! ```

    /// Compares two [`Modulus`] values. Used by the `<`, `<=`, `>`, and `>=` operators.
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns the [`Ordering`] of the elements.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Modulus;
    ///
    /// let a: Modulus = Modulus::from(10);
    /// let b: Modulus = Modulus::from(42);
    ///
    /// assert!(a < b);
    /// assert!(a <= b);
    /// assert!(b > a);
    /// assert!(b >= a);
    /// ```
    fn cmp(&self, other: &Self) -> Ordering {
        let z_1: Z = self.into();
        let z_2: Z = other.into();
        z_1.cmp(&z_2)
    }
}

impl PartialOrd<Z> for Modulus {
    /// Compares a [`Z`] value with a [`Modulus`]. Used by the `<`, `<=`, `>`, and `>=` operators.
    /// [`PartialOrd`] is also implemented for [`Z`] using [`Modulus`].
    ///
    /// Parameters:
    /// - `other`: the other value that is used to compare the elements
    ///
    /// Returns the [`Ordering`] of the elements.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::Modulus;
    ///
    /// let a: Modulus = Modulus::from(10);
    /// let b: Z = Z::from(42);
    ///
    /// assert!(a < b);
    /// assert!(a <= b);
    /// assert!(b > a);
    /// assert!(b >= a);
    /// ```
    fn partial_cmp(&self, other: &Z) -> Option<Ordering> {
        Some(unsafe { fmpz_cmp(&self.modulus.n[0], &other.value).cmp(&0) })
    }
}

implement_for_others!(Z, Modulus, PartialOrd for fmpz i8 i16 i32 i64 u8 u16 u32 u64);

#[cfg(test)]
mod test_eq {
    use super::Modulus;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks whether two equal, large Moduli created with different constructors are equal
    #[test]
    fn equal_large() {
        let a = Modulus::from_str(&"1".repeat(65)).unwrap();
        let b = Modulus::from(&Z::from_str(&"1".repeat(65)).unwrap());
        let a_clone = a.clone();

        assert_eq!(a, b);
        assert_eq!(a, a_clone);
        assert_eq!(b, a_clone);
    }

    /// Checks whether two equal, small Moduli created with different constructors are equal
    #[test]
    fn equal_small() {
        let a = Modulus::from(2);
        let b = Modulus::from(&Z::from(2));
        let b_clone = b.clone();

        assert_eq!(a, b);
        assert_eq!(b, b_clone);
        assert_eq!(a, b_clone);
    }

    /// Checks whether unequal Moduli are unequal
    #[test]
    fn unequal() {
        let one = Modulus::from(3);
        let two = Modulus::from(2);
        let large = Modulus::from_str(&"1".repeat(65)).unwrap();

        assert_ne!(one, two);
        assert_ne!(one, large);
        assert_ne!(two, large);
    }
}

/// Test that the [`PartialEq`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_eq_modulus_other {
    use super::Z;
    use crate::integer_mod_q::Modulus;

    // Ensure that the function can be called with several types
    #[test]
    #[allow(clippy::op_ref)]
    fn availability() {
        let modulus = Modulus::from(2);
        let z = Z::from(2);

        assert!(modulus == z);
        assert!(modulus == z.value);
        assert!(modulus == 2i8);
        assert!(modulus == 2u8);
        assert!(modulus == 2i16);
        assert!(modulus == 2u16);
        assert!(modulus == 2i32);
        assert!(modulus == 2u32);
        assert!(modulus == 2i64);
        assert!(modulus == 2u64);

        assert!(z == modulus);
        assert!(z.value == modulus);
        assert!(2i8 == modulus);
        assert!(2u8 == modulus);
        assert!(2i16 == modulus);
        assert!(2u16 == modulus);
        assert!(2i32 == modulus);
        assert!(2u32 == modulus);
        assert!(2i64 == modulus);
        assert!(2u64 == modulus);

        assert!(&modulus == &z);
        assert!(&z == &modulus);
        assert!(&modulus == &2i8);
        assert!(&2i8 == &modulus);
    }

    // Ensure that large values are compared correctly
    #[test]
    fn equal_large() {
        let modulus = Modulus::from(u64::MAX);
        let z = Z::from(u64::MAX);

        assert!(modulus == z);
        assert!(modulus != z + 1);
    }
}

/// Test the [`PartialOrd`] trait implementation for [`Modulus`]. Only basic tests are
/// performed, since the function is the same as for [`Z`](crate::integer::Z).
#[cfg(test)]
mod test_partial_ord {
    use crate::integer_mod_q::Modulus;

    /// Tests comparisons between [`Modulus`] values.
    #[test]
    fn order_correct() {
        let a = Modulus::from(2);
        let b = Modulus::from(3);

        assert!(a < b);
        assert!(a <= b);
        assert!(a <= a);
        assert!(b > a);
        assert!(b >= a);
        assert!(a >= a);
    }

    /// Tests comparisons between large [`Modulus`] values.
    #[test]
    fn order_large() {
        let a = Modulus::from(i64::MAX);
        let b = Modulus::from(u64::MAX);

        assert!(a < b);
        assert!(a <= b);
        assert!(a <= a);
        assert!(b <= b);
        assert!(b > a);
        assert!(b >= a);
        assert!(a >= a);
        assert!(b >= b);
    }
}

/// Test that the [`PartialOrd`] trait is correctly implemented.
#[cfg(test)]
mod test_partial_ord_modulus_other {
    use super::Modulus;
    use crate::integer::Z;

    // Ensure that the function can be called with several types
    #[test]
    #[allow(clippy::op_ref)]
    fn availability() {
        let modulus = Modulus::from(2);
        let z = Z::from(2);

        assert!(modulus <= z);
        assert!(modulus <= z.value);
        assert!(modulus <= 2i8);
        assert!(modulus <= 2u8);
        assert!(modulus <= 2i16);
        assert!(modulus <= 2u16);
        assert!(modulus <= 2i32);
        assert!(modulus <= 2u32);
        assert!(modulus <= 2i64);
        assert!(modulus <= 2u64);

        assert!(z.value >= modulus);
        assert!(2i8 >= modulus);
        assert!(2u8 >= modulus);
        assert!(2i16 >= modulus);
        assert!(2u16 >= modulus);
        assert!(2i32 >= modulus);
        assert!(2u32 >= modulus);
        assert!(2i64 >= modulus);
        assert!(2u64 >= modulus);

        assert!(&modulus <= &z);
        assert!(&modulus <= &2i8);
        assert!(&2i8 >= &modulus);
    }
}

#[cfg(test)]
mod test_ord {
    use crate::integer_mod_q::Modulus;
    use std::cmp::{max, min};

    /// Tests that are already performed in the [`PartialOrd`] tests and the
    /// implementation of [`Ord`] for [`Z`](crate::integer::Z) are omitted.

    /// Checks whether default implementations `max`, `min`, `clamp` work properly.
    #[test]
    fn default_implementations() {
        let a: Modulus = Modulus::from(10);
        let b: Modulus = Modulus::from(42);

        assert_eq!(b, max(a.clone(), b.clone()));
        assert_eq!(a, min(a.clone(), b.clone()));

        assert_eq!(a, Modulus::from(2).clamp(a.clone(), b.clone()));
        assert_eq!(a, a.clone().clamp(Modulus::from(2), b.clone()));
        assert_eq!(a, b.clamp(Modulus::from(2), a.clone()));
    }
}
