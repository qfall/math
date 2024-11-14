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
use crate::integer::Z;
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
