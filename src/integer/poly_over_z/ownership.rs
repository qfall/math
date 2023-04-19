// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations of functions
//! important for ownership such as the [`Clone`] and [`Drop`] trait.
//!
//! The explicit functions contain the documentation.

use super::PolyOverZ;
use flint_sys::fmpz_poly::{fmpz_poly_clear, fmpz_poly_set};

impl Clone for PolyOverZ {
    /// Clones the given element and returns a deep clone of the [`PolyOverZ`] element.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a = PolyOverZ::from_str("3  0 1 2").unwrap();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut value = PolyOverZ::default();

        unsafe { fmpz_poly_set(&mut value.poly, &self.poly) }

        value
    }
}

impl Drop for PolyOverZ {
    /// Drops the given [`PolyOverZ`] value and frees the allocated memory.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    /// {
    ///     let a = PolyOverZ::from_str("3  0 1 2").unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a = PolyOverZ::from_str("3  0 1 2").unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        // According to FLINT's documentation:
        // "Clears the given polynomial, releasing any memory used. It must be reinitialized in order to be used again."

        unsafe { fmpz_poly_clear(&mut self.poly) }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// check if a clone of a [`PolyOverZ`] with an entry larger than 64 bits
    /// works
    #[test]
    fn large_entries() {
        let u64_string = u64::MAX.to_string();
        let input = format!("2  {} -{}", u64_string, u64_string);

        let poly_1 = PolyOverZ::from_str(&input).unwrap();
        let poly_2 = poly_1.clone();

        // tests where the first coefficient is stored. Since both are larger than
        // an i64, both should be a pointer and their values should differ
        unsafe {
            assert_ne!((*poly_1.poly.coeffs).0, (*poly_2.poly.coeffs).0);
        }
        assert_eq!(poly_1.to_string(), poly_2.to_string())
    }

    /// check if several instantiations are cloned correctly
    #[test]
    fn small_examples() {
        let pos_1 = PolyOverZ::from_str("2  0 11").unwrap();
        let zero_1 = PolyOverZ::from_str("2  0 -11").unwrap();
        let neg_1 = PolyOverZ::from_str("2  0 1100").unwrap();

        let pos_2 = pos_1.clone();
        let zero_2 = zero_1.clone();
        let neg_2 = neg_1.clone();

        assert_eq!(pos_1.to_string(), pos_2.to_string());
        assert_eq!(zero_1.to_string(), zero_2.to_string());
        assert_eq!(neg_1.to_string(), neg_2.to_string());
    }

    /// check if a cloned value is still alive after the original value ran out of scope
    #[test]
    #[allow(clippy::redundant_clone)]
    fn keep_alive() {
        let a: PolyOverZ;
        {
            let b = PolyOverZ::from_str("2  0 1").unwrap();
            a = b.clone();
        }
        assert_eq!("2  0 1", a.to_string());
    }
}

/// Test that the [`Drop`] trait is correctly implemented.
#[cfg(test)]
mod test_drop {

    use super::PolyOverZ;
    use std::{collections::HashSet, str::FromStr};

    /// Creates and drops a [`PolyOverZ`], and returns the storage points in memory
    fn create_and_drop_poly_over_z() -> i64 {
        let a = PolyOverZ::from_str("2  36893488147419103232 36893488147419103233").unwrap();
        unsafe { *a.poly.coeffs }.0
    }

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let mut set = HashSet::new();

        for _i in 0..5 {
            set.insert(create_and_drop_poly_over_z());
        }

        assert!(set.len() < 5);

        let a = PolyOverZ::from_str("2  36893488147419103232 36893488147419103233").unwrap();
        let storage_point = unsafe { *a.poly.coeffs }.0;

        // memory slots differ due to previously created large integer
        let d = PolyOverZ::from_str("2  36893488147419103232 36893488147419103233").unwrap();
        assert_ne!(storage_point, unsafe { *d.poly.coeffs }.0);
    }
}
