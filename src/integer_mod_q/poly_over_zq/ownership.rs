// Copyright 2023 Jan Niklas Siemer
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

use super::PolyOverZq;
use flint3_sys::{fmpz_mod_poly_clear, fmpz_mod_poly_set};

impl Clone for PolyOverZq {
    /// Clones the given [`PolyOverZq`] element by returning a deep clone,
    /// storing the actual value separately and including
    /// a reference to the [`Modulus`](crate::integer_mod_q::Modulus) element.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let a = PolyOverZq::from_str("4  0 1 -2 3 mod 13").unwrap();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut out = PolyOverZq::from(&self.modulus);

        unsafe {
            fmpz_mod_poly_set(
                &mut out.poly,
                &self.poly,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };

        out
    }
}

impl Drop for PolyOverZq {
    /// Drops the given memory allocated for the underlying value
    /// and frees the allocated memory of the corresponding
    /// [`Modulus`](crate::integer_mod_q::Modulus) if no other references are left.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    /// {
    ///     let a = PolyOverZq::from_str("4  0 1 -2 3 mod 13").unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let a = PolyOverZq::from_str("4  0 1 -2 3 mod 13").unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        unsafe {
            fmpz_mod_poly_clear(&mut self.poly, self.modulus.get_fmpz_mod_ctx_struct());
        }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {
    use super::PolyOverZq;
    use std::str::FromStr;

    /// Check if clone points to same point in memory
    #[test]
    fn same_reference() {
        let a = PolyOverZq::from_str(&format!("4  {} 1 -2 3 mod {}", i64::MAX, u64::MAX)).unwrap();

        let b = a.clone();

        // check that Modulus isn't stored twice
        assert_eq!(
            a.modulus.get_fmpz_mod_ctx_struct().n[0],
            b.modulus.get_fmpz_mod_ctx_struct().n[0]
        );

        // check that values on heap are stored separately
        assert_ne!(unsafe { *a.poly.coeffs.offset(0) }, unsafe {
            *b.poly.coeffs.offset(0)
        }); // heap
        assert_eq!(unsafe { *a.poly.coeffs.offset(1) }, unsafe {
            *b.poly.coeffs.offset(1)
        }); // stack
        assert_ne!(unsafe { *a.poly.coeffs.offset(2) }, unsafe {
            *b.poly.coeffs.offset(2)
        }); // heap
        assert_eq!(unsafe { *a.poly.coeffs.offset(3) }, unsafe {
            *b.poly.coeffs.offset(3)
        }); // stack

        // check if length of polynomials is equal
        assert_eq!(a.poly.length, b.poly.length);
    }

    /// Ensure that the zero polynomial can be cloned.
    #[test]
    fn zero_polynomial() {
        let a = PolyOverZq::from_str("0 mod 17").unwrap();
        let b = PolyOverZq::from_str("1  17 mod 17").unwrap();

        assert_eq!(a, a.clone());
        assert_eq!(b, b.clone());
        assert_eq!(a.get_mod(), a.clone().get_mod());
    }

    /// Ensure that cloning preserves the value and modulus.
    #[test]
    fn correct_value() {
        let a = PolyOverZq::from_str(&format!("4  {} 1 -2 3 mod {}", i64::MAX, u64::MAX)).unwrap();

        let b = a.clone();

        assert_eq!(a, b);
        assert_eq!(a.get_mod(), b.get_mod());
    }
}

#[cfg(test)]
mod test_drop {
    use super::PolyOverZq;
    use std::{collections::HashSet, str::FromStr};

    /// Creates and drops a [`PolyOverZq`] object, and outputs
    /// the storage point in memory of that [`fmpz_mod_poly`](flint3_sys::fmpz_mod_poly::fmpz_mod_poly_t) struct
    fn create_and_drop_modulus() -> (i64, i64) {
        let a = PolyOverZq::from_str(&format!("2  {} -2 mod {}", i64::MAX, u64::MAX)).unwrap();

        (unsafe { *a.poly.coeffs.offset(0) }, unsafe {
            *a.poly.coeffs.offset(1)
        })
    }

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let mut storage_addresses = HashSet::new();

        for _i in 0..5 {
            let (a, b) = create_and_drop_modulus();
            storage_addresses.insert(a);
            storage_addresses.insert(b);
        }

        assert!(storage_addresses.len() < 10);
    }
}
