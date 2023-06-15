// Copyright © 2023 Niklas Siemer
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

use super::PolyOverQ;
use flint_sys::fmpq_poly::{fmpq_poly_clear, fmpq_poly_init, fmpq_poly_set};
use std::mem::MaybeUninit;

impl Clone for PolyOverQ {
    /// Clones the given [`PolyOverQ`] element by returning a deep clone,
    /// storing two separately stored [fmpz](flint_sys::fmpz::fmpz) values
    /// for `nominator` and `denominator` in memory.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    ///
    /// let a = PolyOverQ::default();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpq_poly_init(poly.as_mut_ptr());
            let mut poly = poly.assume_init();
            fmpq_poly_set(&mut poly, &self.poly);
            Self { poly }
        }
    }
}

impl Drop for PolyOverQ {
    /// Drops the given memory allocated for the underlying value.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// {
    ///     let a = PolyOverQ::default();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    ///
    /// let a = PolyOverQ::default();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        unsafe {
            fmpq_poly_clear(&mut self.poly);
        }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {
    use super::PolyOverQ;
    use std::str::FromStr;

    /// Check if nominators and denominators are equal for small integers
    #[test]
    fn same_reference_small() {
        let a = PolyOverQ::from_str("4  1/1 -1/-2 -2/2 3/-4").unwrap();

        let b = a.clone();

        // check that nominators on stack should are equal,
        // as they directly store the value in the `i64`
        assert_eq!(
            unsafe { *a.poly.coeffs.offset(0) }.0,
            unsafe { *b.poly.coeffs.offset(0) }.0
        ); // stack

        assert_eq!(
            unsafe { *a.poly.coeffs.offset(1) }.0,
            unsafe { *b.poly.coeffs.offset(1) }.0
        ); // stack
        assert_eq!(
            unsafe { *a.poly.coeffs.offset(2) }.0,
            unsafe { *b.poly.coeffs.offset(2) }.0
        ); // stack
        assert_eq!(
            unsafe { *a.poly.coeffs.offset(3) }.0,
            unsafe { *b.poly.coeffs.offset(3) }.0
        ); // stack

        // denominator should be kept on stack (since common denominator is 8)
        assert_eq!(a.poly.den[0].0, b.poly.den[0].0); // stack

        // check that length is equal
        assert_eq!(a.poly.length, b.poly.length);
    }

    /// Check if clone points to same point in memory for large nominators and denominators
    #[test]
    fn same_reference_large() {
        let a =
            PolyOverQ::from_str(&format!("4  {}/1 1/{} -2/2 3/-4", i64::MAX, i64::MIN)).unwrap();

        let b = a.clone();

        // check that nominators on heap are stored separately
        assert_ne!(
            unsafe { *a.poly.coeffs.offset(0) }.0,
            unsafe { *b.poly.coeffs.offset(0) }.0
        ); // heap
        assert_eq!(
            unsafe { *a.poly.coeffs.offset(1) }.0,
            unsafe { *b.poly.coeffs.offset(1) }.0
        ); // stack
        assert_ne!(
            unsafe { *a.poly.coeffs.offset(2) }.0,
            unsafe { *b.poly.coeffs.offset(2) }.0
        ); // heap
        assert_ne!(
            unsafe { *a.poly.coeffs.offset(3) }.0,
            unsafe { *b.poly.coeffs.offset(3) }.0
        ); // heap

        // denominator should be kept on heap (as common denominator is at least i64::MIN)
        // hence stored separately
        assert_ne!(a.poly.den[0].0, b.poly.den[0].0); // heap

        // check that length is equal
        assert_eq!(a.poly.length, b.poly.length);
    }
}

#[cfg(test)]
mod test_drop {
    use super::PolyOverQ;
    use std::{collections::HashSet, str::FromStr};

    /// Creates and drops a [`PolyOverQ`] object, and outputs
    /// the storage point in memory of that [`fmpq_poly`](flint_sys::fmpz_mod_poly::fmpz_mod_poly_t) struct
    fn create_and_drop_modulus() -> (i64, i64, i64) {
        let a = PolyOverQ::from_str(&format!("2  {}/1 -2/-3", i64::MAX)).unwrap();

        (
            unsafe { *a.poly.coeffs.offset(0) }.0,
            unsafe { *a.poly.coeffs.offset(1) }.0,
            a.poly.den[0].0,
        )
    }

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let mut storage_addresses = HashSet::new();

        for _i in 0..5 {
            storage_addresses.insert(create_and_drop_modulus());
        }

        assert!(storage_addresses.len() < 5);
    }
}
