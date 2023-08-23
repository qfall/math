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

use super::ModulusPolynomialRingZq;
use flint_sys::fq::fq_ctx_clear;
use std::rc::Rc;

impl Clone for ModulusPolynomialRingZq {
    /// Clones the given element and returns another cloned reference
    /// to the [`fq_ctx_struct`](flint_sys::fq::fq_ctx_struct) element.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// // initialize X^2 + 1 mod 17, i.e. a polynomial with modulus
    /// let a = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    ///
    ///
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        Self {
            modulus: Rc::clone(&self.modulus),
        }
    }
}

impl Drop for ModulusPolynomialRingZq {
    /// Drops the given reference to the [`fq_ctx_struct`](flint_sys::fq::fq_ctx_struct) element
    /// and frees the allocated memory if no references are left.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    /// {
    ///     let a = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let a = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        if Rc::strong_count(&self.modulus) <= 1 {
            let mut a = *self.modulus;
            unsafe {
                fq_ctx_clear(&mut a);
            }
        }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {
    use super::ModulusPolynomialRingZq;
    use std::{rc::Rc, str::FromStr};

    /// Check if new references/ cloned Moduli's increase the Rc counter
    #[test]
    fn references_increased() {
        let a = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        assert_eq!(Rc::strong_count(&a.modulus), 1);

        let b = a.clone();

        assert_eq!(Rc::strong_count(&a.modulus), 2);
        assert_eq!(Rc::strong_count(&b.modulus), 2);

        let c = b.clone();

        assert_eq!(Rc::strong_count(&a.modulus), 3);
        assert_eq!(Rc::strong_count(&b.modulus), 3);
        assert_eq!(Rc::strong_count(&c.modulus), 3);
    }

    /// Check if clone points to same point in memory
    #[test]
    fn same_reference() {
        let a = ModulusPolynomialRingZq::from_str(&format!(
            "3  {} 0 -{} mod {}",
            u64::MAX,
            u64::MAX,
            u64::MAX - 58 // closest prime number smaller than u64, but larger than 2^62
        ))
        .unwrap();

        let b = a.clone();

        assert_eq!(
            unsafe { *a.get_fq_ctx_struct().a }.0,
            unsafe { *b.get_fq_ctx_struct().a }.0,
        );
        assert_eq!(
            a.get_fq_ctx_struct().ctxp[0].n[0].0,
            b.get_fq_ctx_struct().ctxp[0].n[0].0,
        );
        assert_eq!(
            unsafe { *a.get_fq_ctx_struct().modulus[0].coeffs.offset(0) }.0,
            unsafe { *b.get_fq_ctx_struct().modulus[0].coeffs.offset(0) }.0,
        );
    }
}

/// Test that the [`Drop`] trait is correctly implemented.
#[cfg(test)]
mod test_drop {
    use super::ModulusPolynomialRingZq;
    use std::{collections::HashSet, rc::Rc, str::FromStr};

    /// Check whether references are decreased when dropping instances
    #[test]
    fn references_decreased() {
        let a = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        assert_eq!(Rc::strong_count(&a.modulus), 1);

        {
            let b = a.clone();

            assert_eq!(Rc::strong_count(&a.modulus), 2);
            assert_eq!(Rc::strong_count(&b.modulus), 2);
        }

        assert_eq!(Rc::strong_count(&a.modulus), 1);

        let b = a.clone();
        assert_eq!(Rc::strong_count(&a.modulus), 2);
        assert_eq!(Rc::strong_count(&b.modulus), 2);

        let c = b.clone();
        assert_eq!(Rc::strong_count(&a.modulus), 3);
        assert_eq!(Rc::strong_count(&b.modulus), 3);
        assert_eq!(Rc::strong_count(&c.modulus), 3);

        drop(a);
        assert_eq!(Rc::strong_count(&b.modulus), 2);
    }

    /// Creates and drops a [`ModulusPolynomialRingZq`] object, and outputs
    /// the storage point in memory of that [`ModulusPolynomialRingZq`]
    fn create_and_drop_modulus() -> (i64, i64, i64) {
        let a = ModulusPolynomialRingZq::from_str(
            "3  184467440739018 0 -184467440739018 mod 184467440739019",
        )
        .unwrap();
        (
            unsafe { *a.get_fq_ctx_struct().a }.0,
            a.get_fq_ctx_struct().ctxp[0].n[0].0,
            unsafe { *a.get_fq_ctx_struct().modulus[0].coeffs.offset(0) }.0,
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
