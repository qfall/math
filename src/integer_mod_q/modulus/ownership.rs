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

use super::Modulus;
use flint_sys::fmpz_mod::fmpz_mod_ctx_clear;
use std::rc::Rc;

impl Clone for Modulus {
    /// Clones the given element and returns another cloned reference
    /// to the [`fmpz_mod_ctx`](flint_sys::fmpz_mod::fmpz_mod_ctx) element.
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let a = Modulus::from_str("3").unwrap();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        Modulus {
            modulus: Rc::clone(&self.modulus),
        }
    }
}

impl Drop for Modulus {
    /// Drops the given reference to the [`fmpz_mod_ctx`](flint_sys::fmpz_mod::fmpz_mod_ctx) element
    /// and frees the allocated memory if no references are left.
    ///
    /// # Examples
    /// ```
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    /// {
    ///     let a = Modulus::from_str("3").unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let a = Modulus::from_str("3").unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        if Rc::strong_count(&self.modulus) <= 1 {
            let mut a = *self.modulus;
            unsafe {
                fmpz_mod_ctx_clear(&mut a);
            }
        }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {

    use super::Modulus;
    use std::{rc::Rc, str::FromStr};

    /// Check if new references/ cloned Moduli's increase the Rc counter
    #[test]
    fn references_increased() {
        let a = Modulus::from_str("3").unwrap();
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
        let a = Modulus::from_str(&"1".repeat(65)).unwrap();

        let b = a.clone();

        assert_eq!(
            &a.get_fmpz_mod_ctx_struct().to_owned().n[0].0,
            &b.get_fmpz_mod_ctx_struct().to_owned().n[0].0
        );
    }
}

#[cfg(test)]
mod test_drop {

    use super::Modulus;
    use std::{collections::HashSet, rc::Rc, str::FromStr};

    /// Check whether references are decreased when dropping instances
    #[test]
    fn references_decreased() {
        let a = Modulus::from_str("3").unwrap();
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

    /// Creates and drops a [`Modulus`] object, and outputs
    /// the storage point in memory of that [`Modulus`]
    fn create_and_drop_modulus() -> i64 {
        let a = Modulus::from_str(&"1".repeat(65)).unwrap();
        a.get_fmpz_mod_ctx_struct().n[0].0
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
