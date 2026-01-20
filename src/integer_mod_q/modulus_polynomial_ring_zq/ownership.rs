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
            ntt_basis: Rc::clone(&self.ntt_basis),
            non_zero: self.non_zero.clone(),
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
}

/// Test that the [`Drop`] trait is correctly implemented.
#[cfg(test)]
mod test_drop {
    use super::ModulusPolynomialRingZq;
    use std::{rc::Rc, str::FromStr};

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
}
