// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to reduce a [`Z`](crate::integer::Z) with the [`Modulus`](crate::integer_mod_q::Modulus).
//!
//! **For Developers** note: The [`Modulus`](crate::integer_mod_q::Modulus)
//! is not applied automatically, and has to be called in the functions individually.
//! Additionally the comparisons assume that the entries are reduced,
//! hence no reduction is performed in the check.

use super::Zq;
use flint_sys::fmpz_mod::fmpz_mod_set_fmpz;

impl Zq {
    /// This function manually applies the
    /// [`Modulus`](crate::integer_mod_q::Modulus)
    /// to the given [`Z`](crate::integer::Z)
    /// in the [`Zq`].
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer_mod_q::Modulus;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let modulus = Modulus::from(17);
    /// let mut zq = Zq::from((18, &modulus));
    ///
    /// zq.reduce();
    /// ```
    pub(crate) fn reduce(&mut self) {
        unsafe {
            fmpz_mod_set_fmpz(
                &mut self.value.value,
                &self.value.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );
        };
    }
}

#[cfg(test)]
mod test_reduce {
    use crate::{
        integer::Z,
        integer_mod_q::{Modulus, Zq},
    };
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Ensure that large entries are reduced correctly
    #[test]
    fn reduces_large() {
        let modulus = Modulus::from_str(&format!("{}", LARGE_PRIME)).unwrap();
        let value = Z::from_str(&format!("{}", u64::MAX)).unwrap();
        let mut original = Zq { value, modulus };

        let cmp_modulus = Modulus::from_str(&format!("{}", LARGE_PRIME)).unwrap();
        let cmp_value = Z::from(58);

        let cmp = Zq {
            value: cmp_value,
            modulus: cmp_modulus,
        };

        assert_ne!(original, cmp);

        original.reduce();

        assert_eq!(original, cmp);
    }

    /// Ensure that small entries are reduced correctly
    #[test]
    fn reduces_small() {
        let modulus = Modulus::from_str("17").unwrap();
        let value = Z::from(20);
        let mut original = Zq { value, modulus };

        let cmp_modulus = Modulus::from_str("17").unwrap();
        let cmp_value = Z::from(3);

        let cmp = Zq {
            value: cmp_value,
            modulus: cmp_modulus,
        };

        assert_ne!(original, cmp);

        original.reduce();

        assert_eq!(original, cmp);
    }
}
