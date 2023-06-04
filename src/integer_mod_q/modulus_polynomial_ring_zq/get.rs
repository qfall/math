// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get content of a [`ModulusPolynomialRingZq].

use crate::integer::Z;

use super::ModulusPolynomialRingZq;
use flint_sys::{fmpz::fmpz_set, fq::fq_ctx_struct};

impl ModulusPolynomialRingZq {
    /// Returns the [`fq_ctx_struct`] of a modulus and is only used internally.
    pub(crate) fn get_fq_ctx_struct(&self) -> &fq_ctx_struct {
        self.modulus.as_ref()
    }

    /// Returns the modulus of the polynomial modulus as a [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly_mod = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let modulus = poly_mod.get_mod();
    /// ```
    pub fn get_mod(&self) -> Z {
        let mut modulus = Z::default();
        unsafe { fmpz_set(&mut modulus.value, &self.get_fq_ctx_struct().ctxp[0].n[0]) };

        modulus
    }
}

#[cfg(test)]
mod test_mod {
    use crate::integer::Z;
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    const BITPRIME64: u64 = u64::MAX - 58;

    /// Ensure that the getter for modulus works correctly.
    #[test]
    fn get_mod() {
        let poly_mod = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();

        assert_eq!(poly_mod.get_mod(), Z::from(17));
    }

    /// Ensure that the getter for modulus works with large numbers.
    #[test]
    fn get_mod_large() {
        let poly_mod =
            ModulusPolynomialRingZq::from_str(&format!("2  100 99 mod {}", BITPRIME64)).unwrap();

        assert_eq!(poly_mod.get_mod(), Z::from(BITPRIME64));
    }
}
