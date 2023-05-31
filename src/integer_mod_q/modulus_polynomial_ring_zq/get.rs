// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get content of a
//! [`ModulusPolynomialRingZq].

use crate::{integer::Z, integer_mod_q::ModulusPolynomialRingZq};
use flint_sys::{fmpz::fmpz_set, fq::fq_ctx_struct};

impl ModulusPolynomialRingZq {
    /// Returns the [`fq_ctx_struct`] of a modulus and is only used internally.
    pub(crate) fn get_fq_ctx_struct(&self) -> &fq_ctx_struct {
        self.modulus.as_ref()
    }

    /// Returns a the prime q as a [`Modulus`]
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let modulus_ring = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    ///
    /// let modulus = modulus_ring.get_q();
    ///
    /// # let cmp_modulus = Z:from(17);
    /// # assert_eq!(cmp_modulus, modulus);
    /// ```
    pub fn get_q(&self) -> Z {
        let mut out = Z::default();
        unsafe {
            fmpz_set(&mut out.value, &self.get_fq_ctx_struct().ctxp[0].n[0]);
        }
        out
    }
}

#[cfg(test)]
mod test_get_q {
    use crate::{integer::Z, integer_mod_q::ModulusPolynomialRingZq};
    use std::str::FromStr;

    /// ensure that the same modulus is correctly returned for a large modulus
    #[test]
    fn correct_large() {
        let large_prime = u64::MAX - 58;
        let modulus_ring =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", large_prime)).unwrap();

        let modulus = modulus_ring.get_q();

        let cmp_modulus = Z::from(large_prime);
        assert_eq!(cmp_modulus, modulus);
    }
}
