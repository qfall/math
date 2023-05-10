// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get content of a
//! [`ModulusPolynomialRingZq].

use crate::integer_mod_q::{Modulus, ModulusPolynomialRingZq};
use flint_sys::{fmpz_mod::fmpz_mod_ctx_init, fq::fq_ctx_struct};
use std::{mem::MaybeUninit, rc::Rc};

impl ModulusPolynomialRingZq {
    /// Returns the [`fq_ctx_struct`] of a modulus and is only used internally.
    pub(crate) fn get_fq_ctx_struct(&self) -> &fq_ctx_struct {
        self.modulus.as_ref()
    }

    /// Returns a the prime q as a [`Modulus`]
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{ModulusPolynomialRingZq, Modulus};
    /// use std::str::FromStr;
    ///
    /// let modulus_ring = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    ///
    /// let modulus = modulus_ring.get_q();
    ///
    /// # let cmp_modulus = Modulus::try_from(&17.into()).unwrap();
    /// # assert_eq!(cmp_modulus, modulus);
    /// ```
    pub fn get_q(&self) -> Modulus {
        let mut ctx = MaybeUninit::uninit();
        unsafe {
            fmpz_mod_ctx_init(ctx.as_mut_ptr(), &self.get_fq_ctx_struct().ctxp[0].n[0]);
            Modulus {
                modulus: Rc::new(ctx.assume_init()),
            }
        }
    }
}

#[cfg(test)]
mod test_get_q {
    use crate::integer_mod_q::{Modulus, ModulusPolynomialRingZq};
    use std::str::FromStr;

    /// ensure that the same modulus is correctly returned for a large modulus
    #[test]
    fn correct_large() {
        let modulus_ring =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX - 58))
                .unwrap();

        let modulus = modulus_ring.get_q();

        let cmp_modulus = Modulus::try_from(&(u64::MAX - 58).into()).unwrap();
        assert_eq!(cmp_modulus, modulus);
    }
}
