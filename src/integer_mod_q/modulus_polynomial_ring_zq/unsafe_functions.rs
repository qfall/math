// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::ModulusPolynomialRingZq;
use crate::macros::unsafe_passthrough::unsafe_getter_mod;
use flint_sys::fq::fq_ctx_struct;

unsafe_getter_mod!(ModulusPolynomialRingZq, modulus, fq_ctx_struct);

#[cfg(test)]
mod test_get_fq_ctx_struct {
    use super::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// Checks availability of the getter for [`ModulusPolynomialRingZq::modulus`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 7").unwrap();
        let cmp_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 5").unwrap();

        let mut fmpz_mod = unsafe { modulus.get_fq_ctx_struct() };

        fmpz_mod.ctxp[0].n[0].0 = 5;

        assert_eq!(cmp_mod, modulus);
    }
}
