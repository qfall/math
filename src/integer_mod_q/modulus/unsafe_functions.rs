// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::Modulus;
use crate::macros::unsafe_passthrough::unsafe_getter_mod;
use flint_sys::fmpz_mod::fmpz_mod_ctx;

unsafe_getter_mod!(Modulus, modulus, fmpz_mod_ctx);

#[cfg(test)]
mod test_get_fmpz_mod_ctx {
    use super::Modulus;

    /// Checks availability of the getter for [`Modulus::modulus`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut modulus = Modulus::from(3);

        let mut fmpz_mod = unsafe { modulus.get_fmpz_mod_ctx() };

        fmpz_mod.n[0].0 = 2;

        assert_eq!(Modulus::from(2), modulus);
    }
}
