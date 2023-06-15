// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`Modulus`].

use super::Modulus;
use flint_sys::fmpz_mod::fmpz_mod_ctx_struct;

impl Modulus {
    /// Returns the [`fmpz_mod_ctx_struct`] of a modulus and is only used internally.
    pub(crate) fn get_fmpz_mod_ctx_struct(&self) -> &fmpz_mod_ctx_struct {
        self.modulus.as_ref()
    }
}
