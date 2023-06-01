// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains functions that interact between [`fmpz`] and [`Modulus`].

use super::Modulus;
use crate::traits::AsInteger;
use flint_sys::fmpz::{fmpz, fmpz_init_set};

unsafe impl AsInteger for Modulus {
    /// Documentation at [`AsInteger::into_fmpz`]
    unsafe fn into_fmpz(self) -> fmpz {
        (&self).into_fmpz()
    }

    /// Documentation at [`AsInteger::get_fmpz_ref`]
    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        Some(&self.modulus.n[0])
    }
}

unsafe impl AsInteger for &Modulus {
    /// Documentation at [`AsInteger::into_fmpz`]
    unsafe fn into_fmpz(self) -> fmpz {
        let mut out = fmpz(0);
        fmpz_init_set(&mut out, &self.modulus.n[0]);
        out
    }

    /// Documentation at [`AsInteger::get_fmpz_ref`]
    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        Some(&self.modulus.n[0])
    }
}
