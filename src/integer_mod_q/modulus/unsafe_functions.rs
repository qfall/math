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
use flint_sys::fmpz_mod::{fmpz_mod_ctx, fmpz_mod_ctx_clear};

unsafe_getter_mod!(Modulus, modulus, fmpz_mod_ctx);

impl Modulus {
    /// Sets a mutable reference to the field `modulus` of type [`Modulus`] to a given `fmpz_mod_ctx`.
    ///
    /// Parameters:
    /// - `flint_struct`: value to set the attribute to
    ///
    /// **WARNING:** The set struct is part of [`flint_sys`].
    /// Any changes to this object are unsafe and may introduce memory leaks.
    /// Please be aware that most moduli are shared across multiple instances and all
    /// modifications of this struct will affect any other instance with a reference to this object.
    ///
    /// This function is a passthrough to enable users of this library to use [`flint_sys`]
    /// and with that [FLINT](https://flintlib.org/) functions that might not be covered in our library yet.
    /// If this is the case, please consider contributing to this open-source project
    /// by opening a Pull Request at [qfall_math](https://github.com/qfall/math)
    /// to provide this feature in the future.
    ///
    /// # Safety
    /// Ensure that the old `modulus` does not share any memory with any moduli
    /// that might be used in the future. The memory of the old `modulus` is freed
    /// using this function.
    ///
    /// Any [`flint_sys`] struct and function is part of a FFI to the C-library `FLINT`.
    /// As `FLINT` is a C-library, it does not provide all memory safety features
    /// that Rust and our Wrapper provide.
    /// Thus, using functions of [`flint_sys`] can introduce memory leaks.
    pub unsafe fn set_fmpz_mod_ctx(&mut self, flint_struct: fmpz_mod_ctx) {
        let modulus = std::rc::Rc::<fmpz_mod_ctx>::get_mut(&mut self.modulus).unwrap();

        // free memory of old modulus before new values of modulus are copied
        unsafe { fmpz_mod_ctx_clear(modulus) };

        modulus.add_fxn = flint_struct.add_fxn;
        modulus.mod_ = flint_struct.mod_;
        modulus.mul_fxn = flint_struct.mul_fxn;
        modulus.n = flint_struct.n;
        modulus.n_limbs = flint_struct.n_limbs;
        modulus.ninv_limbs = flint_struct.ninv_limbs;
        modulus.sub_fxn = flint_struct.sub_fxn;
    }
}

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

#[cfg(test)]
mod test_set_fmpz_mod_ctx {
    use super::Modulus;
    use flint_sys::{fmpz::fmpz, fmpz_mod::fmpz_mod_ctx_init};
    use std::mem::MaybeUninit;

    /// Checks availability of the setter for [`Modulus::modulus`]
    /// and its ability to modify [`Modulus`].
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut modulus = Modulus::from(3);

        let mut flint_struct = MaybeUninit::uninit();
        let mut flint_struct = unsafe {
            fmpz_mod_ctx_init(flint_struct.as_mut_ptr(), &fmpz(2));
            flint_struct.assume_init()
        };

        unsafe { modulus.set_fmpz_mod_ctx(flint_struct) };

        assert_eq!(Modulus::from(2), modulus);
    }
}
