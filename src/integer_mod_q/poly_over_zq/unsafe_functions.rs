// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::PolyOverZq;
use crate::macros::unsafe_passthrough::{
    unsafe_getter, unsafe_getter_indirect, unsafe_setter_indirect,
};
use flint_sys::{
    fmpz_mod::fmpz_mod_ctx,
    fmpz_mod_poly::{fmpz_mod_poly_clear, fmpz_mod_poly_struct},
};

unsafe_getter!(PolyOverZq, poly, fmpz_mod_poly_struct);
unsafe_getter_indirect!(PolyOverZq, modulus, get_fmpz_mod_ctx, fmpz_mod_ctx);

impl PolyOverZq {
    /// Sets the field `poly` of type [`PolyOverZq`] to `flint_struct`.
    ///
    /// Parameters:
    /// - `flint_struct`: value to set the attribute to
    ///
    /// This function is a passthrough to enable users of this library to use [`flint_sys`]
    /// and with that [FLINT](https://flintlib.org/) functions that might not be covered in our library yet.
    /// If this is the case, please consider contributing to this open-source project
    /// by opening a Pull Request at [qfall_math](https://github.com/qfall/math)
    /// to provide this feature in the future.
    ///
    /// # Safety
    /// Ensure that the old struct does not share any memory with any other structs
    /// that might be used in the future. The memory of the old struct is freed
    /// using this function.
    ///
    /// Any [`flint_sys`] struct and function is part of a FFI to the C-library `FLINT`.
    /// As `FLINT` is a C-library, it does not provide all memory safety features
    /// that Rust and our Wrapper provide.
    /// Thus, using functions of [`flint_sys`] can introduce memory leaks.
    pub unsafe fn set_fmpz_mod_poly_struct(&mut self, flint_struct: fmpz_mod_poly_struct) {
        fmpz_mod_poly_clear(&mut self.poly, self.modulus.get_fmpz_mod_ctx_struct());

        self.poly = flint_struct;
    }
}
unsafe_setter_indirect!(PolyOverZq, modulus, set_fmpz_mod_ctx, fmpz_mod_ctx);

#[cfg(test)]
mod test_get_fmpz_mod_poly_struct {
    use super::PolyOverZq;
    use flint_sys::fmpz_mod_poly::fmpz_mod_poly_set_ui;

    /// Checks availability of the getter for [`PolyOverZq::poly`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut poly = PolyOverZq::from((3, 7));

        let mut fmpz_poly = unsafe { poly.get_fmpz_mod_poly_struct() };

        unsafe { fmpz_mod_poly_set_ui(fmpz_poly, 5, poly.get_fmpz_mod_ctx()) };

        assert_eq!(PolyOverZq::from((5, 7)), poly);
    }
}

#[cfg(test)]
mod test_set_fmpz_mod_poly_struct {
    use super::PolyOverZq;
    use crate::integer_mod_q::Modulus;
    use flint_sys::fmpz_mod_poly::fmpz_mod_poly_init;
    use std::mem::MaybeUninit;

    /// Checks availability of the setter for [`PolyOverZq::poly`]
    /// and its ability to modify [`PolyOverZq`].
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut poly = PolyOverZq::from((3, 7));

        let modulus = Modulus::from(7);
        let mut flint_struct = MaybeUninit::uninit();
        let flint_struct = unsafe {
            fmpz_mod_poly_init(flint_struct.as_mut_ptr(), modulus.get_fmpz_mod_ctx_struct());
            flint_struct.assume_init()
        };

        unsafe { poly.set_fmpz_mod_poly_struct(flint_struct) };

        assert_eq!(PolyOverZq::from((0, 7)), poly);
    }
}
