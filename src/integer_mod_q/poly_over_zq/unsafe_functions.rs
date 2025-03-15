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
use crate::macros::unsafe_passthrough::{unsafe_getter, unsafe_getter_indirect};
use flint_sys::{fmpz_mod::fmpz_mod_ctx, fmpz_mod_poly::fmpz_mod_poly_struct};

unsafe_getter!(PolyOverZq, poly, fmpz_mod_poly_struct);
unsafe_getter_indirect!(PolyOverZq, modulus, get_fmpz_mod_ctx, fmpz_mod_ctx);

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
