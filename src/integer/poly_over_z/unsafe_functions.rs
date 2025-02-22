// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::PolyOverZ;
use crate::macros::unsafe_passthrough::unsafe_getter;
use flint_sys::fmpz_poly::fmpz_poly_struct;

unsafe_getter!(PolyOverZ, poly, fmpz_poly_struct);

#[cfg(test)]
mod test_get_poly {
    use super::PolyOverZ;
    use flint_sys::{fmpz::fmpz, fmpz_poly::fmpz_poly_set_fmpz};

    /// Checks availability of the getter for [`PolyOverZ::poly`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut poly = PolyOverZ::from(1);

        let mut fmpz_poly = unsafe { poly.get_fmpz_poly_struct() };

        unsafe { fmpz_poly_set_fmpz(fmpz_poly, &fmpz(2)) };

        assert_eq!(PolyOverZ::from(2), poly);
    }
}
