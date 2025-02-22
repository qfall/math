// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::MatPolyOverZ;
use crate::macros::unsafe_passthrough::unsafe_getter;
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_struct;

unsafe_getter!(MatPolyOverZ, matrix, fmpz_poly_mat_struct);

#[cfg(test)]
mod test_get_matrix {
    use super::MatPolyOverZ;
    use crate::{integer::PolyOverZ, traits::GetEntry};
    use flint_sys::{fmpz_poly::fmpz_poly_set, fmpz_poly_mat::fmpz_poly_mat_entry};
    use std::str::FromStr;

    /// Checks availability of the getter for [`MatPolyOverZ::matrix`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut mat = MatPolyOverZ::from_str("[[1  1]]").unwrap();
        let mut poly = PolyOverZ::from(2);

        let mut fmpz_poly_mat = unsafe { mat.get_matrix() };

        unsafe {
            let entry = fmpz_poly_mat_entry(fmpz_poly_mat, 0, 0);
            fmpz_poly_set(entry, poly.get_poly())
        };

        assert_eq!(poly, mat.get_entry(0, 0).unwrap());
    }
}
