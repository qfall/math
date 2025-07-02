// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::MatZ;
use crate::macros::unsafe_passthrough::{unsafe_getter, unsafe_setter};
use flint_sys::fmpz_mat::{fmpz_mat_clear, fmpz_mat_struct};

unsafe_getter!(MatZ, matrix, fmpz_mat_struct);
unsafe_setter!(MatZ, matrix, fmpz_mat_struct, fmpz_mat_clear);

#[cfg(test)]
mod test_get_fmpz_mat_struct {
    use super::MatZ;
    use crate::{integer::Z, traits::MatrixGetEntry};
    use flint_sys::{
        fmpz::{fmpz, fmpz_set},
        fmpz_mat::fmpz_mat_entry,
    };
    use std::str::FromStr;

    /// Checks availability of the getter for [`MatZ::matrix`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut mat = MatZ::from_str("[[1]]").unwrap();

        let mut fmpz_mat = unsafe { mat.get_fmpz_mat_struct() };

        unsafe {
            let entry = fmpz_mat_entry(fmpz_mat, 0, 0);
            fmpz_set(entry, &fmpz(2))
        };

        assert_eq!(Z::from(2), mat.get_entry(0, 0).unwrap());
    }
}

#[cfg(test)]
mod test_set_fmpz_mat_struct {
    use super::MatZ;
    use crate::{integer::Z, traits::MatrixGetEntry};
    use flint_sys::fmpz_mat::fmpz_mat_init;
    use std::{mem::MaybeUninit, str::FromStr};

    /// Checks availability of the setter for [`MatZ::matrix`]
    /// and its ability to modify [`MatZ`].
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut mat = MatZ::from_str("[[1]]").unwrap();
        let mut flint_struct = MaybeUninit::uninit();
        let flint_struct = unsafe {
            fmpz_mat_init(flint_struct.as_mut_ptr(), 1, 1);
            flint_struct.assume_init()
        };

        unsafe { mat.set_fmpz_mat_struct(flint_struct) };

        assert_eq!(Z::from(0), mat.get_entry(0, 0).unwrap());
    }
}
