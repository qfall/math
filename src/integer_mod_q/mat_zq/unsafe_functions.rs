// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::MatZq;
use crate::macros::unsafe_passthrough::{
    unsafe_getter, unsafe_getter_indirect, unsafe_setter, unsafe_setter_indirect,
};
use flint_sys::{
    fmpz_mod::fmpz_mod_ctx,
    fmpz_mod_mat::{fmpz_mod_mat_clear, fmpz_mod_mat_struct},
};

unsafe_getter!(MatZq, matrix, fmpz_mod_mat_struct);
unsafe_getter_indirect!(MatZq, modulus, get_fmpz_mod_ctx, fmpz_mod_ctx);

unsafe_setter!(MatZq, matrix, fmpz_mod_mat_struct, fmpz_mod_mat_clear);
unsafe_setter_indirect!(MatZq, modulus, set_fmpz_mod_ctx, fmpz_mod_ctx);

#[cfg(test)]
mod test_get_fmpz_mod_mat_struct {
    use super::MatZq;
    use std::str::FromStr;

    /// Checks availability of the getter for [`MatZq::matrix`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut mat = MatZq::from_str("[[3]] mod 7").unwrap();

        let mut fmpz_mat = unsafe { mat.get_fmpz_mod_mat_struct() };

        fmpz_mat.mod_[0].0 = 5;

        assert_eq!(MatZq::from_str("[[3]] mod 5").unwrap(), mat);
    }
}

#[cfg(test)]
mod test_set_fmpz_mod_mat_struct {
    use super::MatZq;
    use flint_sys::{fmpz::fmpz, fmpz_mod_mat::fmpz_mod_mat_init};
    use std::{mem::MaybeUninit, str::FromStr};

    /// Checks availability of the setter for [`MatZq::matrix`]
    /// and its ability to modify [`MatZq`].
    #[test]
    fn availability_and_modification() {
        let mut mat = MatZq::from_str("[[3]] mod 7").unwrap();
        let mut flint_struct = MaybeUninit::uninit();
        let flint_struct = unsafe {
            fmpz_mod_mat_init(flint_struct.as_mut_ptr(), 1, 1, &fmpz(7));
            flint_struct.assume_init()
        };

        unsafe {
            mat.set_fmpz_mod_mat_struct(flint_struct);
        };

        assert_eq!(MatZq::new(1, 1, 7), mat);
    }
}
