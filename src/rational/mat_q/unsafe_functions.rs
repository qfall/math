// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::MatQ;
use crate::macros::unsafe_passthrough::unsafe_getter;
use flint_sys::fmpq_mat::fmpq_mat_struct;

unsafe_getter!(MatQ, matrix, fmpq_mat_struct);

#[cfg(test)]
mod test_get_matrix {
    use super::MatQ;
    use crate::{rational::Q, traits::GetEntry};
    use flint_sys::{fmpq::fmpq_set, fmpq_mat::fmpq_mat_entry};
    use std::str::FromStr;

    /// Checks availability of the getter for [`MatQ::matrix`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut mat = MatQ::from_str("[[1]]").unwrap();
        let mut value = Q::from(2);

        let mut fmpq_mat = unsafe { mat.get_fmpq_mat_struct() };

        unsafe {
            let entry = fmpq_mat_entry(fmpq_mat, 0, 0);
            fmpq_set(entry, value.get_fmpq())
        };

        assert_eq!(value, mat.get_entry(0, 0).unwrap());
    }
}
