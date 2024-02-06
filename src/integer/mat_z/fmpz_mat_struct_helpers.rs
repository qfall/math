// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains helpful functions on [`fmpz_mat_struct`].

use super::{MatZ, MatZSubmatrix};
use crate::traits::AsMatZ;
use flint_sys::fmpz_mat::fmpz_mat_struct;

unsafe impl AsMatZ for MatZ {
    fn get_fmpz_mat_struct_ref(&self) -> &fmpz_mat_struct {
        &self.matrix
    }
}

unsafe impl AsMatZ for &MatZ {
    fn get_fmpz_mat_struct_ref(&self) -> &fmpz_mat_struct {
        &self.matrix
    }
}

unsafe impl<'a> AsMatZ for MatZSubmatrix<'a> {
    fn get_fmpz_mat_struct_ref(&self) -> &fmpz_mat_struct {
        &self.window
    }
}

unsafe impl<'a> AsMatZ for &MatZSubmatrix<'a> {
    fn get_fmpz_mat_struct_ref(&self) -> &fmpz_mat_struct {
        &self.window
    }
}
