// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.
use super::MatPolynomialRingZq;
use crate::macros::unsafe_passthrough::{unsafe_getter_indirect, unsafe_setter_indirect};
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_struct;

unsafe_getter_indirect!(
    MatPolynomialRingZq,
    matrix,
    get_fmpz_poly_mat_struct,
    fmpz_poly_mat_struct
);

unsafe_setter_indirect!(
    MatPolynomialRingZq,
    matrix,
    set_fmpz_poly_mat_struct,
    fmpz_poly_mat_struct
);
