// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.
use super::PolynomialRingZq;
use crate::macros::unsafe_passthrough::{unsafe_getter_indirect, unsafe_setter_indirect};
use flint_sys::fmpz_poly::fmpz_poly_struct;

unsafe_getter_indirect!(
    PolynomialRingZq,
    poly,
    get_fmpz_poly_struct,
    fmpz_poly_struct
);

unsafe_setter_indirect!(
    PolynomialRingZq,
    poly,
    set_fmpz_poly_struct,
    fmpz_poly_struct
);
