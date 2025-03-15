// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::Zq;
use crate::macros::unsafe_passthrough::unsafe_getter_indirect;
use flint_sys::{fmpz::fmpz, fmpz_mod::fmpz_mod_ctx};

unsafe_getter_indirect!(Zq, value, get_fmpz, fmpz);
unsafe_getter_indirect!(Zq, modulus, get_fmpz_mod_ctx, fmpz_mod_ctx);
