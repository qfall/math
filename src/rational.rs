// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the type [`Q`] for rationals with arbitrary length and
//! constructions over it.
//! Each struct provides examples regarding usage.
//! In general you can mix [`Q`]'s with any type of rust integer, whenever the
//! corresponding method takes as input integers of type [`Into<Q>`],
//! e.g. the standard rust integers or tuples of standard rust integers.

mod mat_q;
mod poly_over_q;
mod q;

pub use mat_q::MatQ;
pub use poly_over_q::PolyOverQ;
pub use q::Q;
