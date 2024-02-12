// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the type [`Z`] for integers with arbitrary length and
//! constructions over it.
//! Each struct provides examples regarding usage.
//! In general you can mix [`Z`]'s with any type of rust integer, whenever the
//! corresponding method takes as input integers of type [`Into<Z>`],
//! e.g. the standard rust integers.

mod mat_poly_over_z;
mod mat_z;
mod poly_over_z;
mod z;

pub use mat_poly_over_z::MatPolyOverZ;
pub use mat_z::MatZ;
pub use mat_z::MatZSubmatrix;
pub use poly_over_z::PolyOverZ;
pub(crate) use z::fmpz_helpers;
pub use z::Z;
