// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the type [`Z`] for integers with arbitrary length and
//! constructions over it.

mod mat_poly_over_z;
mod mat_z;
mod poly_over_z;
mod z;

pub use mat_poly_over_z::MatPolyOverZ;
pub use mat_z::MatZ;
pub use poly_over_z::PolyOverZ;
pub use z::Z;
