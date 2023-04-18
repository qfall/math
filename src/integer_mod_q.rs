// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the type [`Zq`] for integers with arbitrary length
//! modulus `q` and constructions over it.

mod mat_zq;
mod modulus;
mod modulus_polynomial_ring_zq;
mod poly_over_zq;
mod polynomial_ring_zq;
mod z_q;

pub use mat_zq::MatZq;
pub use modulus::Modulus;
pub use modulus_polynomial_ring_zq::ModulusPolynomialRingZq;
pub use poly_over_zq::PolyOverZq;
pub use polynomial_ring_zq::PolynomialRingZq;
pub(crate) use z_q::fmpz_mod_helpers;
pub use z_q::Zq;
