// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the type [`Zq`] for integers with arbitrary length
//! modulus `q` and constructions over it.
//! Each struct provides examples regarding usage.
//! In general you can mix [`Zq`]'s with any type of rust integer, whenever the
//! corresponding method takes as input integers of type [`Into<Z>`],
//! e.g. the standard rust integers.
//! The [`Modulus`] is constructed as an explicit struct and can be shared across several
//! [`Zq`], [`MatZq`] and [`PolyOverZq`] instances with efficient memory usage.
//!
//! - \[1\] John D. Dixon.
//!     "Exact Solution of Linear Equations Using P-Adic Expansions"
//!     <https://link.springer.com/article/10.1007/BF01459082>

mod mat_polynomial_ring_zq;
mod mat_zq;
mod modulus;
mod modulus_polynomial_ring_zq;
mod poly_over_zq;
mod polynomial_ring_zq;
mod z_q;

pub use mat_polynomial_ring_zq::MatPolynomialRingZq;
pub use mat_zq::MatZq;
pub use modulus::Modulus;
pub use modulus_polynomial_ring_zq::ModulusPolynomialRingZq;
pub use poly_over_zq::PolyOverZq;
pub use polynomial_ring_zq::PolynomialRingZq;
pub(crate) use z_q::fmpz_mod_helpers;
pub use z_q::Zq;
