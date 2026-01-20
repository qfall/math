// Copyright © 2023 Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! `qFALL` is a prototyping library for lattice-based cryptography.
//! `qFALL-math` yields the mathematical foundation by providing an easy to use, high-level API based on [FLINT](https://flintlib.org/)
//! as well as several additional features often used in lattice-based cryptography.
//! At a high level, it provides the following classes of datatypes:
//! - Integer-based types such as [`Z`](integer::Z), [`MatZ`](integer::MatZ), [`PolyOverZ`](integer::PolyOverZ), [`MatPolyOverZ`](integer::MatPolyOverZ),
//! - Residue Classes over Integers such as [`Zq`](integer_mod_q::Zq), [`MatZq`](integer_mod_q::MatZq), [`PolyOverZq`](integer_mod_q::PolyOverZq), [`PolynomialRingZq`](integer_mod_q::PolynomialRingZq), [`MatPolynomialRingZq`](integer_mod_q::MatPolynomialRingZq), [`NTTPolynomialRingZq`](integer_mod_q::NTTPolynomialRingZq), [`MatNTTPolynomialRingZq`](integer_mod_q::MatNTTPolynomialRingZq),
//! - Rationals such as [Q](rational::Q), [`MatQ`](rational::MatQ), [`PolyOverQ`](rational::PolyOverQ).
//!
//! The `qFALL` project contains two more crates called [`qFALL-tools`](https://crates.io/crates/qfall-tools)
//! and [`qFALL-schemes`](https://crates.io/crates/qfall-schemes) to support prototyping.
//! - Find further information on [our website](https://qfall.github.io/).
//! - We recommend [our tutorial](https://qfall.github.io/book) to start working with qFALL.
//!
//! ## Quick Example
//! ```
//! use qfall_math::{integer_mod_q::MatZq, integer::MatZ};
//!
//! let (n, m, q) = (256, 1024, 3329);
//! let (center, sigma) = (0.0, 8.0);
//!
//! let mat_a = MatZq::sample_uniform(n, m, q);
//! let vec_s = MatZ::sample_uniform(n, 1, 0, 2).unwrap();
//! let vec_e = MatZ::sample_discrete_gauss(m, 1, center, sigma).unwrap();
//!
//! // SIS-Instance: t = A * e mod q
//! let vec_t = &mat_a * &vec_e;
//!
//! // LWE-Instance: b^T = s^T * A + e^T mod q
//! let vec_b = vec_s.transpose() * mat_a + vec_e.transpose();
//! ```

pub mod error;
pub mod integer;
pub mod integer_mod_q;
pub mod rational;
pub mod traits;
pub mod utils;

mod macros;
