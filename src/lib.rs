// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! # What is qFALL-math?
//! qFall-math is a high level interface to the library [FLINT](https://flintlib.org/).
//! It uses the FFI [flint-sys](https://docs.rs/flint-sys/latest/flint_sys/index.html)
//! to access the functionality of FLINT.
//! qFALL-math provides a memory-safe and easy to use interface that is ideal for
//! prototyping. It supports the basic types with arbitrary precision and length:
//! - Integers which are represented as [Z](integer::Z),
//! - Residue Classes over Integers which are represented as [Zq](integer_mod_q::Zq),
//! - Rationals which are represented as [Q](rational::Q).
//!
//! Each of these types also has a matrix and a polynomial version.
//! Further a polynomial ring is supported with
//! [PolynomialRingZq](integer_mod_q::PolynomialRingZq).
//!
//! qFALL-math is free software: you can redistribute it and/or modify it under
//! the terms of the Mozilla Public License Version 2.0 as published by the
//! Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.
//!
//! ## Tutorial + Website
//! You can find a dedicated [tutorial](https://qfall.github.io/book/index.html) to qFALL-math on our [website](https://qfall.github.io/).
//! The tutorial explains the basic steps starting from installation and
//! continues with basic usage.
//! qFALL-math is co-developed together with qFALL-crypto.
//! qFALL-crypto uses qFALL-math to implement cryptographic primitives and can act
//! as inspiration for prototyping and an intuition on how qFALL-math can be used
//! for prototyping.

pub mod error;
pub mod integer;
pub mod integer_mod_q;
pub mod rational;
pub mod traits;
pub mod utils;

mod macros;
