// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Common functions useful across several datatypes and crates.
//!
//! This can include functions to pre-process inputs
//! and similar tasks.

pub(crate) mod dimensions;
mod factorization;
pub mod index;
pub(crate) mod parse;
pub mod reduce;
pub mod sample;

pub use factorization::Factorization;
