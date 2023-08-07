// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains common functions that are used by several crates.
//!
//! This can include functions to pre-process inputs, find size of matrices
//! and similar tasks.

pub(crate) mod collective_evaluation;
pub(crate) mod dimensions;
mod factorization;
pub mod index;
pub(crate) mod parse;
pub(crate) mod sample;

pub use factorization::Factorization;
