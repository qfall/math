// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! `Z` is a type for integers with arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use super::Z;
use std::hash::Hash;

impl Hash for Z {
    /// This function uses the hash of [`String`] with the decimal representation of `self`.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let string = self.to_string();
        string.hash(state);
    }
}
