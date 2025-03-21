// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Hash`] trait for [`Z`].

use super::Z;
use std::hash::Hash;

// MODULUS is 2^62 - 57, which is the largest prime below 2^62.
// We choose it prime to reduce the risk of accidentally introducing
// a hash collision by multiplying values by a prime factor of the given modulus.
static MODULUS: i64 = 4611686018427387847;

impl Hash for Z {
    /// Calculates the value of `self` mod 2^62 - 57 and then uses
    /// the inbuilt hash function for [`i64`].
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // We use Hash of i64 instead of String or Vec<u8> as it
        // significantly reduces the runtime of this function.
        let modulo_value = (self % MODULUS).value.0;
        modulo_value.hash(state);
    }
}
