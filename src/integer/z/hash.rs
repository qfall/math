// Copyright © 2023 Niklas Siemer
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

// The modulus is chosen as large as possible, i.e. slighly below 2^62.
// Furthermore, to ensure that multiplicative actions result in changes with
// high probability, optimizing when it is prime, i.e. behaves like a field.
static MODULUS: u64 = 4611686018427387847; // 2^62 - 57 is the largest prime below 2^62

impl Hash for Z {
    /// Ensure that the [`flint_sys::fmpz::fmpz`] value is below the
    /// threshold of being a pointer to the memory using modulus.
    ///
    /// Otherwise, this function uses the hash of [`i64`].
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let modulo_value = self.modulo(MODULUS).value.0;
        modulo_value.hash(state);
    }
}
