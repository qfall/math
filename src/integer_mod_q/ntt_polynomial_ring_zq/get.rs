// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`NTTPolynomialRingZq`] matrix.

use crate::integer_mod_q::{ModulusPolynomialRingZq, NTTPolynomialRingZq};

impl NTTPolynomialRingZq {
    /// Returns the modulus of the polynomial in NTT representation as a [`ModulusPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{NTTPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 17").unwrap();
    /// let matrix = NTTPolynomialRingZq::sample_uniform(&modulus);
    ///
    /// let modulus = matrix.get_mod();
    /// ```
    pub fn get_mod(&self) -> ModulusPolynomialRingZq {
        self.modulus.clone()
    }
}
