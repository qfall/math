// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to manipulate a [`Zq`] polynomial.

use crate::integer_mod_q::{Modulus, Zq};

impl Zq {
    /// Changes the modulus of the given [`Zq`] value to the new modulus.
    /// It takes the representation of `self` in [0, q) as the new
    /// value and reduces it by the new modulus.
    ///
    /// Parameters:
    /// - `modulus`: the new modulus of the [`Zq`] value
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{Zq, Modulus};
    /// use std::str::FromStr;
    ///
    /// let mut value = Zq::from_str("2 mod 3").unwrap();
    /// value.change_modulus(2);
    ///
    /// assert_eq!("0 mod 2", value.to_string());
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    pub fn change_modulus(&mut self, modulus: impl Into<Modulus>) {
        self.modulus = modulus.into();
        self.value = self.get_representative_least_nonnegative_residue();
        self.reduce();
    }
}

#[cfg(test)]
mod test_change_modulus {
    use super::Zq;
    use crate::integer_mod_q::Modulus;
    use std::str::FromStr;

    /// Ensures that the modulus is changed correctly.
    #[test]
    fn modulus_correct() {
        let mut matrix = Zq::from_str("6 mod 7").unwrap();
        let modulus = Modulus::from(5);

        matrix.change_modulus(&modulus);

        assert_eq!("1 mod 5", matrix.to_string());
    }

    /// Ensures that the modulus is changed correctly, if the modulus is big.
    #[test]
    fn big_modulus_correct() {
        let mut matrix = Zq::from_str(&format!("6 mod {}", i64::MAX)).unwrap();
        let modulus = Modulus::from(u64::MAX);

        matrix.change_modulus(&modulus);

        assert_eq!(format!("6 mod {}", u64::MAX), matrix.to_string());
    }

    /// Ensures that the matrix is reduced correctly.
    #[test]
    fn reduced_correct() {
        let mut matrix = Zq::from_str("6 mod 7").unwrap();
        let modulus = Modulus::from(2);

        matrix.change_modulus(&modulus);

        assert_eq!("0 mod 2", matrix.to_string());
    }
}
