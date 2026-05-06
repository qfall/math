// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to manipulate a [`ModulusPolynomialRingZq`].

use crate::integer_mod_q::{Modulus, ModulusPolynomialRingZq, PolyOverZq};
use std::rc::Rc;

impl ModulusPolynomialRingZq {
    /// Changes the modulus `q` of the given [`ModulusPolynomialRingZq`] to the new modulus `q`
    /// and resets all NTT-related attributes.
    /// It takes the representation of each coefficient in [0, q) as the new
    /// coefficients and reduces them by the new [`Modulus`].
    ///
    /// Parameters:
    /// - `modulus`: the new modulus `q`
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let mut poly = ModulusPolynomialRingZq::from_str("4  5 3 7 1 mod 13").unwrap();
    ///
    /// poly.change_q(5);
    ///
    /// assert_eq!(ModulusPolynomialRingZq::from_str("4  0 3 2 1 mod 5").unwrap(), poly);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    pub fn change_q(&mut self, modulus: impl Into<Modulus>) {
        self.ntt_basis = Rc::new(None);
        self.non_zero = Vec::new();

        let new_poly_zq =
            PolyOverZq::from((self.get_representative_least_nonnegative_residue(), modulus));
        self.modulus = Rc::new(new_poly_zq);
    }
}

#[cfg(test)]
mod test_change_q {
    use super::ModulusPolynomialRingZq;
    use crate::integer_mod_q::Modulus;
    use std::str::FromStr;

    /// Ensures that the modulus is changed correctly.
    #[test]
    fn q_correct() {
        let mut modulus = ModulusPolynomialRingZq::from_str("6  1 2 3 4 5 1 mod 7").unwrap();
        let q = Modulus::from(8);

        modulus.change_q(&q);

        assert_eq!("6  1 2 3 4 5 1 mod 8", modulus.to_string());
    }

    /// Ensures that the modulus is changed correctly, if the modulus is big.
    #[test]
    fn big_q_correct() {
        let mut modulus =
            ModulusPolynomialRingZq::from_str(&format!("6  1 2 3 4 5 1 mod {}", i64::MAX)).unwrap();
        let q = Modulus::from(u64::MAX);

        modulus.change_q(&q);

        assert_eq!(
            format!("6  1 2 3 4 5 1 mod {}", u64::MAX),
            modulus.to_string()
        );
    }

    /// Ensures that the poly is reduced correctly.
    #[test]
    fn reduced_correct() {
        let mut modulus = ModulusPolynomialRingZq::from_str("6  1 2 3 4 5 1 mod 7").unwrap();
        let q = Modulus::from(2);

        modulus.change_q(&q);

        assert_eq!("6  1 0 1 0 1 1 mod 2", modulus.to_string());
    }

    /// Ensures that all NTT-related attributes are reset.
    #[test]
    fn reset_ntt_values() {
        let mut modulus = ModulusPolynomialRingZq::from_str("6  1 2 3 4 5 1 mod 7").unwrap();
        let q = Modulus::from(2);

        modulus.change_q(&q);

        assert!(modulus.non_zero.is_empty());
        assert!(modulus.ntt_basis.is_none());
    }
}
