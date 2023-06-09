// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to check certain properties of [`PolyOverZq`]
//! This includes checks such as reducibility.

use super::PolyOverZq;
use flint_sys::fmpz_mod_poly_factor::fmpz_mod_poly_is_irreducible;

impl PolyOverZq {
    /// Checks if a [`PolyOverZq`] is irreducible.
    ///
    /// Returns true if the polynomial is irreducible and true otherwise
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly_irr = PolyOverZq::from_str("2  1 1 mod 17").unwrap();
    /// // returns true, since X + 1 is irreducible
    /// assert!(poly_irr.is_irreducible())
    /// ```
    pub fn is_irreducible(&self) -> bool {
        1 == unsafe {
            fmpz_mod_poly_is_irreducible(&self.poly, self.modulus.get_fmpz_mod_ctx_struct())
        }
    }
}

#[cfg(test)]
mod test_is_irreducible {
    use crate::integer_mod_q::PolyOverZq;
    use std::str::FromStr;

    /// Ensure that a irreducible [`PolyOverZq`] returns `true`
    #[test]
    fn poly_is_irreducible() {
        // 9X^2 + 12X + 10 is irreducible over Z17
        let poly_irr = PolyOverZq::from_str("3  10 12 9 mod 17").unwrap();
        assert!(poly_irr.is_irreducible())
    }

    /// Ensure that a reducible [`PolyOverZq`] returns `false`
    #[test]
    fn poly_is_reducible() {
        let poly_irr = PolyOverZq::from_str("3  1 2 1 mod 17").unwrap();
        assert!(!poly_irr.is_irreducible())
    }
}
