// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Default value for a [`PolyOverZ`].

use super::PolyOverZ;
use flint_sys::fmpz_poly::fmpz_poly_init;
use std::mem::MaybeUninit;

impl Default for PolyOverZ {
    /// Initializes a [`PolyOverZ`] with the zero polynomial.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    ///
    /// let zero = PolyOverZ::default();
    /// ```
    fn default() -> Self {
        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpz_poly_init(poly.as_mut_ptr());

            Self {
                poly: poly.assume_init(),
            }
        }
    }
}

/// ensure that default initializes an empty polynomial
#[cfg(test)]
mod test_default {
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Check if [`Default`] initializes the zero polynomial appropriately
    #[test]
    fn init_zero() {
        let poly_over_zero = PolyOverZ::default();

        assert_eq!(PolyOverZ::from_str("0").unwrap(), poly_over_zero)
    }
}
