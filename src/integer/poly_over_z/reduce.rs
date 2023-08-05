// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module allows to simulate functionality of the polynomial ring `Z[X]/f(x)`
//! by reducing a [`PolyOverZ`] by a [`PolyOverZ`] that
//! has a leading coefficient of `1`.

use super::{fmpz_poly_helpers::reduce_fmpz_poly_by_poly_over_z, PolyOverZ};

impl PolyOverZ {
    /// Reduces a polynomial by a polynomial `modulus`.
    /// The modulus must have a leading coefficient of `1`, else the function will panic.
    ///
    /// Parameters:
    /// - `modulus`: Specifies the polynomial by which `self` is reduced
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mut a = PolyOverZ::from_str("4  0 0 2 3").unwrap();
    /// let modulus = PolyOverZ::from_str("3  0 1 1").unwrap();
    ///
    /// a.reduce_by_poly(&modulus);
    ///
    /// assert_eq!(PolyOverZ::from_str("2  0 1").unwrap(), a);
    /// ```
    ///
    /// # Panics ...
    /// - if the modulus does not have a leading coefficient of `1`.
    pub fn reduce_by_poly(&mut self, modulus: &PolyOverZ) {
        unsafe { reduce_fmpz_poly_by_poly_over_z(&mut self.poly, modulus) }
    }
}

#[cfg(test)]
mod test_reduce_by_poly {
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Ensures that the reduction works properly for a fixed polynomial that has to be
    /// reduce or more than one coefficient.
    #[test]
    fn reduce_more_than_once() {
        let mut a = PolyOverZ::from_str("4  0 1 2 3").unwrap();
        let modulus = PolyOverZ::from_str("3  0 1 1").unwrap();

        a.reduce_by_poly(&modulus);

        assert_eq!(PolyOverZ::from_str("2  0 2").unwrap(), a);
    }

    /// Ensures that the function panics, if the leading coefficient is not `1`.
    #[test]
    #[should_panic]
    fn no_leading_zero() {
        let mut a = PolyOverZ::from_str("3  1 2 3").unwrap();
        let modulus = PolyOverZ::from_str("2  1 2").unwrap();

        a.reduce_by_poly(&modulus);
    }

    /// Ensures that large coefficients are reduced properly.
    #[test]
    fn large_coefficients() {
        let mut a = PolyOverZ::from_str(&format!("3  1 -{} -1", u64::MAX)).unwrap();
        let modulus = PolyOverZ::from_str(&format!("2  {} 1", u64::MAX)).unwrap();

        a.reduce_by_poly(&modulus);

        assert_eq!(PolyOverZ::from(1), a);
    }
}
