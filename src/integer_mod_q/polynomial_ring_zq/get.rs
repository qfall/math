// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get content of a
//! [`PolynomialRingZq].

use super::PolynomialRingZq;
use crate::{integer::PolyOverZ, integer_mod_q::ModulusPolynomialRingZq};

impl PolynomialRingZq {
    /// Returns the modulus object of the [`PolynomialRingZq`] element.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let poly_ring = PolynomialRingZq::from((&poly, &modulus));
    ///
    /// let poly_ring_mod = poly_ring.get_mod();
    ///
    /// assert_eq!(modulus, poly_ring_mod);
    /// ```
    pub fn get_mod(&self) -> ModulusPolynomialRingZq {
        self.modulus.clone()
    }

    /// Returns the representative polynomial of the [`PolynomialRingZq`] element.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let poly_ring = PolynomialRingZq::from((&poly, &modulus));
    ///
    /// let poly_z = poly_ring.get_poly();
    ///
    /// let cmp_poly = PolyOverZ::from_str("3  15 0 1").unwrap();
    /// assert_eq!(cmp_poly, poly_z);
    /// ```
    pub fn get_poly(&self) -> PolyOverZ {
        self.poly.clone()
    }
}

#[cfg(test)]
mod test_get_mod {
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
    };
    use std::str::FromStr;

    /// ensure that the large modulus polynomial is returned correctly
    #[test]
    fn large_positive() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX - 58))
                .unwrap();
        let poly = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        assert_eq!(modulus, poly_ring.get_mod());
    }
}

#[cfg(test)]
mod test_get_value {
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
    };
    use std::str::FromStr;

    /// ensure that the getter returns for large entries
    #[test]
    fn large_positive() {
        let large_prime = u64::MAX - 58;
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {large_prime}")).unwrap();
        let poly = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let poly_z = poly_ring.get_poly();

        let cmp_poly = PolyOverZ::from_str(&format!("3  {} 0 1", u64::MAX - 60)).unwrap();
        assert_eq!(cmp_poly, poly_z);
    }
}
