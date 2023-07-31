// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get content of a
//! [`PolynomialRingZq].

use super::PolynomialRingZq;
use crate::{
    error::MathError,
    integer::{PolyOverZ, Z},
    integer_mod_q::ModulusPolynomialRingZq,
    traits::GetCoefficient,
    utils::index::evaluate_index,
};
use flint_sys::fmpz_poly::{fmpz_poly_degree, fmpz_poly_get_coeff_fmpz};
use std::fmt::Display;

impl GetCoefficient<Z> for PolynomialRingZq {
    /// Returns the coefficient of a [`PolynomialRingZq`] as a [`Z`].
    ///
    /// If an index is provided which exceeds the highest set coefficient, `0` is returned.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to get (has to be positive)
    ///
    /// Returns the coefficient as a [`Z`] or a [`MathError`] if the provided index
    /// is negative and therefore invalid or it does not fit into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::traits::*;
    /// use qfall_math::integer::{PolyOverZ, Z};
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("3  0 1 1").unwrap();
    /// let poly_ring = PolynomialRingZq::from((&poly, &modulus));
    ///
    /// let coeff_0: Z = poly_ring.get_coeff(0).unwrap();
    /// let coeff_1: Z = poly_ring.get_coeff(1).unwrap();
    /// let coeff_3: Z = poly_ring.get_coeff(3).unwrap();
    ///
    /// assert_eq!(Z::ZERO, coeff_0);
    /// assert_eq!(Z::ONE, coeff_1);
    /// assert_eq!(Z::ZERO, coeff_3);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the index is negative or it does not fit into an [`i64`].
    fn get_coeff(&self, index: impl TryInto<i64> + Display) -> Result<Z, MathError> {
        let index = evaluate_index(index)?;
        let mut out = Z::default();
        unsafe { fmpz_poly_get_coeff_fmpz(&mut out.value, &self.poly.poly, index) }
        Ok(out)
    }
}

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

    /// Returns the degree of a [`PolynomialRingZq`] as a [`i64`].
    /// The zero polynomial has degree '-1'.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("3  0 1 1").unwrap();
    /// let poly_ring = PolynomialRingZq::from((&poly, &modulus));
    ///
    /// let degree = poly_ring.get_degree();
    ///
    /// assert_eq!(2, degree);
    /// ```
    pub fn get_degree(&self) -> i64 {
        unsafe { fmpz_poly_degree(&self.poly.poly) }
    }
}

#[cfg(test)]
mod test_get_coeff {
    use crate::{
        integer::{PolyOverZ, Z},
        integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
        traits::GetCoefficient,
    };
    use std::str::FromStr;

    /// Ensure that 0 is returned if the provided index is not yet set.
    #[test]
    fn index_out_of_range() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  1 1 1").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let zero_coeff = poly_ring.get_coeff(3).unwrap();

        assert_eq!(Z::ZERO, zero_coeff)
    }

    /// Tests if coefficients are returned correctly.
    #[test]
    fn coeff_correct() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  1 0 3").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let coeff = poly_ring.get_coeff(2).unwrap();

        assert_eq!(Z::from(3), coeff)
    }

    /// Tests if large coefficients are returned correctly.
    #[test]
    fn large_coeff() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("5  1 0 4 1 9 mod {}", u64::MAX)).unwrap();
        let poly = PolyOverZ::from_str(&format!("3  0 {} 1", i64::MAX)).unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        assert_eq!(Z::from(i64::MAX), poly_ring.get_coeff(1).unwrap());
    }

    /// Tests if negative index yields an error.
    #[test]
    fn negative_index_error() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  1 0 3").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let coeff = poly_ring.get_coeff(-1);

        assert!(coeff.is_err())
    }
}

#[cfg(test)]
mod test_get_mod {
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
    };
    use std::str::FromStr;

    /// Ensure that the large modulus polynomial is returned correctly.
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

    /// Ensure that the getter returns for large entries.
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

#[cfg(test)]
mod test_get_degree {
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
    };
    use std::str::FromStr;

    /// Ensure that degree is working.
    #[test]
    fn degree() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  0 1 1").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let deg = poly_ring.get_degree();

        assert_eq!(2, deg);
    }

    /// Ensure that degree is working for constant polynomials.
    #[test]
    fn degree_constant() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("1  1").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let deg = poly_ring.get_degree();

        assert_eq!(0, deg);
    }

    /// Ensure that degree is working for polynomials with leading 0 coefficients.
    #[test]
    fn degree_leading_zeros() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly = PolyOverZ::from_str("3  1 0 0").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let deg = poly_ring.get_degree();

        assert_eq!(0, deg);
    }
}
