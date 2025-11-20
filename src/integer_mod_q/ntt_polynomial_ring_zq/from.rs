// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`NTTPolynomialRingZq`] value from other types.

use super::NTTPolynomialRingZq;
use crate::integer_mod_q::{PolyOverZq, PolynomialRingZq};

impl From<&PolynomialRingZq> for NTTPolynomialRingZq {
    /// Computes the NTT representation of `poly`.
    ///
    /// Parameters:
    /// - `poly`: the polynomial that's going to be represented in NTT form.
    ///
    /// Returns the NTT representation as a [`NTTPolynomialRingZq`] of `poly`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{NTTPolynomialRingZq, PolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq};
    /// use crate::qfall_math::traits::SetCoefficient;
    /// use std::str::FromStr;
    ///
    /// let n = 4;
    /// let modulus = 7681;
    ///
    /// let mut mod_poly = PolyOverZq::from(modulus);
    /// mod_poly.set_coeff(0, 1).unwrap();
    /// mod_poly.set_coeff(n, 1).unwrap();
    ///
    /// let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);
    /// polynomial_modulus.set_ntt_unchecked(1925);
    ///
    /// let poly_ring = PolynomialRingZq::sample_uniform(&polynomial_modulus);
    ///
    /// let ntt_poly_ring = NTTPolynomialRingZq::from(&poly_ring);
    /// ```
    ///
    /// # Panics ...
    /// - if the [`NTTBasisPolynomialRingZq`](crate::integer_mod_q::NTTBasisPolynomialRingZq),
    ///   which is part of the [`ModulusPolynomialRingZq`](crate::integer_mod_q::ModulusPolynomialRingZq) in `poly`
    ///   is not set.
    fn from(poly: &PolynomialRingZq) -> Self {
        if let Some(ntt_basis) = poly.modulus.ntt_basis.as_ref() {
            let value = PolyOverZq::from((
                &poly.get_representative_least_nonnegative_residue(),
                poly.get_mod().get_q(),
            ));
            NTTPolynomialRingZq {
                poly: ntt_basis.ntt(&value),
                modulus: poly.modulus.clone(),
            }
        } else {
            panic!("The NTTBasisPolynomialRingZq is not set.")
        }
    }
}

impl NTTPolynomialRingZq {
    /// Computes the inverse NTT of `self` with respect to the given `modulus`.
    ///
    /// Returns a new [`PolynomialRingZq`] with the specified [`ModulusPolynomialRingZq`](crate::integer_mod_q::ModulusPolynomialRingZq)
    /// and values as defined in `self`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, PolyOverZq, ModulusPolynomialRingZq, NTTPolynomialRingZq};
    /// use qfall_math::traits::SetCoefficient;
    ///
    /// let n = 4;
    /// let modulus = 7681;
    ///
    /// let mut mod_poly = PolyOverZq::from(modulus);
    /// mod_poly.set_coeff(0, 1).unwrap();
    /// mod_poly.set_coeff(n, 1).unwrap();
    ///
    /// let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);
    /// polynomial_modulus.set_ntt_unchecked(1925);
    ///
    /// let ntt = NTTPolynomialRingZq::sample_uniform(&polynomial_modulus);
    ///
    /// let res = ntt.inv_ntt();
    /// ```
    ///
    /// # Panics ...
    /// - if the [`NTTBasisPolynomialRingZq`](crate::integer_mod_q::NTTBasisPolynomialRingZq) in `modulus`
    ///   is not set.
    pub fn inv_ntt(self) -> PolynomialRingZq {
        PolynomialRingZq::from(self)
    }
}

#[cfg(test)]
mod test_from {
    use crate::{
        integer::{PolyOverZ, Z},
        integer_mod_q::{ModulusPolynomialRingZq, NTTPolynomialRingZq, PolynomialRingZq},
    };
    use std::str::FromStr;

    /// Ensures that from [`PolynomialRingZq`] works properly.
    #[test]
    fn from_polynomial_ring_zq() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);
        let poly = PolyOverZ::from_str("4  130 99 64 210").unwrap();
        let poly_ring_zq = PolynomialRingZq::from((&poly, &modulus));
        let cmp = vec![Z::from(114), Z::from(84), Z::from(154), Z::from(168)];

        let ntt_poly = NTTPolynomialRingZq::from(&poly_ring_zq);

        assert_eq!(ntt_poly.poly, cmp);
    }
}
