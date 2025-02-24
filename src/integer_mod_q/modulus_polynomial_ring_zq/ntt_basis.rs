// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to instantiate
//! the ntt basis for a given `[ModulusPolynomialRingZq`] object.
//!
//! This includes a collection of fixed NTT-viable rings, and the option to set them
//! unchecked.
//!
//! The explicit functions contain the documentation.

use super::ModulusPolynomialRingZq;
use crate::{
    integer::Z,
    integer_mod_q::{
        ntt_basis_polynomial_ring_zq::{ConvolutionType, NTTBasisPolynomialRingZq},
        Modulus,
    },
};
use std::rc::Rc;

impl ModulusPolynomialRingZq {
    /// # Examples
    /// ```
    /// ```
    ///
    /// # Safety
    /// The caller is responsible in ensuring that the  given root is actually a proper
    /// root, under the associated polynomial. For negacyclic polynomials, this means
    /// that the root must be a 2nth root of unity and for cyclic polynomials this means
    /// that it must be an nth root.
    pub unsafe fn set_ntt_unchecked(&mut self, root_of_unity: impl Into<Z>) {
        let n = self.get_degree();

        let ntt_basis = NTTBasisPolynomialRingZq::init(
            n as usize,
            root_of_unity,
            &Modulus::from(self.get_q()),
            ConvolutionType::Negacyclic,
        );
        self.ntt_basis = Rc::new(Some(ntt_basis))
    }
}

#[cfg(test)]
mod test_setting_ntt {
    use crate::{
        integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq, Zq},
        traits::SetCoefficient,
    };

    /// Ensure that the entrywise multiplication and the intuitive multiplication yields
    /// the same results for the parameters from Dilithium.
    #[test]
    fn test_dilithium_params() {
        let n = 256;
        let modulus = 2_i64.pow(23) - 2_i64.pow(13) + 1;

        let mut mod_poly = PolyOverZq::from(modulus);
        mod_poly.set_coeff(0, 1).unwrap();
        mod_poly.set_coeff(n, 1).unwrap();

        let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);
        unsafe {
            polynomial_modulus.set_ntt_unchecked(1753);
        };

        let p1 = PolynomialRingZq::sample_uniform(&polynomial_modulus);
        let p2 = PolynomialRingZq::sample_uniform(&polynomial_modulus);

        let p1_ntt: Vec<Zq> = p1.ntt().unwrap();
        let p2_ntt: Vec<Zq> = p2.ntt().unwrap();

        let mut p3_ntt = Vec::new();
        for i in 0..256 {
            p3_ntt.push(&p1_ntt[i] * &p2_ntt[i])
        }

        let p3 = PolynomialRingZq::intt(p3_ntt, &polynomial_modulus).unwrap();
        assert_eq!(p3, p1 * p2)
    }

    /// Ensure that the entrywise multiplication and the intuitive multiplication yields
    /// the same results for the parameters from Hawk1024.
    #[test]
    fn test_hawk1024_params() {
        let n = 1024;
        let modulus = 12289;

        let mut mod_poly = PolyOverZq::from(modulus);
        mod_poly.set_coeff(0, 1).unwrap();
        mod_poly.set_coeff(n, 1).unwrap();

        let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);
        unsafe {
            polynomial_modulus.set_ntt_unchecked(1945);
        };

        let p1 = PolynomialRingZq::sample_uniform(&polynomial_modulus);
        let p2 = PolynomialRingZq::sample_uniform(&polynomial_modulus);

        let p1_ntt: Vec<Zq> = p1.ntt().unwrap();
        let p2_ntt: Vec<Zq> = p2.ntt().unwrap();

        let mut p3_ntt = Vec::new();
        for i in 0..1024 {
            p3_ntt.push(&p1_ntt[i] * &p2_ntt[i])
        }

        let p3 = PolynomialRingZq::intt(p3_ntt, &polynomial_modulus).unwrap();
        assert_eq!(p3, p1 * p2)
    }
}
