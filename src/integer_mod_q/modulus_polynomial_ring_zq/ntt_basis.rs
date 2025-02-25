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
    traits::GetCoefficient,
};
use std::rc::Rc;

impl ModulusPolynomialRingZq {
    /// Initiates the NTT-basis for the [`ModulusPolynomialRingZq`] by providing a
    /// root of unity.
    /// It is not checked if it is actually a root of unity.
    /// Based on the constant coefficient, it will either be instantiated for cyclic or negacyclic convolution.
    /// If it is 1, then it will be interpreted as negacyclic and as cyclic otherwise.
    /// The rest of the modulus-polynomial will not be checked, whether it is suited, and it will not be checked
    /// if the provided root is actually a root of unity in the ring.
    /// Setting the basis only works if `n` is a power of two.
    ///
    /// Parameters:
    /// - `root_of_unity`: the `n`th or respectivley `2n`th root of unity over the modulus
    ///
    /// Defines the NTT-basis for the modulus ring without checking the context.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use crate::qfall_math::traits::SetCoefficient;
    ///
    /// let n = 256;
    /// let modulus = 2_i64.pow(23) - 2_i64.pow(13) + 1;
    ///
    /// let mut mod_poly = PolyOverZq::from(modulus);
    /// mod_poly.set_coeff(0, 1).unwrap();
    /// mod_poly.set_coeff(n, 1).unwrap();
    ///
    /// let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);
    ///
    /// polynomial_modulus.set_ntt_unchecked(1753);
    /// ```
    ///
    /// # Safety
    /// The caller is responsible in ensuring that the  given root is actually a proper
    /// root, under the associated polynomial. For negacyclic polynomials, this means
    /// that the root must be a 2nth root of unity and for cyclic polynomials this means
    /// that it must be an nth root.
    ///
    /// # Panics
    /// - if `n` is not a power of two.
    pub fn set_ntt_unchecked(&mut self, root_of_unity: impl Into<Z>) {
        let n = self.get_degree();
        let one_coeff: Z = self.get_coeff(0).unwrap();

        let convolution_type = {
            if one_coeff == Z::ONE {
                ConvolutionType::Negacyclic
            } else {
                ConvolutionType::Cyclic
            }
        };

        let ntt_basis = NTTBasisPolynomialRingZq::init(
            n as usize,
            root_of_unity,
            &Modulus::from(self.get_q()),
            convolution_type,
        );
        self.ntt_basis = Rc::new(Some(ntt_basis))
    }
}
