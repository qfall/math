// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to construct [`NTTBasisPolynomialRingZq`] for the
//! NTT-transform for [`PolyOverZq`](crate::integer_mod_q::PolyOverZq) objects in the polynomialring.
//!
//! The explicit functions contain the documentation.

use super::NTTBasisPolynomialRingZq;
use crate::{
    integer::Z,
    integer_mod_q::{Modulus, Zq},
    traits::Pow,
};

impl NTTBasisPolynomialRingZq {
    /// This function allows to initialize a [`NTTBasisPolynomialRingZq`]
    /// object.
    /// We currently only allow for two kinds of moduli to accompany the construction:
    /// It must be either cyclic (`X^n - 1`) or negacyclic (`X^n + 1`) convoluted wrapping (also submitted in the algorithm)
    /// and the degree of the polynomial must be a power of two.
    /// Only then can we compute a full-split of the polynomial ring.
    /// Accordingly, the `root_of_unity` must be a `n`th root of unity or respectively a `2n`th root of unity.
    ///
    /// This function does not check if the provided root of unity is actually a root of unity!
    ///
    /// Parameters:
    /// - `n`: the degree of the polynomial
    /// - `root_of_unity`: the `n`-th or `2n`-th root of unity
    /// - `q`: the modulus of the polynomial
    /// - `convolution_type`: defines whether convolution is cyclic or negacyclic
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Modulus;
    /// use qfall_math::integer_mod_q::NTTBasisPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ConvolutionType;
    ///
    /// let modulus = Modulus::from(7681);
    ///
    /// // Initializes the NTT for `X^4 - 1 mod 7681`
    /// let ntt_basis =
    ///     NTTBasisPolynomialRingZq::init(4, 3383, &modulus, ConvolutionType::Cyclic);
    ///
    /// // Initializes the NTT for `X^4 + 1 mod 7681`
    /// let ntt_basis =
    ///     NTTBasisPolynomialRingZq::init(4, 1925, &modulus, ConvolutionType::Negacyclic);
    /// ```
    ///
    /// # Panics...
    /// - if `n` is not a power of two.
    pub fn init(
        n: usize,
        root_of_unity: impl Into<Z>,
        modulus: impl Into<Modulus>,
        convolution_type: ConvolutionType,
    ) -> Self {
        assert_eq!(n.next_power_of_two(), n);
        let n = n as i64;
        let root_of_unity = Zq::from((root_of_unity, modulus));
        let modulus = root_of_unity.get_mod();

        let n_inv = Zq::from((n, modulus)).inverse().unwrap();
        let root_of_unity_inv = root_of_unity.inverse().unwrap();

        // map the input to the `n`th root of unity and prepare power computation
        let (psi, psi_inv, omega, omega_inv) = match convolution_type {
            ConvolutionType::Cyclic => (None, None, root_of_unity.clone(), root_of_unity_inv),
            ConvolutionType::Negacyclic => (
                Some(&root_of_unity),
                Some(&root_of_unity_inv),
                root_of_unity.pow(2).unwrap(),
                root_of_unity.pow(-2).unwrap(),
            ),
        };

        // precompute powers of `n`th root of unity
        let powers_of_omega = (0..n)
            .map(|i| {
                omega
                    .pow(i)
                    .unwrap()
                    .get_representative_least_nonnegative_residue()
            })
            .collect();
        let powers_of_omega_inv = (0..n)
            .map(|i| {
                omega_inv
                    .pow(i)
                    .unwrap()
                    .get_representative_least_nonnegative_residue()
            })
            .collect();

        // precompute powers of `2n`th root of unity
        let powers_of_psi = match convolution_type {
            ConvolutionType::Cyclic => Vec::new(),
            ConvolutionType::Negacyclic => (0..n)
                .map(|i| {
                    psi.unwrap()
                        .pow(i)
                        .unwrap()
                        .get_representative_least_nonnegative_residue()
                })
                .collect(),
        };
        let powers_of_psi_inv = match convolution_type {
            ConvolutionType::Cyclic => Vec::new(),
            ConvolutionType::Negacyclic => (0..n)
                .map(|i| {
                    psi_inv
                        .unwrap()
                        .pow(i)
                        .unwrap()
                        .get_representative_least_nonnegative_residue()
                })
                .collect(),
        };

        Self {
            n,
            n_inv: n_inv.get_representative_least_nonnegative_residue(),
            powers_of_omega,
            powers_of_omega_inv,
            powers_of_psi,
            powers_of_psi_inv,
            modulus: root_of_unity.get_mod(),
            convolution_type: convolution_type.clone(),
        }
    }
}

/// This enum only serves the purpose of distinguishing between cycic or negacyclic wrapping
/// in polynomial rings, and more specificially, for the purpose of distinguishing them when utilizing NTT
/// for the polynomial rings.
#[derive(Debug, Clone, PartialEq)]
pub enum ConvolutionType {
    Cyclic,
    Negacyclic,
}

#[cfg(test)]
mod test_init {
    use super::ConvolutionType;
    use crate::{
        integer::Z,
        integer_mod_q::{Modulus, NTTBasisPolynomialRingZq},
    };

    /// Our algorithm only supports complete splits as of right now, so other inputs should be prohibited for now.
    #[test]
    #[should_panic]
    fn n_not_power_2() {
        let _ = NTTBasisPolynomialRingZq::init(12315, 1, 2, ConvolutionType::Cyclic);
    }

    /// Ensure that the algorithm sets the set of values as expected
    #[test]
    fn set_values_correctly_cyclic() {
        let ntt_basis = NTTBasisPolynomialRingZq::init(4, 3383, 7681, ConvolutionType::Cyclic);

        assert_eq!(ConvolutionType::Cyclic, ntt_basis.convolution_type);
        assert_eq!(Modulus::from(7681), ntt_basis.modulus);
        assert_eq!(4, ntt_basis.n);
        assert_eq!(Z::from(5761), ntt_basis.n_inv);
        assert!(ntt_basis.powers_of_psi.is_empty());
        assert!(ntt_basis.powers_of_psi_inv.is_empty());
        assert_eq!(
            vec![Z::from(1), Z::from(3383), Z::from(7680), Z::from(4298)],
            ntt_basis.powers_of_omega
        );
        assert_eq!(
            vec![Z::from(1), Z::from(4298), Z::from(7680), Z::from(3383)],
            ntt_basis.powers_of_omega_inv
        );
    }

    /// Ensure that the algorithm sets the set of values as expected
    #[test]
    fn set_values_correctly_negacyclic() {
        let ntt_basis = NTTBasisPolynomialRingZq::init(4, 1925, 7681, ConvolutionType::Negacyclic);

        assert_eq!(ConvolutionType::Negacyclic, ntt_basis.convolution_type);
        assert_eq!(Modulus::from(7681), ntt_basis.modulus);
        assert_eq!(4, ntt_basis.n);
        assert_eq!(Z::from(5761), ntt_basis.n_inv);
        assert_eq!(
            vec![Z::from(1), Z::from(1925), Z::from(3383), Z::from(6468)],
            ntt_basis.powers_of_psi
        );
        assert_eq!(
            vec![Z::from(1), Z::from(1213), Z::from(4298), Z::from(5756)],
            ntt_basis.powers_of_psi_inv
        );
        assert_eq!(
            vec![Z::from(1), Z::from(3383), Z::from(7680), Z::from(4298)],
            ntt_basis.powers_of_omega
        );
        assert_eq!(
            vec![Z::from(1), Z::from(4298), Z::from(7680), Z::from(3383)],
            ntt_basis.powers_of_omega_inv
        );
    }
}
