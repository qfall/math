// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! [`PolynomialRingZq`] is a type of ring over PolyOverZq/f(X).
//! Where f(X) is a [`PolyOverZq`](crate::integer_mod_q::PolyOverZq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.
//!
//! For **DEVELOPERS**: Many functions assume that the [`PolynomialRingZq`] instances are reduced.
//! To avoid unnecessary checks and reductions, always return canonical/reduced
//! values. The end-user should be unable to obtain a non-reduced value.
//! Therefore, the DEVELOPER has to call the [`PolynomialRingZq::reduce`], whenever
//! a computation may exceed the modulus, because it is not reduced automatically

use super::{ModulusPolynomialRingZq, PolyOverZq, Zq};
use crate::integer::{PolyOverZ, Z};
use derive_more::Display;
use flint_sys::fmpz_mod::fmpz_mod_mul;
use serde::{Deserialize, Serialize};

mod arithmetic;
mod cmp;
mod coefficient_embedding;
mod from;
mod get;
mod norm;
mod properties;
mod reduce;
mod sample;
mod set;
mod to_string;
mod unsafe_functions;

/// [`PolynomialRingZq`] represents polynomials over the finite field
/// [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)/f(X) where f(X) is a polynomial over [`Zq`](super::Zq).
///
/// Attributes
/// - `poly`: holds the value
/// - `modulus`: holds the modulus q and f(X)
///
/// # Examples
/// ```
/// # use qfall_math::error::MathError;
/// use qfall_math::integer::PolyOverZ;
/// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
/// use qfall_math::integer_mod_q::PolyOverZq;
/// use qfall_math::integer_mod_q::PolynomialRingZq;
/// use std::str::FromStr;
///
/// let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
/// let modulus = ModulusPolynomialRingZq::from(poly_mod);
///
/// // instantiation
/// let a = PolynomialRingZq::from((PolyOverZ::from(5), &modulus));
/// let b = PolynomialRingZq::from((PolyOverZ::from_str("2  1 5").unwrap(), &modulus));
/// let _ = a.clone();
///
/// // arithmetics
/// let _ = &a + &b;
/// let _ = &a * &b;
///
/// // to_string incl. (de-)serialization
/// assert_eq!("1  5 / 3  1 0 1 mod 17", &a.to_string());
/// let _ = serde_json::to_string(&a).unwrap();
///
/// # Ok::<(), MathError>(())
/// ```
#[derive(PartialEq, Eq, Debug, Serialize, Deserialize, Display, Clone)]
#[display("{poly} / {modulus}")]
pub struct PolynomialRingZq {
    pub(crate) poly: PolyOverZ,
    pub(crate) modulus: ModulusPolynomialRingZq,
}

impl PolynomialRingZq {
    /// This algorithm transforms an element from the polynomial ring using NTT.
    /// The algorithm will output `None`, if the base is not defined.
    ///
    /// Returns the NTT version of the polynomial if the [`NTTBasisPolynomialRingZq`](super::NTTBasisPolynomialRingZq)
    /// is set, and otherwise it returns `None`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
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
    /// polynomial_modulus.set_ntt_unchecked(1753);
    ///
    /// let sample = PolynomialRingZq::sample_uniform(&polynomial_modulus);
    ///
    /// let ntt = sample.ntt().unwrap();
    /// ```
    pub fn ntt(&self) -> Option<Vec<Zq>> {
        if let Some(ntt_basis) = self.modulus.ntt_basis.as_ref() {
            let value = PolyOverZq::from((
                &self.get_representative_least_nonnegative_residue(),
                self.get_mod().get_q(),
            ));
            Some(ntt_basis.ntt(&value))
        } else {
            None
        }
    }

    /// This algorithm transforms an element in NTT form and transfors it into its polynomial representation.
    /// The algorithm will output `None`, if the base is not defined.
    ///
    /// # Parameters
    /// - `vector`: the polynomial in NTT form
    /// - `modulus`: the modulus under which the intt is to be computed
    ///
    /// Returns the INTT version of the input if the [`NTTBasisPolynomialRingZq`](super::NTTBasisPolynomialRingZq)
    /// is set, and otherwise it returns `None`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
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
    /// polynomial_modulus.set_ntt_unchecked(1753);
    ///
    /// let sample = PolynomialRingZq::sample_uniform(&polynomial_modulus);
    ///
    /// let ntt = sample.ntt().unwrap();
    /// let sample_in_polynomial_form = PolynomialRingZq::intt(ntt, &polynomial_modulus);
    /// ```
    pub fn intt(vector: Vec<Zq>, modulus: &ModulusPolynomialRingZq) -> Option<Self> {
        modulus
            .ntt_basis
            .as_ref()
            .as_ref()
            .map(|basis| PolynomialRingZq {
                poly: basis
                    .intt(vector)
                    .get_representative_least_nonnegative_residue(),
                modulus: modulus.clone(),
            })
    }

    /// This algorithm performs polynomial multiplication of [`PolynomialRingZq`]
    /// using the NTT transform.
    ///
    /// !! Benchmarks have shown that this multiplication is slower than the
    /// classical multiplication for most parameter ranges !!
    ///
    /// # Parameters
    /// - `other`: the other vector to multiply `self`` with
    ///
    /// Returns the mulitplication of `self` with `other` using NTT transform.
    /// If the basis is not set, than it panics.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
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
    ///
    /// let sample1 = PolynomialRingZq::sample_uniform(&polynomial_modulus);
    /// let sample2 = PolynomialRingZq::sample_uniform(&polynomial_modulus);
    ///
    /// assert_eq!(&sample1 * &sample2, sample1.mul_ntt(&sample2))
    /// ```
    ///
    /// # Panics...
    /// - if the the moduli differ
    /// - if the [`NTTBasisPolynomialRingZq`](super::NTTBasisPolynomialRingZq) is not set.
    pub fn mul_ntt(&self, other: &Self) -> Self {
        assert_eq!(self.get_mod(), other.get_mod());
        let ntt1 = self.ntt().unwrap();
        let ntt2 = other.ntt().unwrap();
        let modulus = ntt1[0].get_mod();

        let mut ntt3 = Vec::with_capacity(ntt1.capacity());
        for i in 0..ntt1.len() {
            let mut z_i = Z::ZERO;
            unsafe {
                fmpz_mod_mul(
                    &mut z_i.value,
                    &ntt1[i].value.value,
                    &ntt2[i].value.value,
                    modulus.get_fmpz_mod_ctx_struct(),
                );
            }
            ntt3.push(Zq {
                value: z_i,
                modulus: modulus.clone(),
            });
        }

        PolynomialRingZq::intt(ntt3, &self.get_mod()).unwrap()
    }
}

#[cfg(test)]
mod test_setting_ntt {
    use crate::{
        integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq},
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

        polynomial_modulus.set_ntt_unchecked(1753);

        let p1 = PolynomialRingZq::sample_uniform(&polynomial_modulus);
        let p2 = PolynomialRingZq::sample_uniform(&polynomial_modulus);

        assert_eq!(&p1 * &p2, p1.mul_ntt(&p2))
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

        polynomial_modulus.set_ntt_unchecked(1945);

        let p1 = PolynomialRingZq::sample_uniform(&polynomial_modulus);
        let p2 = PolynomialRingZq::sample_uniform(&polynomial_modulus);

        assert_eq!(&p1 * &p2, p1.mul_ntt(&p2))
    }
}
