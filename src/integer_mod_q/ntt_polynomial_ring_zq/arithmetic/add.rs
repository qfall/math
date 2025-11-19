// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of addition for [`NTTPolynomialRingZq`].

use crate::{
    integer::Z,
    integer_mod_q::{Modulus, NTTPolynomialRingZq},
};
use flint_sys::fmpz_mod::fmpz_mod_add;

impl NTTPolynomialRingZq {
    /// Adds `self` with `other`.
    ///
    /// Paramters:
    /// - `other`: specifies the NTT-representation of the polynomial to add to `self`
    /// - `modulus`: defines the modulus `q`
    ///
    /// Returns the NTT-representation of the sum of `self` and `other` generated
    /// with respect to `modulus`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::{NTTPolynomialRingZq, Modulus};
    /// use crate::qfall_math::traits::SetCoefficient;
    ///
    /// let n = 4;
    /// let q = Modulus::from(257);
    ///
    /// let a = NTTPolynomialRingZq::sample_uniform(n, &q);
    /// let b = NTTPolynomialRingZq::sample_uniform(n, &q);
    ///
    /// let c = a.add(&b, &q);
    /// ```
    ///
    /// # Panics ...
    /// - if the `modulus` is smaller than `2`.
    /// - if the degree of the polynomials is not equal.
    pub fn add(&self, other: &Self, modulus: &Modulus) -> Self {
        assert_eq!(
            self.poly.len(),
            other.poly.len(),
            "The degree of both polynomials has to be equal for addition."
        );
        let mod_q = modulus.get_fmpz_mod_ctx_struct();

        let mut out = NTTPolynomialRingZq {
            poly: vec![Z::default(); self.poly.len()],
        };

        for i in 0..self.poly.len() {
            unsafe {
                fmpz_mod_add(
                    &mut out.poly[i].value,
                    &self.poly[i].value,
                    &other.poly[i].value,
                    mod_q,
                );
            }
        }

        out
    }

    /// Adds `self` with `other` reusing the memory of `self`.
    ///
    /// Paramters:
    /// - `other`: specifies the NTT-representation of the polynomial to add to `self`
    /// - `modulus`: defines the modulus `q`
    ///
    /// Computes the NTT-representation of the sum of `self` and `other` generated
    /// with respect to `modulus`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::{NTTPolynomialRingZq, Modulus};
    /// use crate::qfall_math::traits::SetCoefficient;
    ///
    /// let n = 4;
    /// let q = Modulus::from(257);
    ///
    /// let mut a = NTTPolynomialRingZq::sample_uniform(n, &q);
    /// let b = NTTPolynomialRingZq::sample_uniform(n, &q);
    ///
    /// a.add_assign(&b, &q);
    /// ```
    ///
    /// # Panics ...
    /// - if the `modulus` is smaller than `2`.
    /// - if the degree of the polynomials is not equal.
    pub fn add_assign(&mut self, other: &Self, modulus: &Modulus) {
        assert_eq!(
            self.poly.len(),
            other.poly.len(),
            "The degree of both polynomials has to be equal for addition."
        );
        let mod_q = modulus.get_fmpz_mod_ctx_struct();

        for i in 0..self.poly.len() {
            unsafe {
                fmpz_mod_add(
                    &mut self.poly[i].value,
                    &self.poly[i].value,
                    &other.poly[i].value,
                    mod_q,
                );
            }
        }
    }
}

#[cfg(test)]
mod test_add {
    use crate::{
        integer_mod_q::{
            Modulus, ModulusPolynomialRingZq, NTTPolynomialRingZq, PolyOverZq, PolynomialRingZq,
        },
        traits::SetCoefficient,
    };

    /// Ensure that the entrywise addition and the intuitive addition yields
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

        let ntt1 = NTTPolynomialRingZq::from(&p1);
        let ntt2 = NTTPolynomialRingZq::from(&p2);

        let res = ntt1.add(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 + &p2,
            PolynomialRingZq::from((res, &polynomial_modulus))
        )
    }

    /// Ensure that the entrywise addition and the intuitive addition yields
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

        let ntt1 = NTTPolynomialRingZq::from(&p1);
        let ntt2 = NTTPolynomialRingZq::from(&p2);

        let res = ntt1.add(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 + &p2,
            PolynomialRingZq::from((res, &polynomial_modulus))
        )
    }
}

#[cfg(test)]
mod test_add_assign {
    use crate::{
        integer_mod_q::{
            Modulus, ModulusPolynomialRingZq, NTTPolynomialRingZq, PolyOverZq, PolynomialRingZq,
        },
        traits::SetCoefficient,
    };

    /// Ensure that the entrywise addition and the intuitive addition yields
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

        let mut ntt1 = NTTPolynomialRingZq::from(&p1);
        let ntt2 = NTTPolynomialRingZq::from(&p2);

        ntt1.add_assign(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 + &p2,
            PolynomialRingZq::from((ntt1, &polynomial_modulus))
        )
    }

    /// Ensure that the entrywise addition and the intuitive addition yields
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

        let mut ntt1 = NTTPolynomialRingZq::from(&p1);
        let ntt2 = NTTPolynomialRingZq::from(&p2);

        ntt1.add_assign(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 + &p2,
            PolynomialRingZq::from((ntt1, &polynomial_modulus))
        )
    }
}
