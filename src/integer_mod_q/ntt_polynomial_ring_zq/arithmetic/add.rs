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
    integer_mod_q::NTTPolynomialRingZq,
    macros::arithmetics::{
        arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpz_mod::fmpz_mod_add;
use std::ops::{Add, AddAssign};

impl Add for &NTTPolynomialRingZq {
    type Output = NTTPolynomialRingZq;

    /// Adds `self` with `other`.
    ///
    /// Paramters:
    /// - `other`: specifies the NTT-representation of the polynomial to add to `self`
    ///
    /// Returns the NTT-representation of the sum of `self` and `other`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::{NTTPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
    /// modulus.set_ntt_unchecked(64);
    ///
    /// let a = NTTPolynomialRingZq::sample_uniform(&modulus);
    /// let b = NTTPolynomialRingZq::sample_uniform(&modulus);
    ///
    /// let c = a + b;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli are not equal.
    fn add(self, other: Self) -> Self::Output {
        assert_eq!(
            self.modulus, other.modulus,
            "The moduli of both polynomials have to be equal for addition."
        );
        let mod_q = &self.modulus.get_fq_ctx().ctxp[0];

        let mut out = NTTPolynomialRingZq {
            poly: vec![Z::default(); self.poly.len()],
            modulus: self.modulus.clone(),
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
}

arithmetic_trait_borrowed_to_owned!(
    Add,
    add,
    NTTPolynomialRingZq,
    NTTPolynomialRingZq,
    NTTPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Add,
    add,
    NTTPolynomialRingZq,
    NTTPolynomialRingZq,
    NTTPolynomialRingZq
);

impl AddAssign<&NTTPolynomialRingZq> for NTTPolynomialRingZq {
    /// Adds `self` with `other` reusing the memory of `self`.
    ///
    /// Paramters:
    /// - `other`: specifies the NTT-representation of the polynomial to add to `self`
    ///
    /// Computes the NTT-representation of the sum of `self` and `other`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::{NTTPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
    /// modulus.set_ntt_unchecked(64);
    ///
    /// let mut a = NTTPolynomialRingZq::sample_uniform(&modulus);
    /// let b = NTTPolynomialRingZq::sample_uniform(&modulus);
    ///
    /// a += b;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli are not equal.
    fn add_assign(&mut self, other: &Self) {
        assert_eq!(
            self.modulus, other.modulus,
            "The moduli of both polynomials have to be equal for addition."
        );
        let mod_q = &self.modulus.get_fq_ctx().ctxp[0];

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

arithmetic_assign_trait_borrowed_to_owned!(
    AddAssign,
    add_assign,
    NTTPolynomialRingZq,
    NTTPolynomialRingZq
);

#[cfg(test)]
mod test_add {
    use std::ops::Add;

    use crate::{
        integer_mod_q::{
            ModulusPolynomialRingZq, NTTPolynomialRingZq, PolyOverZq, PolynomialRingZq,
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

        let res = (&ntt1).add(ntt2);

        assert_eq!(&p1 + &p2, PolynomialRingZq::from(res))
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

        let res = ntt1.add(ntt2);

        assert_eq!(&p1 + &p2, PolynomialRingZq::from(res))
    }
}

#[cfg(test)]
mod test_add_assign {
    use std::ops::AddAssign;

    use crate::{
        integer_mod_q::{
            ModulusPolynomialRingZq, NTTPolynomialRingZq, PolyOverZq, PolynomialRingZq,
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

        ntt1.add_assign(ntt2);

        assert_eq!(&p1 + &p2, PolynomialRingZq::from(ntt1))
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

        ntt1.add_assign(&ntt2);

        assert_eq!(&p1 + &p2, PolynomialRingZq::from(ntt1))
    }
}
