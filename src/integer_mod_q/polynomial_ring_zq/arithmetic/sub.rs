// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Sub`] trait for [`PolynomialRingZq`] values.

use super::super::PolynomialRingZq;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fq::fq_sub;
use std::{ops::Sub, str::FromStr};

impl Sub for &PolynomialRingZq {
    type Output = PolynomialRingZq;
    /// Implements the [`Sub`] trait for two [`PolynomialRingZq`] values.
    /// [`Sub`] is implemented for any combination of [`PolynomialRingZq`] and borrowed [`PolynomialRingZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the result of the subtraction of both polynomials as a [`PolynomialRingZq`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let a = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_a, &modulus);
    /// let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    /// let b = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_b, &modulus);
    ///
    /// let c: PolynomialRingZq = &a - &b;
    /// let d: PolynomialRingZq = a - b;
    /// let e: PolynomialRingZq = &c - d;
    /// let f: PolynomialRingZq = c - &e;
    /// ```
    ///
    /// # Panics ...
    /// - ... if the moduli of both [`PolynomialRingZq`] mismatch.
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
    }
}

impl PolynomialRingZq {
    /// Implements subtraction for two [`PolynomialRingZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the result of subtraction of both polynomials as a
    /// [`PolynomialRingZq`] or an error if the moduli mismatch.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let a = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_a, &modulus);
    /// let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    /// let b = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_b, &modulus);
    ///
    /// let c: PolynomialRingZq = a.sub_safe(&b).unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    /// both [`PolynomialRingZq`] mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<PolynomialRingZq, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to subtract polynomial with modulus '{}' and polynomial with modulus '{}'.",
                self.modulus, other.modulus
            )));
        }
        let mut out = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(
            &PolyOverZ::from_str("0").unwrap(),
            &self.modulus,
        );
        unsafe {
            fq_sub(
                &mut out.poly.poly,
                &self.poly.poly,
                &other.poly.poly,
                self.modulus.get_fq_ctx_struct(),
            );
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(
    Sub,
    sub,
    PolynomialRingZq,
    PolynomialRingZq,
    PolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Sub,
    sub,
    PolynomialRingZq,
    PolynomialRingZq,
    PolynomialRingZq
);

#[cfg(test)]
mod test_sub {

    use crate::integer::PolyOverZ;
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use crate::integer_mod_q::PolynomialRingZq;
    use std::str::FromStr;

    /// testing subtraction for two [`PolynomialRingZq`]
    #[test]
    fn sub() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 2").unwrap();
        let a = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_a, &modulus);
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_b, &modulus);
        let c = a - b;
        assert_eq!(
            c,
            PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(
                &PolyOverZ::from_str("4  -3 0 -2 1").unwrap(),
                &modulus
            )
        );
    }

    /// testing subtraction for two borrowed [`PolynomialRingZq`]
    #[test]
    fn sub_borrow() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 2").unwrap();
        let a = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_a, &modulus);
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_b, &modulus);
        let c = &a - &b;
        assert_eq!(
            c,
            PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(
                &PolyOverZ::from_str("4  -3 0 -2 1").unwrap(),
                &modulus
            )
        );
    }

    /// testing subtraction for borrowed [`PolynomialRingZq`] and [`PolynomialRingZq`]
    #[test]
    fn sub_first_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 2").unwrap();
        let a = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_a, &modulus);
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_b, &modulus);
        let c = &a - b;
        assert_eq!(
            c,
            PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(
                &PolyOverZ::from_str("4  -3 0 -2 1").unwrap(),
                &modulus
            )
        );
    }

    /// testing subtraction for [`PolynomialRingZq`] and borrowed [`PolynomialRingZq`]
    #[test]
    fn sub_second_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 2").unwrap();
        let a = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_a, &modulus);
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_b, &modulus);
        let c = a - &b;
        assert_eq!(
            c,
            PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(
                &PolyOverZ::from_str("4  -3 0 -2 1").unwrap(),
                &modulus
            )
        );
    }

    /// testing subtraction for [`PolynomialRingZq`] reduces '0' coefficients
    #[test]
    fn sub_reduce() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_a, &modulus);
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_b, &modulus);
        let c = a - &b;
        assert_eq!(
            c,
            PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(
                &PolyOverZ::from_str("3  -3 0 -2").unwrap(),
                &modulus
            )
        );
    }

    /// testing subtraction for big [`PolynomialRingZq`]
    #[test]
    fn sub_large_numbers() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "4  {} 0 0 {} mod {}",
            u64::MAX,
            i64::MIN + 12,
            u64::MAX - 58
        ))
        .unwrap();

        let poly_a = PolyOverZ::from_str(&format!("4  {} 0 1 {}", u64::MAX, i64::MIN)).unwrap();
        let a = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_a, &modulus);

        let poly_b = PolyOverZ::from_str(&format!("4  {} 0 -1 {}", i64::MAX, i64::MAX)).unwrap();
        let b = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_b, &modulus);

        let c = a - b;

        assert_eq!(
            c,
            PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(
                &PolyOverZ::from_str(&format!(
                    "4  {} 0 2 {}",
                    (u64::MAX - 1) / 2 + 1,
                    -18446744073709551615_i128
                ))
                .unwrap(),
                &modulus
            )
        );
    }

    /// testing subtraction for [`PolynomialRingZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn sub_mismatching_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_a, &modulus);
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_b, &modulus);
        let _c = a - b;
    }

    /// testing whether sub_safe throws an error for mismatching moduli
    #[test]
    fn sub_safe_is_err() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_a, &modulus);
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from_poly_over_z_modulus_polynomial_ring_zq(&poly_b, &modulus);

        assert!(&a.sub_safe(&b).is_err());
    }
}
