// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`PolynomialRingZq`] values.

use super::super::PolynomialRingZq;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fq::fq_mul;
use std::ops::Mul;

impl Mul for &PolynomialRingZq {
    type Output = PolynomialRingZq;
    /// Implements the [`Mul`] trait for two [`PolynomialRingZq`] values.
    /// [`Mul`] is implemented for any combination of [`PolynomialRingZq`] and borrowed [`PolynomialRingZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to multiply to `self`
    ///
    /// Returns the product of both polynomials as a [`PolynomialRingZq`].
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
    /// let a = PolynomialRingZq::from((&poly_a, &modulus));
    /// let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    /// let b = PolynomialRingZq::from((&poly_b, &modulus));
    ///
    /// let c: PolynomialRingZq = &a * &b;
    /// let d: PolynomialRingZq = a * b;
    /// let e: PolynomialRingZq = &c * d;
    /// let f: PolynomialRingZq = c * &e;
    /// ```
    ///
    /// # Panics ...
    /// - ... if the moduli of both [`PolynomialRingZq`] mismatch.
    fn mul(self, other: Self) -> Self::Output {
        self.mul_safe(other).unwrap()
    }
}

impl PolynomialRingZq {
    /// Implements multiplication for two [`PolynomialRingZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to multiply to `self`
    ///
    /// Returns the product of both polynomials as a [`PolynomialRingZq`] or an error if the moduli
    /// mismatch.
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
    /// let a = PolynomialRingZq::from((&poly_a, &modulus));
    /// let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    /// let b = PolynomialRingZq::from((&poly_b, &modulus));
    ///
    /// let c: PolynomialRingZq = a.mul_safe(&b).unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    /// both [`PolynomialRingZq`] mismatch.
    pub fn mul_safe(&self, other: &Self) -> Result<PolynomialRingZq, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to multiply polynomial with modulus '{}' and polynomial with modulus '{}'.",
                self.modulus, other.modulus
            )));
        }
        let mut out = PolynomialRingZq::from((&PolyOverZ::default(), &self.modulus));
        unsafe {
            fq_mul(
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
    Mul,
    mul,
    PolynomialRingZq,
    PolynomialRingZq,
    PolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Mul,
    mul,
    PolynomialRingZq,
    PolynomialRingZq,
    PolynomialRingZq
);

#[cfg(test)]
mod test_mul {

    use crate::integer::PolyOverZ;
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use crate::integer_mod_q::PolynomialRingZq;
    use std::str::FromStr;

    /// testing multiplication for two [`PolynomialRingZq`]
    #[test]
    fn mul() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_a, &modulus));
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_b, &modulus));
        let c = a * b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("3  15 14 12").unwrap(), &modulus))
        );
    }

    /// testing multiplication for two borrowed [`PolynomialRingZq`]
    #[test]
    fn mul_borrow() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_a, &modulus));
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_b, &modulus));
        let c = &a * &b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("3  15 14 12").unwrap(), &modulus))
        );
    }

    /// testing multiplication for borrowed [`PolynomialRingZq`] and [`PolynomialRingZq`]
    #[test]
    fn mul_first_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_a, &modulus));
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_b, &modulus));
        let c = &a * b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("3  15 14 12").unwrap(), &modulus))
        );
    }

    /// testing multiplication for [`PolynomialRingZq`] and borrowed [`PolynomialRingZq`]
    #[test]
    fn mul_second_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_a, &modulus));
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_b, &modulus));
        let c = a * &b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("3  15 14 12").unwrap(), &modulus))
        );
    }

    /// testing multiplication for [`PolynomialRingZq`] with constant
    #[test]
    fn mul_constant() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_a, &modulus));
        let poly_b = PolyOverZ::from_str("1  3").unwrap();
        let b = PolynomialRingZq::from((&poly_b, &modulus));
        let c = &a * b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("4  -3 0 3 3").unwrap(), &modulus))
        );
        assert_eq!(
            PolynomialRingZq::from((&PolyOverZ::from_str("0").unwrap(), &modulus)),
            a * PolynomialRingZq::from((&PolyOverZ::from_str("0").unwrap(), &modulus))
        )
    }

    /// testing multiplication for big [`PolynomialRingZq`]
    #[test]
    fn mul_large_numbers() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "4  {} 0 0 {} mod {}",
            u64::MAX,
            i64::MIN,
            u64::MAX - 58
        ))
        .unwrap();

        let poly_a = PolyOverZ::from_str(&format!("3  {} 0 {}", u64::MAX, i64::MIN)).unwrap();
        let a = PolynomialRingZq::from((&poly_a, &modulus));

        let poly_b = PolyOverZ::from_str(&format!("3  {} 0 {}", i64::MAX, i64::MAX)).unwrap();
        let b = PolynomialRingZq::from((&poly_b, &modulus));

        let c = a * b;
        assert_eq!(
            c,
            PolynomialRingZq::from((
                &PolyOverZ::from_str(&format!(
                    "5  {} {} {} {} {}",
                    u128::from(u64::MAX) * u128::from((u64::MAX - 1) / 2),
                    0,
                    i128::from(i64::MIN) * i128::from(i64::MAX)
                        + (i128::from(i64::MAX) - i128::from(i64::MIN)) * i128::from(i64::MAX),
                    0,
                    i128::from(i64::MAX) * i128::from(i64::MIN)
                ))
                .unwrap(),
                &modulus
            ))
        );
    }

    /// testing multiplication for [`PolynomialRingZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn mul_mismatching_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_a, &modulus));
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_b, &modulus));
        let _c = a * b;
    }

    /// testing whether mul_safe throws an error for mismatching moduli
    #[test]
    fn mul_safe_is_err() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_a = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_a, &modulus));
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_b, &modulus));

        assert!(&a.mul_safe(&b).is_err());
    }
}
