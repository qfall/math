// Copyright © 2023 Phil Milewski, Marcel Luca Schmidt
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
    integer_mod_q::PolyOverZq,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
    traits::CompareBase,
};
use flint_sys::fq::fq_sub;
use std::ops::Sub;

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
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let a = PolynomialRingZq::from((&poly_1, &modulus));
    /// let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    /// let b = PolynomialRingZq::from((&poly_2, &modulus));
    ///
    /// let c: PolynomialRingZq = &a - &b;
    /// let d: PolynomialRingZq = a - b;
    /// let e: PolynomialRingZq = &c - d;
    /// let f: PolynomialRingZq = c - &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli of both [`PolynomialRingZq`] mismatch.
    fn sub(self, other: Self) -> Self::Output {
        self.sub_safe(other).unwrap()
    }
}

impl Sub<&PolyOverZ> for &PolynomialRingZq {
    type Output = PolynomialRingZq;
    /// Implements the [`Sub`] trait for [`PolynomialRingZq`] and [`PolyOverZ`].
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the subtraction of both polynomials as a [`PolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let a = PolynomialRingZq::from((&poly, &modulus));
    /// let b = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    ///
    /// let c: PolynomialRingZq = &a - &b;
    /// ```
    fn sub(self, other: &PolyOverZ) -> Self::Output {
        let mut out = PolynomialRingZq::from((&PolyOverZ::default(), &self.modulus));
        unsafe {
            fq_sub(
                &mut out.poly.poly,
                &self.poly.poly,
                &other.poly,
                self.modulus.get_fq_ctx(),
            );
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolynomialRingZq, PolyOverZ, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolynomialRingZq, PolyOverZ, PolynomialRingZq);

impl Sub<&PolyOverZq> for &PolynomialRingZq {
    type Output = PolynomialRingZq;
    /// Implements the [`Sub`] trait for [`PolynomialRingZq`] and [`PolyOverZq`].
    /// [`Sub`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the subtraction of both polynomials as a [`PolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolyOverZq, PolynomialRingZq};
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let a = PolynomialRingZq::from((&poly, &modulus));
    /// let b = PolyOverZq::from_str("4  2 0 3 1 mod 17").unwrap();
    ///
    /// let c: PolynomialRingZq = &a - &b;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli mismatch.
    fn sub(self, other: &PolyOverZq) -> Self::Output {
        assert_eq!(
            self.modulus.get_q(),
            other.modulus,
            "Tried to subtract polynomials with different moduli."
        );

        let mut out = PolynomialRingZq::from((&PolyOverZ::default(), &self.modulus));
        unsafe {
            fq_sub(
                &mut out.poly.poly,
                &self.poly.poly,
                &other.get_representative_least_nonnegative_residue().poly,
                self.modulus.get_fq_ctx(),
            );
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolynomialRingZq, PolyOverZq, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolynomialRingZq, PolyOverZq, PolynomialRingZq);

impl PolynomialRingZq {
    /// Implements subtraction for two [`PolynomialRingZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to subtract from `self`
    ///
    /// Returns the result of subtraction of both polynomials as a
    /// [`PolynomialRingZq`] or an error if the moduli mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let a = PolynomialRingZq::from((&poly_1, &modulus));
    /// let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    /// let b = PolynomialRingZq::from((&poly_2, &modulus));
    ///
    /// let c: PolynomialRingZq = a.sub_safe(&b).unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    ///   both [`PolynomialRingZq`] mismatch.
    pub fn sub_safe(&self, other: &Self) -> Result<PolynomialRingZq, MathError> {
        if !self.compare_base(other) {
            return Err(self.call_compare_base_error(other).unwrap());
        }
        let mut out = PolynomialRingZq::from((&PolyOverZ::default(), &self.modulus));
        unsafe {
            fq_sub(
                &mut out.poly.poly,
                &self.poly.poly,
                &other.poly.poly,
                self.modulus.get_fq_ctx(),
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

    /// Testing subtraction for two [`PolynomialRingZq`]
    #[test]
    fn sub() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 2").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = a - b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("4  -3 0 -2 1").unwrap(), &modulus))
        );
    }

    /// Testing subtraction for two borrowed [`PolynomialRingZq`]
    #[test]
    fn sub_borrow() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 2").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = &a - &b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("4  -3 0 -2 1").unwrap(), &modulus))
        );
    }

    /// Testing subtraction for borrowed [`PolynomialRingZq`] and [`PolynomialRingZq`]
    #[test]
    fn sub_first_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 2").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = &a - b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("4  -3 0 -2 1").unwrap(), &modulus))
        );
    }

    /// Testing subtraction for [`PolynomialRingZq`] and borrowed [`PolynomialRingZq`]
    #[test]
    fn sub_second_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 2").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = a - &b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("4  -3 0 -2 1").unwrap(), &modulus))
        );
    }

    /// Testing subtraction for [`PolynomialRingZq`] reduces `0` coefficients
    #[test]
    fn sub_reduce() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = a - &b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("3  -3 0 -2").unwrap(), &modulus))
        );
    }

    /// Testing subtraction for large [`PolynomialRingZq`]
    #[test]
    fn sub_large_numbers() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "4  {} 0 0 {} mod {}",
            u64::MAX,
            i64::MIN + 12,
            u64::MAX - 58
        ))
        .unwrap();

        let poly_1 = PolyOverZ::from_str(&format!("4  {} 0 1 {}", u64::MAX, i64::MIN)).unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));

        let poly_2 = PolyOverZ::from_str(&format!("4  {} 0 -1 {}", i64::MAX, i64::MAX)).unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));

        let c = a - b;

        assert_eq!(
            c,
            PolynomialRingZq::from((
                &PolyOverZ::from_str(&format!(
                    "4  {} 0 2 {}",
                    (u64::MAX - 1) / 2 + 1,
                    -18446744073709551615_i128
                ))
                .unwrap(),
                &modulus
            ))
        );
    }

    /// Testing subtraction for [`PolynomialRingZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn sub_mismatching_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let _ = a - b;
    }

    /// Testing whether sub_safe throws an error for mismatching moduli
    #[test]
    fn sub_safe_is_err() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));

        assert!(&a.sub_safe(&b).is_err());
    }
}

#[cfg(test)]
mod test_sub_poly_over_z {
    use super::PolynomialRingZq;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Checks if polynomial subtraction works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 =
            PolynomialRingZq::from_str(&format!("2  2 {} / 4  1 2 3 4 mod {}", i64::MAX, u64::MAX))
                .unwrap();
        let poly_2 = PolynomialRingZq::from_str(&format!(
            "2  1 {} / 4  1 2 3 4 mod {}",
            i64::MAX as u64 - 2,
            u64::MAX
        ))
        .unwrap();
        let poly = PolyOverZ::from_str("2  1 2").unwrap();

        let poly_1 = &poly_1 - &poly;

        assert_eq!(poly_2, poly_1);
    }

    /// Checks if subtraction works fine for different types
    #[test]
    fn availability() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let z = PolyOverZ::from(2);

        _ = poly.clone() - z.clone();
        _ = &poly - &z;
        _ = &poly - z.clone();
        _ = poly.clone() - &z;
    }
}

#[cfg(test)]
mod test_sub_poly_over_zq {
    use super::PolynomialRingZq;
    use crate::integer_mod_q::PolyOverZq;
    use std::str::FromStr;

    /// Checks if polynomial subtraction works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 =
            PolynomialRingZq::from_str(&format!("2  2 {} / 4  1 2 3 4 mod {}", i64::MAX, u64::MAX))
                .unwrap();
        let poly_2 = PolynomialRingZq::from_str(&format!(
            "2  1 {} / 4  1 2 3 4 mod {}",
            i64::MAX as u64 - 2,
            u64::MAX
        ))
        .unwrap();
        let poly = PolyOverZq::from_str(&format!("2  1 2 mod {}", u64::MAX)).unwrap();

        let poly_1 = &poly_1 - &poly;

        assert_eq!(poly_2, poly_1);
    }

    /// Checks if subtraction works fine for different types
    #[test]
    fn availability() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let zq = PolyOverZq::from((2, 17));

        _ = poly.clone() - zq.clone();
        _ = &poly - &zq;
        _ = &poly - zq.clone();
        _ = poly.clone() - &zq;
    }

    /// Checks if subtraction panics if the moduli mismatch
    #[test]
    #[should_panic]
    fn different_moduli_panic() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let zq = PolyOverZq::from((2, 16));

        _ = &poly - &zq;
    }
}
