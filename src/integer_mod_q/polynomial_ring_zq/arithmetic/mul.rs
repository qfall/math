// Copyright © 2023 Phil Milewski, Marcel Luca Schmidt
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
    integer_mod_q::PolyOverZq,
    macros::arithmetics::{
        arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned, arithmetic_trait_reverse,
    },
    traits::CompareBase,
};
use flint_sys::fq::fq_mul;
use std::ops::{Mul, MulAssign};

impl MulAssign<&PolynomialRingZq> for PolynomialRingZq {
    /// Computes the multiplication of `self` and `other` reusing
    /// the memory of `self`.
    /// [`MulAssign`] can be used on [`PolynomialRingZq`] in combination with
    /// [`PolynomialRingZq`], [`PolyOverZ`] and [`PolyOverZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to multiply to `self`
    ///
    /// Returns the product of both polynomials modulo `Z_q[X]` as a [`PolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq};
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let mut a = PolynomialRingZq::from((&poly_1, &modulus));
    /// let c = PolyOverZ::from_str("4  2 0 3 1").unwrap();
    /// let b = PolynomialRingZq::from((&c, &modulus));
    /// let d = PolyOverZq::from((&c, 17));
    ///
    /// a *= &b;
    /// a *= b;
    /// a *= &c;
    /// a *= c;
    /// a *= &d;
    /// a *= d;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli of both [`PolynomialRingZq`] mismatch.
    fn mul_assign(&mut self, other: &Self) {
        if !self.compare_base(other) {
            panic!("{}", self.call_compare_base_error(other).unwrap());
        }

        unsafe {
            fq_mul(
                &mut self.poly.poly,
                &self.poly.poly,
                &other.poly.poly,
                self.modulus.get_fq_ctx(),
            );
        };
    }
}
impl<T> MulAssign<T> for PolynomialRingZq
where
    PolyOverZ: MulAssign<T>,
{
    /// Documentation at [`PolynomialRingZq::mul_assign`]
    /// This implicitly also implements scalar multiplication for all types that have a `mul_assign` with [`PolyOverZ`]`.
    fn mul_assign(&mut self, rhs: T) {
        self.poly *= rhs;
        self.reduce();
    }
}
impl MulAssign<&PolyOverZq> for PolynomialRingZq {
    /// Documentation at [`PolynomialRingZq::mul_assign`].
    ///
    /// # Panics ...
    /// - if the moduli are different.
    fn mul_assign(&mut self, other: &PolyOverZq) {
        if !self.compare_base(other) {
            panic!("{}", self.call_compare_base_error(other).unwrap())
        }
        // get a fmpz_poly_struct from a fmpz_mod_poly_struct
        let other = other.get_representative_least_nonnegative_residue();

        unsafe {
            fq_mul(
                &mut self.poly.poly,
                &self.poly.poly,
                &other.poly,
                self.modulus.get_fq_ctx(),
            );
        };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(
    MulAssign,
    mul_assign,
    PolynomialRingZq,
    PolynomialRingZq
);
arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, PolynomialRingZq, PolyOverZq);

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
    /// let c: PolynomialRingZq = &a * &b;
    /// let d: PolynomialRingZq = a * b;
    /// let e: PolynomialRingZq = &c * d;
    /// let f: PolynomialRingZq = c * &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli of both [`PolynomialRingZq`] mismatch.
    fn mul(self, other: Self) -> Self::Output {
        self.mul_safe(other).unwrap()
    }
}

impl Mul<&PolyOverZ> for &PolynomialRingZq {
    type Output = PolynomialRingZq;
    /// Implements the [`Mul`] trait for [`PolynomialRingZq`] and [`PolyOverZ`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to multiply to `self`
    ///
    /// Returns the product of both polynomials as a [`PolynomialRingZq`].
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
    /// let c: PolynomialRingZq = &a * &b;
    /// ```
    fn mul(self, other: &PolyOverZ) -> Self::Output {
        let mut out = PolynomialRingZq::from((&PolyOverZ::default(), &self.modulus));
        unsafe {
            fq_mul(
                &mut out.poly.poly,
                &self.poly.poly,
                &other.poly,
                self.modulus.get_fq_ctx(),
            );
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, PolyOverZ, PolynomialRingZq, PolynomialRingZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolynomialRingZq, PolyOverZ, PolynomialRingZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZ, PolynomialRingZq, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolynomialRingZq, PolyOverZ, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZ, PolynomialRingZq, PolynomialRingZq);

impl Mul<&PolyOverZq> for &PolynomialRingZq {
    type Output = PolynomialRingZq;
    /// Implements the [`Mul`] trait for [`PolynomialRingZq`] and [`PolyOverZq`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to multiply to `self`
    ///
    /// Returns the product of both polynomials as a [`PolynomialRingZq`].
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
    /// let c: PolynomialRingZq = &a * &b;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli mismatch.
    fn mul(self, other: &PolyOverZq) -> Self::Output {
        if !self.compare_base(other) {
            panic!("{}", self.call_compare_base_error(other).unwrap())
        }

        let mut out = PolynomialRingZq::from((&PolyOverZ::default(), &self.modulus));
        unsafe {
            fq_mul(
                &mut out.poly.poly,
                &self.poly.poly,
                &other.get_representative_least_nonnegative_residue().poly,
                self.modulus.get_fq_ctx(),
            );
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, PolyOverZq, PolynomialRingZq, PolynomialRingZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolynomialRingZq, PolyOverZq, PolynomialRingZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZq, PolynomialRingZq, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolynomialRingZq, PolyOverZq, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZq, PolynomialRingZq, PolynomialRingZq);

impl PolynomialRingZq {
    /// Implements multiplication for two [`PolynomialRingZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to multiply to `self`
    ///
    /// Returns the product of both polynomials as a [`PolynomialRingZq`] or an error if the moduli
    /// mismatch.
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
    /// let c: PolynomialRingZq = a.mul_safe(&b).unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    ///   both [`PolynomialRingZq`] mismatch.
    pub fn mul_safe(&self, other: &Self) -> Result<PolynomialRingZq, MathError> {
        if !self.compare_base(other) {
            return Err(self.call_compare_base_error(other).unwrap());
        }
        let mut out = PolynomialRingZq::from((&PolyOverZ::default(), &self.modulus));
        unsafe {
            fq_mul(
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
mod test_mul_assign {
    use super::PolyOverZ;
    use crate::integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq};
    use std::str::FromStr;

    /// Ensure that `mul_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let mut a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));

        a *= b;

        assert_eq!(
            a,
            PolynomialRingZq::from((&PolyOverZ::from_str("3  15 14 12").unwrap(), &modulus))
        );
    }

    /// Ensure that `mul_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "4  {} 0 0 {} mod {}",
            u64::MAX,
            i64::MIN,
            u64::MAX - 58
        ))
        .unwrap();

        let poly_1 = PolyOverZ::from_str(&format!("3  {} 0 {}", u64::MAX, i64::MIN)).unwrap();
        let mut a = PolynomialRingZq::from((&poly_1, &modulus));

        let poly_2 = PolyOverZ::from_str(&format!("3  {} 0 {}", i64::MAX, i64::MAX)).unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));

        a *= b;

        assert_eq!(
            a,
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

    /// Ensure that `mul_assign` is available for all types.
    #[test]
    fn availability() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let mut a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = PolyOverZq::from((poly_2, 17));

        a *= &b;
        a *= b;
        a *= &poly_1;
        a *= poly_1;
        a *= &c;
        a *= c;
    }

    /// Ensures that mismatching moduli result in a panic.
    #[test]
    #[should_panic]
    fn mismatching_moduli() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let mut a = PolynomialRingZq::from((&poly_1, &modulus));
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));

        a *= b;
    }
}

#[cfg(test)]
mod test_mul {
    use crate::integer::PolyOverZ;
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use crate::integer_mod_q::PolynomialRingZq;
    use std::str::FromStr;

    /// Testing multiplication for two [`PolynomialRingZq`]
    #[test]
    fn mul() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = a * b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("3  15 14 12").unwrap(), &modulus))
        );
    }

    /// Testing multiplication for two borrowed [`PolynomialRingZq`]
    #[test]
    fn mul_borrow() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = &a * &b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("3  15 14 12").unwrap(), &modulus))
        );
    }

    /// Testing multiplication for borrowed [`PolynomialRingZq`] and [`PolynomialRingZq`]
    #[test]
    fn mul_first_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = &a * b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("3  15 14 12").unwrap(), &modulus))
        );
    }

    /// Testing multiplication for [`PolynomialRingZq`] and borrowed [`PolynomialRingZq`]
    #[test]
    fn mul_second_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = a * &b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("3  15 14 12").unwrap(), &modulus))
        );
    }

    /// Testing multiplication for [`PolynomialRingZq`] with constant
    #[test]
    fn mul_constant() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let poly_2 = PolyOverZ::from(3);
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let c = &a * b;
        assert_eq!(
            c,
            PolynomialRingZq::from((&PolyOverZ::from_str("4  -3 0 3 3").unwrap(), &modulus))
        );
        assert_eq!(
            PolynomialRingZq::from((&PolyOverZ::default(), &modulus)),
            a * PolynomialRingZq::from((&PolyOverZ::default(), &modulus))
        )
    }

    /// Testing multiplication for large [`PolynomialRingZq`]
    #[test]
    fn mul_large_numbers() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "4  {} 0 0 {} mod {}",
            u64::MAX,
            i64::MIN,
            u64::MAX - 58
        ))
        .unwrap();

        let poly_1 = PolyOverZ::from_str(&format!("3  {} 0 {}", u64::MAX, i64::MIN)).unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));

        let poly_2 = PolyOverZ::from_str(&format!("3  {} 0 {}", i64::MAX, i64::MAX)).unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));

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

    /// Testing multiplication for [`PolynomialRingZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn mul_mismatching_modulus() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));
        let _ = a * b;
    }

    /// Testing whether mul_safe throws an error for mismatching moduli
    #[test]
    fn mul_safe_is_err() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_1 = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
        let a = PolynomialRingZq::from((&poly_1, &modulus));
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_2 = PolyOverZ::from_str("4  2 0 3 1").unwrap();
        let b = PolynomialRingZq::from((&poly_2, &modulus));

        assert!(&a.mul_safe(&b).is_err());
    }
}

#[cfg(test)]
mod test_mul_poly_over_z {
    use super::PolynomialRingZq;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 =
            PolynomialRingZq::from_str(&format!("2  2 {} / 4  1 2 3 4 mod {}", i64::MAX, u64::MAX))
                .unwrap();
        let poly_2 = PolynomialRingZq::from_str(&format!(
            "3  2 {} {} / 4  1 2 3 4 mod {}",
            i64::MAX as u64 + 4,
            (i64::MAX as u64) * 2,
            u64::MAX
        ))
        .unwrap();
        let poly = PolyOverZ::from_str("2  1 2").unwrap();

        let poly_1 = &poly_1 * &poly;

        assert_eq!(poly_2, poly_1);
    }

    /// Checks if scalar multiplication works fine for different types
    #[test]
    fn availability() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let z = PolyOverZ::from(2);

        _ = poly.clone() * z.clone();
        _ = z.clone() * poly.clone();
        _ = &poly * &z;
        _ = &z * &poly;
        _ = &poly * z.clone();
        _ = z.clone() * &poly;
        _ = &z * poly.clone();
        _ = poly.clone() * &z;
    }
}

#[cfg(test)]
mod test_mul_poly_over_zq {
    use super::PolynomialRingZq;
    use crate::integer_mod_q::PolyOverZq;
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 =
            PolynomialRingZq::from_str(&format!("2  2 {} / 4  1 2 3 4 mod {}", i64::MAX, u64::MAX))
                .unwrap();
        let poly_2 = PolynomialRingZq::from_str(&format!(
            "3  2 {} {} / 4  1 2 3 4 mod {}",
            i64::MAX as u64 + 4,
            (i64::MAX as u64) * 2,
            u64::MAX
        ))
        .unwrap();
        let poly = PolyOverZq::from_str(&format!("2  1 2 mod {}", u64::MAX)).unwrap();

        let poly_1 = &poly_1 * &poly;

        assert_eq!(poly_2, poly_1);
    }

    /// Checks if multiplication works fine for different types
    #[test]
    fn availability() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let zq = PolyOverZq::from((2, 17));

        _ = poly.clone() * zq.clone();
        _ = zq.clone() * poly.clone();
        _ = &poly * &zq;
        _ = &zq * &poly;
        _ = &poly * zq.clone();
        _ = zq.clone() * &poly;
        _ = &zq * poly.clone();
        _ = poly.clone() * &zq;
    }

    /// Checks if multiplication panics if the moduli mismatch
    #[test]
    #[should_panic]
    fn different_moduli_panic() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let zq = PolyOverZq::from((2, 16));

        _ = &poly * &zq;
    }
}
