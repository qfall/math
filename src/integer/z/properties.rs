// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`Z`] instances.

use super::Z;
use crate::rational::Q;
use flint_sys::{
    fmpq::{fmpq, fmpq_inv},
    fmpz::{
        fmpz, fmpz_abs, fmpz_bits, fmpz_is_one, fmpz_is_perfect_power, fmpz_is_prime, fmpz_is_zero,
        fmpz_mod, fmpz_tstbit,
    },
};

impl Z {
    /// Checks if a [`Z`] is `0`.
    ///
    /// Returns true if the value is `0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::ZERO;
    /// assert!(value.is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        1 == unsafe { fmpz_is_zero(&self.value) }
    }

    /// Checks if a [`Z`] is `1`.
    ///
    /// Returns true if the value is `1`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::ONE;
    /// assert!(value.is_one());
    /// ```
    pub fn is_one(&self) -> bool {
        1 == unsafe { fmpz_is_one(&self.value) }
    }

    /// Checks if a [`Z`] is prime.
    ///
    /// Returns true if the value is prime.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(17);
    /// assert!(value.is_prime());
    /// ```
    pub fn is_prime(&self) -> bool {
        1 == unsafe { fmpz_is_prime(&self.value) }
    }

    /// Returns the given [`Z`] instance with its absolute value.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let mut value = Z::from(-1);
    ///
    /// let value = value.abs();
    ///
    /// assert_eq!(Z::ONE, value);
    /// ```
    pub fn abs(mut self) -> Self {
        unsafe {
            fmpz_abs(&mut self.value, &self.value);
        }
        self
    }

    /// Returns the inverse of `self` as a fresh [`Q`] instance.
    ///
    /// As the inverse of `0` is undefined, it returns `None` in case `self == 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::Z, rational::Q};
    /// let value = Z::from(4);
    ///
    /// let inverse = value.inverse().unwrap();
    ///
    /// assert_eq!(Q::from((1, 4)), inverse);
    /// ```
    pub fn inverse(&self) -> Option<Q> {
        if self == &Z::ZERO {
            return None;
        }

        let mut out = Q::ZERO;
        // the manual construction of fmpq removes the need to clone self's value/
        // the numerator. the new fmpz value does not need to be cleared manually
        // as it's small the fmpq instance does neither as the fmpq value is
        // dropped automatically, but the numerator/ self's value is kept alive
        let self_fmpq = fmpq {
            num: self.value,
            den: fmpz(1),
        };
        unsafe { fmpq_inv(&mut out.value, &self_fmpq) };
        Some(out)
    }

    /// Computes the number of bits needed to store the absolute value of `self`.
    ///
    /// The number of bits needs to fit into an [`u64`],
    /// i.e. the size should not exceed `2^(2^64)`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let value = Z::from(4);
    ///
    /// let nr_bits = value.bits();
    ///
    /// assert_eq!(3, nr_bits);
    /// ```
    pub fn bits(&self) -> u64 {
        unsafe { fmpz_bits(&self.value) }
    }

    /// Computes the [`Vec`] of [`bool`] bits corresponding
    /// to the bits of the absolute value of `self`.
    ///
    /// The first bit is the least significant bit.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let value = Z::from(4);
    ///
    /// let vec_bits = value.to_bits();
    ///
    /// assert_eq!(vec![false, false, true], vec_bits);
    /// ```
    pub fn to_bits(&self) -> Vec<bool> {
        // compute absolute value
        let value = self.clone().abs();
        // resulting bit-vector
        let mut bits = vec![];
        for i in 0..value.bits() {
            // get i-th bit of value
            let bit_i = unsafe { fmpz_tstbit(&value.value, i) };
            // appends i-th bit to vector
            if bit_i == 0 {
                bits.push(false);
            } else {
                bits.push(true);
            }
        }

        bits
    }

    /// Computes `self` mod `modulus` as long as `modulus` is unequal to 0.
    /// For negative values, the smallest positive representative is returned.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    /// over which the positive remainder is computed
    ///
    /// Returns `self` mod `modulus` as a [`Z`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let value = Z::from(5);
    ///
    /// let value_mod_two = value.modulo(2);
    ///
    /// assert_eq!(Z::ONE, value_mod_two);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is 0.
    pub fn modulo(&self, modulus: impl Into<Z>) -> Self {
        let modulus = modulus.into();
        assert!(modulus != Z::ZERO, "Modulus can not be 0.");
        let mut out = Z::default();
        unsafe { fmpz_mod(&mut out.value, &self.value, &modulus.value) };
        out
    }

    /// Computes a pair `(root, exp)` s.t. `root^exp = self`
    /// if `self` is a perfect power and can be represented via `root.pow(exp)`.
    ///
    /// This algorithm tries to find the smallest perfect root,
    /// but there is no formal guarantee to find it.
    ///
    /// Returns a pair `(root, exp)` if `root.pow(exp) = self` exists. Otherwise,
    /// `None` is returned.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let value = Z::from(16);
    ///
    /// let (root, exp) = value.is_perfect_power().unwrap();
    ///
    /// assert_eq!(root, Z::from(2));
    /// assert_eq!(exp, 4);
    /// ```
    pub fn is_perfect_power(&self) -> Option<(Self, i32)> {
        let mut root = Z::default();
        let exp = unsafe { fmpz_is_perfect_power(&mut root.value, &self.value) };
        if root.is_zero() && exp == 0 {
            return None;
        }
        Some((root, exp))
    }
}

#[cfg(test)]
mod test_is_perfect_power {
    use super::Z;
    use crate::traits::Pow;

    /// Ensures that positive small values for root 2 are correctly dissembled.
    #[test]
    fn positive_small_2() {
        let x = Z::from(32);

        let (root, exp) = x.is_perfect_power().unwrap();

        assert_eq!(root, Z::from(2));
        assert_eq!(exp, 5);
    }

    /// Ensures that positive small values for root 5 are correctly dissembled.
    #[test]
    fn positive_small_5() {
        let x = Z::from(25);

        let (root, exp) = x.is_perfect_power().unwrap();

        assert_eq!(root, Z::from(5));
        assert_eq!(exp, 2);
    }

    /// Ensures that positive small values non perfect powers return None.
    #[test]
    fn positive_small_non_perfect_power() {
        let x = Z::from(26);

        let result = x.is_perfect_power();

        assert!(result.is_none());
    }

    /// Ensures that positive large values for root 2 are correctly dissembled.
    #[test]
    fn positive_large_2() {
        let x = Z::from(i64::MAX as u64 + 1);

        let (root, exp) = x.is_perfect_power().unwrap();

        assert_eq!(root, Z::from(2));
        assert_eq!(exp, 63);
    }

    /// Ensures that positive large values for root 5 are correctly dissembled.
    #[test]
    fn positive_large_5() {
        let x = Z::from(5).pow(67).unwrap();

        let (root, exp) = x.is_perfect_power().unwrap();

        assert_eq!(root, Z::from(5));
        assert_eq!(exp, 67);
    }

    /// Ensures that positive large values for 25^50 are correctly dissembled.
    #[test]
    fn positive_large_25() {
        let x = Z::from(25).pow(50).unwrap();

        let (root, exp) = x.is_perfect_power().unwrap();

        assert_eq!(root, Z::from(5));
        assert_eq!(exp, 100);
    }

    /// Ensures that positive large values non perfect powers return None.
    #[test]
    fn positive_large_non_perfect_power() {
        let x = Z::from(i64::MAX);

        let result = x.is_perfect_power();

        assert!(result.is_none());
    }

    /// Ensures that zero is correctly dissembled.
    #[test]
    fn zero() {
        let x = Z::ZERO;

        let (root, exp) = x.is_perfect_power().unwrap();

        assert!(root.is_zero());
        assert!(exp > 0);
    }

    /// Ensures that negative small values for root -2 are correctly dissembled.
    #[test]
    fn negative_small_2() {
        let x = Z::from(-32);

        let (root, exp) = x.is_perfect_power().unwrap();

        assert_eq!(root, Z::from(-2));
        assert_eq!(exp, 5);
    }

    /// Ensures that negative small values for root -5 are correctly dissembled.
    #[test]
    fn negative_small_5() {
        let x = Z::from(-125);

        let (root, exp) = x.is_perfect_power().unwrap();

        assert_eq!(root, Z::from(-5));
        assert_eq!(exp, 3);
    }

    /// Ensures that negative small values non perfect powers return None.
    #[test]
    fn negative_small_non_perfect_power() {
        let x = Z::from(-26);

        let result = x.is_perfect_power();

        assert!(result.is_none());
    }

    /// Ensures that negative large values for root -2 are correctly dissembled.
    #[test]
    fn negative_large_2() {
        let x = Z::from(i64::MIN);

        let (root, exp) = x.is_perfect_power().unwrap();

        assert_eq!(root, Z::from(-2));
        assert_eq!(exp, 63);
    }

    /// Ensures that negative large values for root -5 are correctly dissembled.
    #[test]
    fn negative_large_5() {
        let x = Z::from(-5).pow(67).unwrap();

        let (root, exp) = x.is_perfect_power().unwrap();

        assert_eq!(root, Z::from(-5));
        assert_eq!(exp, 67);
    }

    /// Ensures that negative large values for root -25 are correctly dissembled.
    #[test]
    fn negative_large_25() {
        let x = Z::from(-25).pow(67).unwrap();

        let (root, exp) = x.is_perfect_power().unwrap();

        assert_eq!(root, Z::from(-25));
        assert_eq!(exp, 67);
    }

    /// Ensures that negative large values non perfect powers return None.
    #[test]
    fn negative_large_non_perfect_power() {
        let x = Z::from(i64::MIN + 1);

        let result = x.is_perfect_power();

        assert!(result.is_none());
    }
}

#[cfg(test)]
mod test_modulo {
    use super::Z;

    /// Ensures that `modulo` works properly for small and large positive integers
    /// and positive moduli.
    #[test]
    fn positive_value_positive_modulus() {
        let value_0: i64 = 15;
        let value_1: i64 = i64::MAX;
        let mod_0: i64 = 2;
        let mod_1: i64 = 15;

        assert_eq!(
            Z::from(value_0.rem_euclid(mod_0)),
            Z::from(value_0).modulo(mod_0)
        );
        assert_eq!(
            Z::from(value_1.rem_euclid(mod_0)),
            Z::from(value_1).modulo(mod_0)
        );
        assert_eq!(
            Z::from(value_0.rem_euclid(mod_1)),
            Z::from(value_0).modulo(mod_1)
        );
        assert_eq!(
            Z::from(value_1.rem_euclid(mod_1)),
            Z::from(value_1).modulo(mod_1)
        );
    }

    /// Ensures that `modulo` works properly for small and large positive integers
    /// and negative moduli.
    #[test]
    fn positive_value_negative_modulus() {
        let value_0: i64 = 15;
        let value_1: i64 = i64::MAX;
        let mod_0: i64 = -2;
        let mod_1: i64 = -15;

        assert_eq!(
            Z::from(value_0.rem_euclid(mod_0)),
            Z::from(value_0).modulo(mod_0)
        );
        assert_eq!(
            Z::from(value_1.rem_euclid(mod_0)),
            Z::from(value_1).modulo(mod_0)
        );
        assert_eq!(
            Z::from(value_0.rem_euclid(mod_1)),
            Z::from(value_0).modulo(mod_1)
        );
        assert_eq!(
            Z::from(value_1.rem_euclid(mod_1)),
            Z::from(value_1).modulo(mod_1)
        );
    }

    /// Ensures that `modulo` works properly for small and large negative integers
    /// and positive moduli.
    #[test]
    fn negative_value_positive_modulus() {
        let value_0: i64 = -15;
        let value_1: i64 = i64::MIN;
        let mod_0: i64 = 2;
        let mod_1: i64 = 15;

        assert_eq!(
            Z::from(value_0.rem_euclid(mod_0)),
            Z::from(value_0).modulo(mod_0)
        );
        assert_eq!(
            Z::from(value_1.rem_euclid(mod_0)),
            Z::from(value_1).modulo(mod_0)
        );
        assert_eq!(
            Z::from(value_0.rem_euclid(mod_1)),
            Z::from(value_0).modulo(mod_1)
        );
        assert_eq!(
            Z::from(value_1.rem_euclid(mod_1)),
            Z::from(value_1).modulo(mod_1)
        );
    }

    /// Ensures that `modulo` works properly for small and large negative integers
    /// and negative moduli.
    #[test]
    fn negative_value_negative_modulus() {
        let value_0: i64 = -15;
        let value_1: i64 = i64::MIN;
        let mod_0: i64 = -2;
        let mod_1: i64 = -15;

        assert_eq!(
            Z::from(value_0.rem_euclid(mod_0)),
            Z::from(value_0).modulo(mod_0)
        );
        assert_eq!(
            Z::from(value_1.rem_euclid(mod_0)),
            Z::from(value_1).modulo(mod_0)
        );
        assert_eq!(
            Z::from(value_0.rem_euclid(mod_1)),
            Z::from(value_0).modulo(mod_1)
        );
        assert_eq!(
            Z::from(value_1.rem_euclid(mod_1)),
            Z::from(value_1).modulo(mod_1)
        );
    }

    /// Ensures that the result is equal for the same positive and negative modulus.
    #[test]
    fn result_positive_negative_modulus_equal() {
        let value: i64 = 17;
        let mod_0: i64 = 3;
        let mod_1: i64 = -3;
        let cmp_0 = Z::from(value.rem_euclid(mod_0));
        let cmp_1 = Z::from(value.rem_euclid(mod_1));

        let res_0 = Z::from(value).modulo(mod_0);
        let res_1 = Z::from(value).modulo(mod_1);

        // values correct
        assert_eq!(cmp_0, res_0);
        assert_eq!(cmp_1, res_1);
        // values equal for negative and positive modulus
        assert_eq!(res_0, res_1);
    }

    /// Ensures that `modulo` is available for several types implementing [`Into<Z>`].
    #[test]
    fn availability() {
        let _ = Z::ONE.modulo(1u8);
        let _ = Z::ONE.modulo(1u16);
        let _ = Z::ONE.modulo(1u32);
        let _ = Z::ONE.modulo(1u64);
        let _ = Z::ONE.modulo(1i8);
        let _ = Z::ONE.modulo(1i16);
        let _ = Z::ONE.modulo(1i32);
        let _ = Z::ONE.modulo(1i64);
        let _ = Z::ONE.modulo(Z::ONE);
    }

    /// Ensures that computing modulo 0 results in a panic.
    #[test]
    #[should_panic]
    fn zero_modulus() {
        Z::from(15).modulo(0);
    }
}

#[cfg(test)]
mod test_to_bits {
    use super::Z;

    /// Ensures that `to_bits` works properly for small and large positive integer values.
    #[test]
    fn positive() {
        let value_0 = Z::from(16);
        let value_1 = Z::from(u64::MAX);

        let res_0 = value_0.to_bits();
        let res_1 = value_1.to_bits();

        assert_eq!(vec![false, false, false, false, true], res_0);
        assert_eq!(vec![true; 64], res_1);
    }

    /// Ensures that `to_bits` works properly for zero.
    #[test]
    fn zero() {
        let value = Z::ZERO;
        let cmp: Vec<bool> = vec![];

        let res = value.to_bits();

        assert_eq!(cmp, res);
    }

    /// Ensures that `to_bits` works properly for small and large negative integer values.
    #[test]
    fn negative() {
        let value_0 = Z::from(-13);
        let value_1 = Z::from(i64::MIN);
        let mut cmp = vec![false; 63];
        cmp.push(true);

        let res_0 = value_0.to_bits();
        let res_1 = value_1.to_bits();

        assert_eq!(vec![true, false, true, true], res_0);
        assert_eq!(cmp, res_1);
    }
}

#[cfg(test)]
mod test_bits {
    use super::Z;

    /// Checks whether the number of bits needed to store the absolute value
    /// is output correctly for small values.
    #[test]
    fn small_values() {
        assert_eq!(0, Z::ZERO.bits());
        assert_eq!(1, Z::ONE.bits());
        assert_eq!(1, Z::MINUS_ONE.bits());
        assert_eq!(3, Z::from(4).bits());
        assert_eq!(31, Z::from(i32::MAX).bits());
        assert_eq!(32, Z::from(i32::MIN).bits());
        assert_eq!(32, Z::from(u32::MAX).bits());
    }

    /// Checks whether the number of bits needed to store the absolute value
    /// is output correctly for large values.
    #[test]
    fn large_values() {
        let vector = vec![255; 16];
        let large = Z::from_bytes(&vector);

        assert_eq!(128, large.bits());
        assert_eq!(63, Z::from(i64::MAX).bits());
        assert_eq!(64, Z::from(i64::MIN).bits());
        assert_eq!(64, Z::from(u64::MAX).bits());
    }
}

#[cfg(test)]
mod test_abs {
    use super::Z;

    /// Checks whether `abs` returns the positive value for small values correctly.
    #[test]
    fn small_values() {
        let pos = Z::ONE;
        let zero = Z::ZERO;
        let neg = Z::from(-15);

        assert_eq!(Z::ONE, pos.abs());
        assert_eq!(Z::ZERO, zero.abs());
        assert_eq!(Z::from(15), neg.abs());
    }

    /// Checks whether `abs` returns the positive value for large values correctly.
    #[test]
    fn large_values() {
        let pos = Z::from(i64::MAX);
        let neg = Z::from(i64::MIN);

        assert_eq!(Z::from(i64::MAX), pos.abs());
        assert_eq!(Z::from(i64::MIN) * Z::from(-1), neg.abs());
    }
}

#[cfg(test)]
mod test_is_prime {
    use super::Z;

    /// Ensure that primes are correctly detected
    #[test]
    fn prime_detection() {
        let small = Z::from(2_i32.pow(16) + 1);
        let large = Z::from(u64::MAX - 58);
        assert!(small.is_prime());
        assert!(large.is_prime());
    }

    /// Ensure that non-primes are correctly detected
    #[test]
    fn non_prime_detection() {
        let small = Z::from(2_i32.pow(16));
        let large = Z::from(i64::MAX);
        assert!(!small.is_prime());
        assert!(!large.is_prime());
    }
}

#[cfg(test)]
mod test_inv {
    use super::{Q, Z};

    /// Checks whether the inverse is correctly computed for small values.
    #[test]
    fn small_values() {
        let val_0 = Z::from(4);
        let val_1 = Z::from(-7);

        let inv_0 = val_0.inverse().unwrap();
        let inv_1 = val_1.inverse().unwrap();

        assert_eq!(Q::from((1, 4)), inv_0);
        assert_eq!(Q::from((-1, 7)), inv_1);
    }

    /// Checks whether the inverse is correctly computed for large values.
    #[test]
    fn large_values() {
        let val_0 = Z::from(i64::MAX);
        let val_1 = Z::from(i64::MIN);

        let inv_0 = val_0.inverse().unwrap();
        let inv_1 = val_1.inverse().unwrap();

        assert_eq!(Q::from((1, i64::MAX)), inv_0);
        assert_eq!(Q::from((1, i64::MIN)), inv_1);
    }

    /// Checks whether the inverse of `0` returns `None`.
    #[test]
    fn inv_zero_none() {
        let zero = Z::ZERO;

        let inv_zero = zero.inverse();

        assert!(inv_zero.is_none());
    }
}

#[cfg(test)]
mod test_is_zero {
    use super::Z;
    use std::str::FromStr;

    /// Ensure that is_zero returns `true` for `0`.
    #[test]
    fn zero_detection() {
        let zero = Z::ZERO;

        assert!(zero.is_zero());
    }

    /// Ensure that is_zero returns `false` for non-zero values.
    #[test]
    fn zero_rejection() {
        let small = Z::from(2);
        let large = Z::from_str(&format!("{}", (u128::MAX - 1) / 2 + 1)).unwrap();

        assert!(!small.is_zero());
        assert!(!large.is_zero());
    }
}

#[cfg(test)]
mod test_is_one {
    use super::Z;
    use std::str::FromStr;

    /// Ensure that is_one returns `true` for `1`.
    #[test]
    fn one_detection() {
        let zero = Z::ONE;

        assert!(zero.is_one());
    }

    /// Ensure that is_one returns `false` for other values.
    #[test]
    fn one_rejection() {
        let small = Z::from(2);
        let large = Z::from_str(&format!("{}", (u128::MAX - 1) / 2 + 2)).unwrap();

        assert!(!small.is_one());
        assert!(!large.is_one());
    }
}
