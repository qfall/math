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
        fmpz, fmpz_abs, fmpz_bits, fmpz_is_one, fmpz_is_prime, fmpz_is_zero, fmpz_mod, fmpz_tstbit,
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
    /// assert!(value.is_zero())
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
    /// assert!(value.is_one())
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
    /// assert!(value.is_prime())
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

    /// Computes `self` mod `modulus` as long as `modulus` is unequal to 0.
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
}

#[cfg(test)]
mod test_modulo {
    use super::Z;

    /// Ensures that `modulo` works properly for small and large positive integers
    /// and positive moduli
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
    /// and negative moduli
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
    /// and positive moduli
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
    /// and negative moduli
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
