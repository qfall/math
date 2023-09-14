// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the [`Distance`] trait for [`Zq`].

use super::Zq;
use crate::{error::MathError, integer::Z, traits::Distance};
use std::cmp::min;

impl Zq {
    /// Computes the absolute distance between two [`Zq`] instances. It returns the minimum
    /// distance across boundaries, i.e. `distance(1 mod 7, 6 mod 7) = 2` as `6 == -2 mod 7`.
    ///
    /// Parameters:
    /// - `other`: specifies one of the [`Zq`] values whose distance
    /// is calculated to `self`
    ///
    /// Returns the absolute minimum distance between the two given values as a new
    /// [`Z`] instance or a [`MathError`] if the moduli mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{
    ///     integer::Z,
    ///     integer_mod_q::Zq,
    /// };
    ///
    /// let a = Zq::from((-1, 13));
    /// let b = Zq::from((5, 13));
    ///
    /// let distance = a.distance_safe(&b).unwrap();
    ///
    /// assert_eq!(Z::from(6), distance);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`MismatchingModulus`](MathError::MismatchingModulus) if the
    /// provided moduli differ.
    pub fn distance_safe(&self, other: &Zq) -> Result<Z, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                "To compute the distance of two Zq elements, their moduli need to match. 
                The provided once were {} and {}.",
                self.modulus, other.modulus,
            )));
        }

        let distance_direct = self.value.distance(&other.value);
        let distance_across_modulus = Z::from(self.modulus.clone()) - &distance_direct;

        Ok(min(distance_direct, distance_across_modulus))
    }
}

impl Distance<&Zq> for Zq {
    type Output = Z;

    /// Computes the absolute distance between two [`Zq`] instances. It returns the minimum
    /// distance across boundaries, i.e. `distance(1 mod 7, 6 mod 7) = 2` as `6 == -2 mod 7`.
    ///
    /// Parameters:
    /// - `other`: specifies one of the [`Zq`] values whose distance
    /// is calculated to `self`.
    ///
    /// Returns the absolute minimum distance between the two given values as a new
    /// [`Z`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{
    ///     integer::Z,
    ///     integer_mod_q::Zq,
    ///     traits::*,
    /// };
    ///
    /// let a = Zq::from((-1, 13));
    /// let b = Zq::from((5, 13));
    ///
    /// let distance = a.distance(&b);
    ///
    /// assert_eq!(Z::from(6), distance);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided moduli mismatch.
    fn distance(&self, other: &Zq) -> Self::Output {
        self.distance_safe(other).unwrap()
    }
}

impl Distance<Zq> for Zq {
    type Output = Z;

    // This reference links to the correct distance implementation
    // just because the correct one is the first in this file.
    /// Just calls [`Zq::distance<&Zq>`].
    fn distance(&self, other: Zq) -> Self::Output {
        self.distance(&other)
    }
}

impl<Integer: Into<Z>> Distance<Integer> for Zq {
    type Output = Z;

    /// Computes the absolute distance between `self` and `other`.
    ///
    /// Parameters:
    /// - `other`: specifies one of the [`Zq`] values whose distance
    /// is calculated to `self`. The modulus from `self` will be used.
    ///
    /// Returns the absolute minimum distance between the two given values as a new
    /// [`Z`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{
    ///     integer::Z,
    ///     integer_mod_q::Zq,
    ///     traits::*,
    /// };
    ///
    /// let a = Zq::from((-1, 13));
    ///
    /// let distance_0 = a.distance(5);
    /// let distance_1 = a.distance(10);
    ///
    /// assert_eq!(Z::from(6), distance_0);
    /// assert_eq!(Z::from(2), distance_1);
    /// ```
    fn distance(&self, other: Integer) -> Self::Output {
        let other = Zq::from((&other.into(), &self.modulus));
        self.distance(&other)
    }
}

#[cfg(test)]
mod test_distance_safe {
    use super::{Zq, Z};

    /// Checks if distance_safe is correctly computed for small [`Zq`] values
    /// and whether distance(a, b) == distance(b, a) and distance(a, a) == 0
    #[test]
    fn small_values() {
        let a = Zq::from((1, 29));
        let b = Zq::from((-12, 29));
        let zero = Zq::from((0, 29));

        let res_0 = a.distance_safe(&zero).unwrap();
        let res_1 = zero.distance_safe(&a).unwrap();
        let res_2 = a.distance_safe(&b).unwrap();
        let res_3 = b.distance_safe(&a).unwrap();
        let res_4 = b.distance_safe(&zero).unwrap();
        let res_5 = zero.distance_safe(&b).unwrap();
        let res_6 = b.distance_safe(&b).unwrap();
        let res_7 = a.distance_safe(&a).unwrap();
        let res_8 = zero.distance_safe(&zero).unwrap();

        assert_eq!(Z::ONE, res_0);
        assert_eq!(Z::ONE, res_1);
        assert_eq!(Z::from(13), res_2);
        assert_eq!(Z::from(13), res_3);
        assert_eq!(Z::from(12), res_4);
        assert_eq!(Z::from(12), res_5);
        assert_eq!(Z::ZERO, res_6);
        assert_eq!(Z::ZERO, res_7);
        assert_eq!(Z::ZERO, res_8);
    }

    /// Checks if distance_safe is correctly computed for large [`Zq`] values
    /// and whether distance(a, b) == distance(b, a), and distance(a, a) == 0
    #[test]
    fn large_values() {
        let a = Zq::from((i64::MAX, u64::MAX));
        let b = Zq::from((i64::MIN, u64::MAX));
        let zero = Zq::from((0, u64::MAX));

        let res_0 = a.distance_safe(&b).unwrap();
        let res_1 = b.distance_safe(&a).unwrap();
        let res_2 = a.distance_safe(&zero).unwrap();
        let res_3 = zero.distance_safe(&a).unwrap();
        let res_4 = b.distance_safe(&zero).unwrap();
        let res_5 = zero.distance_safe(&b).unwrap();
        let res_6 = a.distance_safe(&a).unwrap();

        assert_eq!(Z::ZERO, res_0);
        assert_eq!(Z::ZERO, res_1);
        assert_eq!(Z::from(i64::MAX), res_2);
        assert_eq!(Z::from(i64::MAX), res_3);
        assert_eq!(Z::from(i64::MAX), res_4);
        assert_eq!(Z::from(i64::MAX), res_5);
        assert_eq!(Z::ZERO, res_6);
    }

    /// Check whether mismatching provided moduli result in an error
    #[test]
    fn mismatching_moduli() {
        let a = Zq::from((0, 17));
        let b = Zq::from((0, 19));

        assert!(a.distance_safe(&b).is_err());
    }
}

#[cfg(test)]
mod test_distance {
    use super::{Distance, Zq, Z};

    /// Check whether distance is available for owned [`Zq`] and other types
    #[test]
    fn availability() {
        let a = Zq::from((0, u64::MAX));
        let b = a.clone();

        let u_0 = a.distance(0_u8);
        let u_1 = a.distance(15_u16);
        let u_2 = a.distance(35_u32);
        let u_3 = a.distance(u64::MIN);
        let i_0 = a.distance(0_i8);
        let i_1 = a.distance(-15_i16);
        let i_2 = a.distance(35_i32);
        let i_3 = a.distance(i64::MIN);
        let borrowed = a.distance(&b);
        let owned = a.distance(b);

        assert_eq!(Z::ZERO, u_0);
        assert_eq!(Z::from(15), u_1);
        assert_eq!(Z::from(35), u_2);
        assert_eq!(Z::ZERO, u_3);
        assert_eq!(Z::ZERO, i_0);
        assert_eq!(Z::from(15), i_1);
        assert_eq!(Z::from(35), i_2);
        assert_eq!(Z::from(i64::MAX), i_3);
        assert_eq!(Z::ZERO, borrowed);
        assert_eq!(Z::ZERO, owned);
    }

    /// Check whether mismatching provided moduli result in a panic
    #[test]
    #[should_panic]
    fn mismatching_moduli() {
        let a = Zq::from((0, 17));
        let b = Zq::from((0, 19));

        let _ = a.distance(&b);
    }
}
