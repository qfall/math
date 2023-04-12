// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the [`Distance`] trait for [`Zq`].

use super::Zq;
use crate::{integer::Z, macros::for_others::implement_for_owned, traits::Distance};

impl Distance<&Zq> for Zq {
    type Output = Z;

    /// Computes the absolute distance between two [`Zq`] instances.
    ///
    /// Parameters:
    /// - `other`: specifies one of the [`Zq`] values whose distance
    /// is calculated to `self`
    ///
    /// Returns the absolute difference, i.e. distance between the two given [`Zq`]
    /// instances as a new [`Z`] instance.
    ///
    /// # Example
    /// ```
    /// use qfall_math::{
    ///     integer::Z,
    ///     integer_mod_q::Zq,
    ///     traits::*,
    /// };
    ///
    /// let a = Zq::try_from((-1, 13)).unwrap();
    /// let b = Zq::try_from((5, 13)).unwrap();
    ///
    /// let distance = a.distance(&b);
    ///
    /// assert_eq!(Z::from(6), distance);
    /// ```
    fn distance(&self, other: &Zq) -> Self::Output {
        let distance_direct = self.value.distance(&other.value);
        let distance_across_modulus = Z::from(self.modulus.clone()) - &distance_direct;

        if distance_direct < distance_across_modulus {
            distance_direct
        } else {
            distance_across_modulus
        }
    }
}

impl<T: Into<Z> + Copy> Distance<T> for Zq {
    type Output = Z;

    /// Computes the absolute distance between two [`Zq`] instances.
    ///
    /// Parameters:
    /// - `other`: specifies one of the [`Zq`] values whose distance
    /// is calculated to `self`
    ///
    /// Returns the absolute difference, i.e. distance between the two given [`Zq`]
    /// instances as a new [`Z`] instance.
    ///
    /// # Example
    /// ```
    /// use qfall_math::{
    ///     integer::Z,
    ///     integer_mod_q::Zq,
    ///     traits::*,
    /// };
    ///
    /// let a = Zq::try_from((-1, 13)).unwrap();
    ///
    /// let distance_0 = a.distance(5);
    /// let distance_1 = a.distance(10);
    ///
    /// assert_eq!(Z::from(6), distance_0);
    /// assert_eq!(Z::from(2), distance_1);
    /// ```
    fn distance(&self, other: T) -> Self::Output {
        let other = Zq::from_z_modulus(&other.into(), &self.modulus.clone());
        self.distance(&other)
    }
}

implement_for_owned!(Z, Zq, Distance);

#[cfg(test)]
mod test_distance {
    use super::{Distance, Zq, Z};

    /// Checks if distance is correctly computed for small [`Zq`] values
    /// and whether distance(a,b) == distance(b,a), distance(a,a) == 0
    #[test]
    fn small_values() {
        let a = Zq::try_from((1, 29)).unwrap();
        let b = Zq::try_from((-12, 29)).unwrap();
        let zero = Zq::try_from((0, 29)).unwrap();

        assert_eq!(Z::ONE, a.distance(&zero));
        assert_eq!(Z::ONE, zero.distance(&a));
        assert_eq!(Z::from(13), a.distance(&b));
        assert_eq!(Z::from(13), b.distance(&a));
        assert_eq!(Z::from(12), b.distance(&zero));
        assert_eq!(Z::from(12), zero.distance(&b));
        assert_eq!(Z::ZERO, b.distance(&b));
        assert_eq!(Z::ZERO, a.distance(&a));
        assert_eq!(Z::ZERO, zero.distance(&zero));
    }

    /// Checks if distance is correctly computed for large [`Zq`] values
    /// and whether distance(a,b) == distance(b,a), distance(a,a) == 0
    #[test]
    fn large_values() {
        let a = Zq::try_from((i64::MAX, u64::MAX)).unwrap();
        let b = Zq::try_from((i64::MIN, u64::MAX)).unwrap();
        let zero = Zq::try_from((0, u64::MAX)).unwrap();

        assert_eq!(Z::ZERO, a.distance(&b));
        assert_eq!(Z::ZERO, b.distance(&a));
        assert_eq!(Z::from(i64::MAX), a.distance(&zero));
        assert_eq!(Z::from(i64::MAX), zero.distance(&a));
        assert_eq!(Z::from(i64::MAX), b.distance(&zero));
        assert_eq!(Z::from(i64::MAX), zero.distance(&b));
        assert_eq!(Z::ZERO, a.distance(&a));
    }

    /// Check whether distance is available for owned [`Zq`] and other types
    #[test]
    fn availability() {
        let a = Zq::try_from((0, u64::MAX)).unwrap();

        let u_0 = a.distance(0_u8);
        let u_1 = a.distance(15_u16);
        let u_2 = a.distance(35_u32);
        let u_3 = a.distance(u64::MIN);
        let i_0 = a.distance(0_i8);
        let i_1 = a.distance(-15_i16);
        let i_2 = a.distance(35_i32);
        let i_3 = a.distance(i64::MIN);

        assert_eq!(Z::ZERO, u_0);
        assert_eq!(Z::from(15), u_1);
        assert_eq!(Z::from(35), u_2);
        assert_eq!(Z::ZERO, u_3);
        assert_eq!(Z::ZERO, i_0);
        assert_eq!(Z::from(15), i_1);
        assert_eq!(Z::from(35), i_2);
        assert_eq!(Z::from(i64::MAX), i_3);
    }
}
