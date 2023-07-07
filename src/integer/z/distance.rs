// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the [`Distance`] trait for [`Z`].

use super::Z;
use crate::traits::Distance;

impl<Integer: Into<Z>> Distance<Integer> for Z {
    type Output = Z;

    /// Computes the absolute distance between two [`Z`] instances.
    ///
    /// Parameters:
    /// - `other`: specifies one of the [`Z`] values whose distance
    /// is calculated to `self`
    ///
    /// Returns the absolute difference, i.e. distance between the two given [`Z`]
    /// instances as a new [`Z`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::traits::*;
    ///
    /// let a = Z::from(-1);
    /// let b = Z::from(10);
    ///
    /// let distance_0 = a.distance(5);
    /// let distance_1 = a.distance(10);
    ///
    /// # assert_eq!(Z::from(6), distance_0);
    /// # assert_eq!(Z::from(11), distance_1);
    /// ```
    fn distance(&self, other: Integer) -> Self::Output {
        let other = other.into();
        let difference = other - self;
        difference.abs()
    }
}

#[cfg(test)]
mod test_distance {
    use crate::integer_mod_q::Modulus;

    use super::{Distance, Z};

    /// Checks if distance is correctly computed for small [`Z`] values
    /// and whether distance(a, b) == distance(b, a), distance(a, a) == 0
    #[test]
    fn small_values() {
        let a = Z::ONE;
        let b = Z::from(-15);
        let zero = Z::ZERO;

        assert_eq!(Z::ONE, a.distance(&zero));
        assert_eq!(Z::ONE, zero.distance(&a));
        assert_eq!(Z::from(16), a.distance(&b));
        assert_eq!(Z::from(16), b.distance(&a));
        assert_eq!(Z::from(15), b.distance(&zero));
        assert_eq!(Z::from(15), zero.distance(&b));
        assert_eq!(Z::ZERO, b.distance(&b))
    }

    /// Checks if distance is correctly computed for large [`Z`] values
    /// and whether distance(a, b) == distance(b, a), distance(a, a) == 0
    #[test]
    fn large_values() {
        let a = Z::from(i64::MAX);
        let b = Z::from(i64::MIN);
        let zero = Z::ZERO;

        assert_eq!(&a - &b, a.distance(&b));
        assert_eq!(&a - &b, b.distance(&a));
        assert_eq!(a, a.distance(&zero));
        assert_eq!(a, zero.distance(&a));
        assert_eq!(&a + Z::ONE, b.distance(&zero));
        assert_eq!(&a + Z::ONE, zero.distance(&b));
        assert_eq!(Z::ZERO, a.distance(&a));
    }

    /// Check whether distance is available for owned [`Z`] and other types
    #[test]
    fn availability() {
        let a = Z::ZERO;
        let modulus = Modulus::from(2);

        let u_0 = a.distance(0_u8);
        let u_1 = a.distance(15_u16);
        let u_2 = a.distance(35_u32);
        let u_3 = a.distance(u64::MAX);
        let i_0 = a.distance(0_i8);
        let i_1 = a.distance(-15_i16);
        let i_2 = a.distance(35_i32);
        let i_3 = a.distance(i64::MIN);
        let dist_mod = a.distance(modulus);

        assert_eq!(Z::ZERO, u_0);
        assert_eq!(Z::from(15), u_1);
        assert_eq!(Z::from(35), u_2);
        assert_eq!(Z::from(u64::MAX), u_3);
        assert_eq!(Z::ZERO, i_0);
        assert_eq!(Z::from(15), i_1);
        assert_eq!(Z::from(35), i_2);
        assert_eq!(Z::from(i64::MIN).abs(), i_3);
        assert_eq!(Z::from(2), dist_mod);
    }
}
