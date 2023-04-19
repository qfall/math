// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the [`Distance`] trait for [`Q`].

use super::Q;
use crate::{
    macros::for_others::{implement_for_others, implement_for_owned},
    traits::Distance,
};

impl Distance<&Q> for Q {
    type Output = Q;

    /// Computes the absolute distance between two [`Q`] instances.
    ///
    /// Parameters:
    /// - `other`: specifies one of the [`Q`] values whose distance
    /// is calculated to `self`
    ///
    /// Returns the absolute difference, i.e. distance between the two given [`Q`]
    /// instances as a new [`Q`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::traits::*;
    ///
    /// let a = Q::from(1);
    ///
    /// let distance_0 = a.distance(5);
    /// let distance_1 = a.distance(10);
    ///
    /// # assert_eq!(Q::from(4), distance_0);
    /// # assert_eq!(Q::from(9), distance_1);
    /// ```
    fn distance(&self, other: &Q) -> Self::Output {
        let difference = other - self;
        difference.abs()
    }
}

implement_for_owned!(Q, Q, Distance);
implement_for_others!(Q, Q, Distance for u8 u16 u32 u64 i8 i16 i32 i64 f64 f32);

#[cfg(test)]
mod test_distance {
    use super::{Distance, Q};

    /// Checks if distance is correctly computed for small [`Q`] values
    /// and whether distance(a,b) == distance(b,a), distance(a,a) == 0
    #[test]
    fn small_values() {
        let a = Q::ONE;
        let b = Q::try_from((&5, &-15)).unwrap();
        let zero = Q::ZERO;

        assert_eq!(Q::ONE, a.distance(&zero));
        assert_eq!(Q::ONE, zero.distance(&a));
        assert_eq!(Q::try_from((&4, &3)).unwrap(), a.distance(&b));
        assert_eq!(Q::try_from((&4, &3)).unwrap(), b.distance(&a));
        assert_eq!(Q::try_from((&1, &3)).unwrap(), b.distance(&zero));
        assert_eq!(Q::try_from((&1, &3)).unwrap(), zero.distance(&b));
        assert_eq!(Q::ZERO, b.distance(&b))
    }

    /// Checks if distance is correctly computed for large [`Q`] values
    /// and whether distance(a,b) == distance(b,a), distance(a,a) == 0
    #[test]
    fn large_values() {
        let a = Q::from(i64::MAX);
        let b = Q::from(i64::MIN);
        let zero = Q::ZERO;

        assert_eq!(&a - &b, a.distance(&b));
        assert_eq!(&a - &b, b.distance(&a));
        assert_eq!(a, a.distance(&zero));
        assert_eq!(a, zero.distance(&a));
        assert_eq!(&a + Q::ONE, b.distance(&zero));
        assert_eq!(&a + Q::ONE, zero.distance(&b));
        assert_eq!(Q::ZERO, a.distance(&a));
    }

    /// Check whether distance is available for owned [`Q`] and other types
    #[test]
    fn availability() {
        let a = Q::ZERO;

        let u_0 = a.distance(0_u8);
        let u_1 = a.distance(15_u16);
        let u_2 = a.distance(35_u32);
        let u_3 = a.distance(u64::MAX);
        let i_0 = a.distance(0_i8);
        let i_1 = a.distance(-15_i16);
        let i_2 = a.distance(35_i32);
        let i_3 = a.distance(i64::MIN);
        let f_0 = a.distance(4.25_f32);
        let f_1 = a.distance(15.7_f64);

        assert_eq!(Q::ZERO, u_0);
        assert_eq!(Q::from(15), u_1);
        assert_eq!(Q::from(35), u_2);
        assert_eq!(Q::from(u64::MAX), u_3);
        assert_eq!(Q::ZERO, i_0);
        assert_eq!(Q::from(15), i_1);
        assert_eq!(Q::from(35), i_2);
        assert_eq!(Q::from(i64::MIN).abs(), i_3);
        assert_eq!(Q::try_from((&425, &100)).unwrap(), f_0);
        assert_eq!(Q::try_from((&157, &10)).unwrap(), f_1);
    }
}
