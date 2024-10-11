// Copyright © 2024 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the [`Distance`] trait for [`Modulus`].

use super::Modulus;
use crate::{integer::Z, integer_mod_q::Zq, traits::Distance};

impl<Integer: Into<Z>> Distance<Integer> for Modulus {
    type Output = Z;

    /// Computes the absolute distance between a [`Modulus`] and a value that
    /// implements [`Into<Z>`].
    ///
    /// Parameters:
    /// - `other`: specifies the [`Z`] value whose distance is calculated to `self`
    ///
    /// Returns the absolute difference, i.e. distance between the [`Modulus`] instance
    /// and the value that implements [`Into<Z>`] as a new [`Z`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::Modulus;
    /// use qfall_math::traits::*;
    ///
    /// let a = Modulus::from(2);
    ///
    /// let distance_0 = a.distance(5);
    /// let distance_1 = a.distance(10);
    ///
    /// # assert_eq!(Z::from(3), distance_0);
    /// # assert_eq!(Z::from(8), distance_1);
    /// ```
    fn distance(&self, other: Integer) -> Self::Output {
        let z: Z = self.into();
        z.distance(other)
    }
}

impl Distance<&Zq> for Modulus {
    type Output = Z;

    /// Computes the absolute distance between `self` and `other`.
    /// For that, the representative of the ['Zq'] value is chosen from
    /// the range `[0, q)` (`0` inclusive, `q` exclusive).
    ///
    /// Parameters:
    /// - `other`: specifies the [`Zq`] value whose distance
    ///     is calculated to `self`.
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
    /// let a = Z::from(-1);
    /// let b = Zq::from((2, 13));
    /// let c = Zq::from((-1, 13));
    ///
    /// let distance_0 = a.distance(&b);
    /// let distance_1 = a.distance(&c);
    ///
    /// # assert_eq!(Z::from(3), distance_0);
    /// # assert_eq!(Z::from(13), distance_1);
    /// ```
    fn distance(&self, other: &Zq) -> Self::Output {
        self.distance(&other.value)
    }
}

impl Distance<Zq> for Modulus {
    type Output = Z;

    /// Computes the absolute distance between `self` and `other`.
    /// For that, the representative of the ['Zq'] value is chosen from
    /// the range `[0, q)` (`0` inclusive, `q` exclusive).
    ///
    /// Parameters:
    /// - `other`: specifies the [`Zq`] value whose distance
    ///     is calculated to `self`.
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
    /// let a = Z::from(-1);
    /// let b = Zq::from((2, 13));
    /// let c = Zq::from((-1, 13));
    ///
    /// let distance_0 = a.distance(b);
    /// let distance_1 = a.distance(c);
    ///
    /// # assert_eq!(Z::from(3), distance_0);
    /// # assert_eq!(Z::from(13), distance_1);
    /// ```
    fn distance(&self, other: Zq) -> Self::Output {
        self.distance(other.value)
    }
}

#[cfg(test)]
mod test_distance {
    use super::{Distance, Z};
    use crate::integer_mod_q::{Modulus, Zq};

    /// Since we convert `self` always into a [`Z`] instance, it suffices to test
    /// the availability here
    #[test]
    fn availability() {
        let modulus = Modulus::from(2);
        let z = Z::from(5);
        let zq = Zq::from((5, 10));

        let u_0 = modulus.distance(0_u8);
        let u_1 = modulus.distance(15_u16);
        let u_2 = modulus.distance(35_u32);
        let u_3 = modulus.distance(u64::MAX);
        let i_0 = modulus.distance(0_i8);
        let i_1 = modulus.distance(-15_i16);
        let i_2 = modulus.distance(35_i32);
        let i_3 = modulus.distance(i64::MIN + 2);
        let dist_z_0 = modulus.distance(&z);
        let dist_z_1 = modulus.distance(z);
        let dist_zq_0 = modulus.distance(&zq);
        let dist_zq_1 = modulus.distance(zq);

        assert_eq!(Z::from(2), u_0);
        assert_eq!(Z::from(13), u_1);
        assert_eq!(Z::from(33), u_2);
        assert_eq!(Z::from(u64::MAX - 2), u_3);
        assert_eq!(Z::from(2), i_0);
        assert_eq!(Z::from(17), i_1);
        assert_eq!(Z::from(33), i_2);
        assert_eq!(Z::from(i64::MIN).abs(), i_3);
        assert_eq!(Z::from(3), dist_z_0);
        assert_eq!(Z::from(3), dist_z_1);
        assert_eq!(Z::from(3), dist_zq_0);
        assert_eq!(Z::from(3), dist_zq_1);
    }
}
