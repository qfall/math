// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about properties of [`Zq`] instances.

use super::Zq;
use crate::traits::Pow;
use flint_sys::{fmpz::fmpz_is_zero, fmpz_mod::fmpz_mod_is_one};

impl Zq {
    /// Returns the inverse of `self` as a fresh [`Zq`] instance.
    /// It returns `None` if no inverse for `self mod q` exists.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// let value = Zq::try_from((4, 7)).unwrap();
    ///
    /// let inverse = value.inverse().unwrap();
    ///
    /// assert_eq!(Zq::try_from((2, 7)).unwrap(), inverse);
    /// ```
    pub fn inverse(&self) -> Option<Zq> {
        self.pow(-1).ok()
    }

    /// Checks if a [`Zq`] is `0`.
    ///
    /// Returns true if the value is `0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let value = Zq::try_from((0,7)).unwrap();
    /// assert!(value.is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        1 == unsafe { fmpz_is_zero(&self.value.value) }
    }

    /// Checks if a [`Zq`] is `1`.
    ///
    /// Returns true if the value is `1`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let value = Zq::try_from((1,7)).unwrap();
    /// assert!(value.is_one());
    /// ```
    pub fn is_one(&self) -> bool {
        1 == unsafe { fmpz_mod_is_one(&self.value.value, self.modulus.get_fmpz_mod_ctx_struct()) }
    }
}

#[cfg(test)]
mod test_inv {
    use super::Zq;

    /// Checks whether the inverse is correctly computed for small values.
    #[test]
    fn small_values() {
        let val_0 = Zq::try_from((4, 7)).unwrap();
        let val_1 = Zq::try_from((-2, 7)).unwrap();

        let inv_0 = val_0.inverse().unwrap();
        let inv_1 = val_1.inverse().unwrap();

        assert_eq!(Zq::try_from((2, 7)).unwrap(), inv_0);
        assert_eq!(Zq::try_from((3, 7)).unwrap(), inv_1);
    }

    /// Checks whether the inverse is correctly computed for large values.
    #[test]
    fn large_values() {
        let val_0 = Zq::try_from((i64::MAX, u64::MAX)).unwrap();
        let val_1 = Zq::try_from((i64::MIN, u64::MAX)).unwrap();

        let inv_0 = val_0.inverse().unwrap();
        let inv_1 = val_1.inverse().unwrap();

        assert_eq!(
            Zq::try_from((18446744073709551613_u64, u64::MAX)).unwrap(),
            inv_0
        );
        assert_eq!(
            Zq::try_from((18446744073709551613_u64, u64::MAX)).unwrap(),
            inv_1
        );
    }

    /// Checks whether `inv` returns `None` for any values without an inverse.
    #[test]
    fn no_inverse_returns_none() {
        let val_0 = Zq::try_from((4, 8)).unwrap();
        let val_1 = Zq::try_from((3, 9)).unwrap();
        let val_2 = Zq::try_from((0, 7)).unwrap();

        assert!(val_0.inverse().is_none());
        assert!(val_1.inverse().is_none());
        assert!(val_2.inverse().is_none());
    }
}

#[cfg(test)]
mod test_is_zero {
    use super::Zq;
    use std::str::FromStr;

    /// Ensure that is_zero returns `true` for `0`.
    #[test]
    fn zero_detection() {
        let zero = Zq::from_str("0 mod 7").unwrap();

        assert!(zero.is_zero());
    }

    /// Ensure that is_zero returns `false` for non-zero values.
    #[test]
    fn zero_rejection() {
        let small = Zq::from((4, 9));
        let large =
            Zq::from_str(&format!("{} mod {}", (u128::MAX - 1) / 2 + 1, u128::MAX)).unwrap();

        assert!(!small.is_zero());
        assert!(!large.is_zero());
    }
}

#[cfg(test)]
mod test_is_one {
    use super::Zq;
    use std::str::FromStr;

    /// Ensure that is_one returns `true` for `1`.
    #[test]
    fn one_detection() {
        let one = Zq::from_str("8 mod 7").unwrap();

        assert!(one.is_one());
    }

    /// Ensure that is_one returns `false` for other values.
    #[test]
    fn one_rejection() {
        let small = Zq::from_str("12 mod 7").unwrap();
        let large =
            Zq::from_str(&format!("{} mod {}", (u128::MAX - 1) / 2 + 2, u128::MAX)).unwrap();

        assert!(!small.is_one());
        assert!(!large.is_one());
    }
}
