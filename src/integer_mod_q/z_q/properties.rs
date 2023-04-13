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

impl Zq {
    /// Returns the inverse of `self` as a fresh [`Zq`] instance.
    /// It returns `None` if no inverse for `self mod q` exists.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// let value = Zq::try_from((4, 7)).unwrap();
    ///
    /// let inverse = value.inv().unwrap();
    ///
    /// assert_eq!(Zq::try_from((2, 7)).unwrap(), inverse);
    /// ```
    pub fn inv(&self) -> Option<Zq> {
        self.pow(-1).ok()
    }
}

#[cfg(test)]
mod test_inv {
    use super::Zq;

    /// Checks whether the inverse is correctly computed for small values
    #[test]
    fn small_values() {
        let val_0 = Zq::try_from((4, 7)).unwrap();
        let val_1 = Zq::try_from((-2, 7)).unwrap();

        let inv_0 = val_0.inv().unwrap();
        let inv_1 = val_1.inv().unwrap();

        assert_eq!(Zq::try_from((2, 7)).unwrap(), inv_0);
        assert_eq!(Zq::try_from((3, 7)).unwrap(), inv_1);
    }

    /// Checks whether the inverse is correctly computed for large values
    #[test]
    fn large_values() {
        let val_0 = Zq::try_from((i64::MAX, u64::MAX)).unwrap();
        let val_1 = Zq::try_from((i64::MIN, u64::MAX)).unwrap();

        let inv_0 = val_0.inv().unwrap();
        let inv_1 = val_1.inv().unwrap();

        assert_eq!(
            Zq::try_from((18446744073709551613_u64, u64::MAX)).unwrap(),
            inv_0
        );
        assert_eq!(
            Zq::try_from((18446744073709551613_u64, u64::MAX)).unwrap(),
            inv_1
        );
    }

    /// Checks whether `inv` returns `None` for any values without an inverse
    #[test]
    fn no_inverse_returns_none() {
        let val_0 = Zq::try_from((4, 8)).unwrap();
        let val_1 = Zq::try_from((3, 9)).unwrap();
        let val_2 = Zq::try_from((0, 7)).unwrap();

        assert!(val_0.inv().is_none());
        assert!(val_1.inv().is_none());
        assert!(val_2.inv().is_none());
    }
}
