// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality for rounding instances of [`Q`].

use super::Q;
use crate::{integer::Z, traits::Distance};
use flint_sys::{
    fmpq::fmpq_simplest_between,
    fmpz::{fmpz_cdiv_q, fmpz_fdiv_q},
};

impl Q {
    /// Rounds the given rational [`Q`] down to the next integer [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    ///
    /// let value = Q::try_from((&5,&2)).unwrap();
    /// assert_eq!(Z::from(2), value.floor());
    ///
    /// let value = Q::try_from((&-5,&2)).unwrap();
    /// assert_eq!(Z::from(-3), value.floor());
    ///
    /// let value = Q::try_from((&2,&1)).unwrap();
    /// assert_eq!(Z::from(2), value.floor());
    /// ```
    pub fn floor(&self) -> Z {
        let mut out = Z::default();
        unsafe { fmpz_fdiv_q(&mut out.value, &self.value.num, &self.value.den) };
        out
    }

    /// Rounds the given rational [`Q`] up to the next integer [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    ///
    /// let value = Q::try_from((&5,&2)).unwrap();
    /// assert_eq!(Z::from(3), value.ceil());
    ///
    /// let value = Q::try_from((&-5,&2)).unwrap();
    /// assert_eq!(Z::from(-2), value.ceil());
    ///
    /// let value = Q::try_from((&2,&1)).unwrap();
    /// assert_eq!(Z::from(2), value.ceil());
    /// ```
    pub fn ceil(&self) -> Z {
        let mut out = Z::default();
        unsafe { fmpz_cdiv_q(&mut out.value, &self.value.num, &self.value.den) };
        out
    }

    /// Rounds the given rational [`Q`] to the closest integer [`Z`].
    /// If the distance is equal, it rounds up.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    ///
    /// let value = Q::try_from((&5,&2)).unwrap();
    /// assert_eq!(Z::from(3), value.round());
    ///
    /// let value = Q::try_from((&-5,&2)).unwrap();
    /// assert_eq!(Z::from(-2), value.round());
    ///
    /// let value = Q::try_from((&2,&1)).unwrap();
    /// assert_eq!(Z::from(2), value.round());
    /// ```
    pub fn round(&self) -> Z {
        if Q::from(self.floor()).distance(self) < Q::from(0.5) {
            self.floor()
        } else {
            self.ceil()
        }
    }

    /// Returns the smallest rational with the smallest denominator in the range
    /// `\[self - |precision|, self + |precision|\]`.
    ///
    /// Parameters:
    /// -`precision`: the precision the new value can differ from `self`.
    /// Note that the absolute value is relevant, not the sign.
    ///
    /// Returns the simplest [`Q`] within the defined range.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let value = Q::try_from((&17, &20)).unwrap();
    /// let precision = Q::try_from((&1, &20)).unwrap();
    ///
    /// let simplified = Q::try_from((&4, &5)).unwrap();
    /// assert_eq!(simplified, value.simplify(&precision));
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let value = Q::try_from((&3, &2)).unwrap();
    /// let precision = Q::try_from((&1, &2)).unwrap();
    ///
    /// assert_eq!(Q::ONE, value.simplify(&precision));
    /// ```
    pub fn simplify(&self, precision: &Q) -> Self {
        let lower = self - precision;
        let upper = self + precision;
        let mut out = Q::default();
        unsafe { fmpq_simplest_between(&mut out.value, &lower.value, &upper.value) };
        out
    }
}

#[cfg(test)]
mod test_floor {
    use crate::{integer::Z, rational::Q};

    // ensure that positive rationals are rounded correctly
    #[test]
    fn positive() {
        let val_1 = Q::try_from((&i64::MAX, &2)).unwrap();
        let val_2 = Q::try_from((&1, &u64::MAX)).unwrap();

        assert_eq!(Z::from((i64::MAX - 1) / 2), val_1.floor());
        assert_eq!(Z::ZERO, val_2.floor());
    }

    // ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let val_1 = Q::try_from((&-i64::MAX, &2)).unwrap();
        let val_2 = Q::try_from((&-1, &u64::MAX)).unwrap();

        assert_eq!(Z::from((-i64::MAX - 1) / 2), val_1.floor());
        assert_eq!(Z::MINUS_ONE, val_2.floor());
    }
}

#[cfg(test)]
mod test_ceil {
    use crate::{integer::Z, rational::Q};

    // ensure that positive rationals are rounded correctly
    #[test]
    fn positive() {
        let val_1 = Q::try_from((&i64::MAX, &2)).unwrap();
        let val_2 = Q::try_from((&1, &u64::MAX)).unwrap();

        assert_eq!(Z::from((i64::MAX - 1) / 2 + 1), val_1.ceil());
        assert_eq!(Z::ONE, val_2.ceil());
    }

    // ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let val_1 = Q::try_from((&-i64::MAX, &2)).unwrap();
        let val_2 = Q::try_from((&-1, &u64::MAX)).unwrap();

        assert_eq!(Z::from((-i64::MAX - 1) / 2 + 1), val_1.ceil());
        assert_eq!(Z::ZERO, val_2.ceil());
    }
}

#[cfg(test)]
mod test_round {
    use crate::{integer::Z, rational::Q};

    // ensure that positive rationals are rounded correctly
    #[test]
    fn positive() {
        let val_1 = Q::try_from((&i64::MAX, &2)).unwrap();
        let val_2 = Q::try_from((&1, &u64::MAX)).unwrap();

        assert_eq!(Z::from((i64::MAX - 1) / 2 + 1), val_1.round());
        assert_eq!(Z::ZERO, val_2.round());
    }

    // ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let val_1 = Q::try_from((&-i64::MAX, &2)).unwrap();
        let val_2 = Q::try_from((&-1, &u64::MAX)).unwrap();

        assert_eq!(Z::from((-i64::MAX - 1) / 2 + 1), val_1.round());
        assert_eq!(Z::ZERO, val_2.round());
    }
}

#[cfg(test)]
mod test_simplify {
    use crate::rational::Q;

    /// ensure that negative precision works as expected
    #[test]
    fn precision_absolute_value() {
        let value_1 = Q::try_from((&17, &20)).unwrap();
        let value_2 = Q::try_from((&-17, &20)).unwrap();
        let precision = Q::try_from((&-1, &20)).unwrap();

        let simplified_1 = Q::try_from((&4, &5)).unwrap();
        let simplified_2 = Q::try_from((&-4, &5)).unwrap();
        assert_eq!(simplified_1, value_1.simplify(&precision));
        assert_eq!(simplified_2, value_2.simplify(&precision));
    }

    /// ensure that large values with pointer representations are reduced
    #[test]
    fn large_pointer_representation() {
        let value = Q::try_from((&(i64::MAX - 1), &i64::MAX)).unwrap();
        let precision = Q::try_from((&1, &u64::MAX)).unwrap();

        let simplified = Q::try_from(1).unwrap();
        assert_eq!(simplified, value.simplify(&precision));
    }

    /// ensure that the simplified value stays in range
    #[test]
    fn stay_in_precision() {
        let value = Q::try_from((&(i64::MAX - 1), &i64::MAX)).unwrap();
        let precision = Q::try_from((&1, &(u64::MAX - 1))).unwrap();

        let simplified = value.simplify(&precision);
        assert!(&value - &precision <= simplified && simplified <= &value + &precision);
        assert!(
            Q::try_from((&(i64::MAX - 2), &i64::MAX)).unwrap() <= simplified
                && simplified <= 1.into()
        );
    }

    /// ensure that a value which can not be simplified is not changed
    #[test]
    fn no_change() {
        let precision = Q::try_from((&1, &(u64::MAX - 1))).unwrap();

        assert_eq!(Q::ONE, Q::ONE.simplify(&precision));
        assert_eq!(Q::MINUS_ONE, Q::MINUS_ONE.simplify(&precision));
        assert_eq!(Q::ZERO, Q::ZERO.simplify(&precision));
    }
}
