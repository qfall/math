// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes functionality about round instances of [`Q`].

use super::Q;
use crate::{integer::Z, traits::Distance};
use flint_sys::fmpz::{fmpz_cdiv_q, fmpz_fdiv_q};

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
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    ///
    /// let value = Q::try_from((&4,&2)).unwrap();
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
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    ///
    /// let value = Q::try_from((&4,&2)).unwrap();
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
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    ///
    /// let value = Q::try_from((&9,&4)).unwrap();
    /// assert_eq!(Z::from(2), value.round());
    /// ```
    pub fn round(&self) -> Z {
        if Q::from(self.floor()).distance(self) < Q::from(0.5) {
            self.floor()
        } else {
            self.ceil()
        }
    }
}

#[cfg(test)]
mod test_floor {
    use crate::{integer::Z, rational::Q};

    // ensure that positive rationals are rounded correctly
    #[test]
    fn positive() {
        let val_1 = Q::try_from((&i64::MAX, &2)).unwrap();
        let val_2 = Q::try_from((&17, &u64::MAX)).unwrap();

        assert_eq!(Z::from((i64::MAX - 1) / 2), val_1.floor());
        assert_eq!(Z::ZERO, val_2.floor());
    }

    // ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let val_1 = Q::try_from((&-i64::MAX, &2)).unwrap();
        let val_2 = Q::try_from((&-17, &u64::MAX)).unwrap();

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
        let val_2 = Q::try_from((&17, &u64::MAX)).unwrap();

        assert_eq!(Z::from((i64::MAX - 1) / 2 + 1), val_1.ceil());
        assert_eq!(Z::ONE, val_2.ceil());
    }

    // ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let val_1 = Q::try_from((&-i64::MAX, &2)).unwrap();
        let val_2 = Q::try_from((&-17, &u64::MAX)).unwrap();

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
        let val_2 = Q::try_from((&17, &u64::MAX)).unwrap();

        assert_eq!(Z::from((i64::MAX - 1) / 2 + 1), val_1.round());
        assert_eq!(Z::ZERO, val_2.round());
    }

    // ensure that negative rationals are rounded correctly
    #[test]
    fn negative() {
        let val_1 = Q::try_from((&-i64::MAX, &2)).unwrap();
        let val_2 = Q::try_from((&-17, &u64::MAX)).unwrap();

        assert_eq!(Z::from((-i64::MAX - 1) / 2 + 1), val_1.round());
        assert_eq!(Z::ZERO, val_2.round());
    }
}
