// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Get elements of [`Q`] like the numerator and denominator.

use super::Q;
use crate::integer::Z;
use flint_sys::fmpz::fmpz_set;

impl Q {
    /// Returns the denominator
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    ///
    /// let value = Q::from((2, 20));
    ///
    /// let den = value.get_denominator();
    ///
    /// assert_eq!(den, Z::from(10));
    /// ```
    pub fn get_denominator(&self) -> Z {
        let mut result = Z::default();
        unsafe { fmpz_set(&mut result.value, &self.value.den) };
        result
    }

    /// Returns the numerator
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    ///
    /// let value = Q::from((2, 20));
    ///
    /// let num = value.get_numerator();
    ///
    /// assert_eq!(num, Z::from(1));
    /// ```
    pub fn get_numerator(&self) -> Z {
        let mut result = Z::default();
        unsafe { fmpz_set(&mut result.value, &self.value.num) };
        result
    }
}

#[cfg(test)]
mod test_get_denominator {
    use crate::{integer::Z, rational::Q};

    /// get a small denominator
    #[test]
    fn get_small() {
        let value = Q::from((2, 20));
        let den = value.get_denominator();
        assert_eq!(den, Z::from(10));
    }

    /// get a large denominator (uses FLINT's pointer representation)
    #[test]
    fn get_large() {
        let value = Q::from((1, i64::MAX));
        let den = value.get_denominator();
        assert_eq!(den, Z::from(i64::MAX));
    }
}

#[cfg(test)]
mod test_get_numerator {
    use crate::{integer::Z, rational::Q};

    /// get a small numerator
    #[test]
    fn get_small() {
        let value = Q::from((2, 20));
        let num = value.get_numerator();
        assert_eq!(num, Z::from(1));
    }

    /// get a large numerator (uses FLINT's pointer representation)
    #[test]
    fn get_large() {
        let value = Q::from(i64::MAX);
        let num = value.get_numerator();
        assert_eq!(num, Z::from(i64::MAX));
    }
}
