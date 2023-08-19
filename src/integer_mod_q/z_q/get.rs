// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Get elements of [`Zq`] like its [`Z`] value and [`Modulus`].

use crate::{
    integer::Z,
    integer_mod_q::{Modulus, Zq},
};

impl Zq {
    /// Returns the [`Z`] value of the [`Zq`] element.
    ///
    /// The representation in the range `[0, modulus[` (`0` inclusive, `modulus` exclusive)
    /// is returned.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer::Z;
    /// let zq_value = Zq::from((4, 7));
    ///
    /// let z_value = zq_value.get_value();
    ///
    /// assert_eq!(Z::from(4), z_value);
    /// ```
    pub fn get_value(&self) -> Z {
        self.value.clone()
    }

    /// Returns the [`Modulus`] of the [`Zq`] element.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{Zq, Modulus};
    /// use std::str::FromStr;
    /// let value = Zq::from((4, 7));
    /// let cmp = Modulus::from(7);
    ///
    /// let modulus = value.get_mod();
    ///
    /// assert_eq!(cmp, modulus);
    /// ```
    pub fn get_mod(&self) -> Modulus {
        self.modulus.clone()
    }
}

#[cfg(test)]
mod test_get_value {
    use super::{Zq, Z};

    /// Check whether `get_value` outputs the correct value for small values
    #[test]
    fn get_small() {
        let value_0 = Zq::from((2, 20));
        let value_1 = Zq::from((-2, 20));

        let res_0 = value_0.get_value();
        let res_1 = value_1.get_value();

        assert_eq!(res_0, Z::from(2));
        assert_eq!(res_1, Z::from(18));
    }

    /// Check whether `get_value` outputs the correct value for large values
    #[test]
    fn get_large() {
        let value_0 = Zq::from((i64::MAX, u64::MAX));
        let value_1 = Zq::from((i64::MIN, u64::MAX));

        let res_0 = value_0.get_value();
        let res_1 = value_1.get_value();

        assert_eq!(res_0, Z::from(i64::MAX));
        assert_eq!(res_1, Z::from(i64::MAX));
    }
}

#[cfg(test)]
mod test_get_mod {
    use super::{Modulus, Zq};

    /// Check whether `get_mod` outputs the correct modulus for small moduli
    #[test]
    fn get_small() {
        let value = Zq::from((2, 20));

        let modulus = value.get_mod();

        assert_eq!(modulus, Modulus::from(20));
    }

    /// Check whether `get_mod` outputs the correct modulus for large moduli
    #[test]
    fn get_large() {
        let value = Zq::from((2, u64::MAX));

        let modulus = value.get_mod();

        assert_eq!(modulus, Modulus::from(u64::MAX));
    }
}
