// Copyright © 2023 Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert an integer of type
//! [`Zq`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::Zq;
use core::fmt;

impl fmt::Display for Zq {
    /// Allows to convert an integer of type [`Zq`] into a [`String`].
    ///
    /// # Examples
    /// ```
    /// use math::integer_mod_q::Zq;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let integer = Zq::from_str("42 mod 3").unwrap();
    /// println!("{}", integer);
    /// ```
    ///
    /// ```
    /// use math::integer_mod_q::Zq;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let integer = Zq::from_str("42 mod 3").unwrap();
    /// let integer_string = integer.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} mod {}", self.value, self.modulus)
    }
}

#[cfg(test)]
mod test_to_string {

    use crate::integer_mod_q::Zq;
    use std::str::FromStr;

    /// tests whether a large integer works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = Zq::from_str(&format!("{} mod {}", u64::MAX, u128::MAX)).unwrap();

        assert_eq!(format!("{} mod {}", u64::MAX, u128::MAX), cmp.to_string())
    }

    /// tests whether a large integer works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = Zq::from_str(&format!("-{} mod {}", u64::MAX, u128::MAX)).unwrap();
        let diff = u128::MAX - u64::MAX as u128;

        assert_eq!(format!("{} mod {}", diff, u128::MAX), cmp.to_string())
    }

    /// tests whether a positive integer works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = Zq::from_str("42 mod 60").unwrap();

        assert_eq!("42 mod 60", cmp.to_string())
    }

    /// tests whether a negative integer works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = Zq::from_str("-40 mod 3").unwrap();

        assert_eq!("2 mod 3", cmp.to_string())
    }

    /// tests whether a integer that is created using a string, returns a
    /// string that can be used to create a [`Zq`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = Zq::from_str("42 mod 10").unwrap();

        let cmp_string = cmp.to_string();

        assert!(Zq::from_str(&cmp_string).is_ok())
    }
}
